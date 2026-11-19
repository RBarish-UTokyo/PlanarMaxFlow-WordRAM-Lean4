module

public import PlanarFlow.NegSSSP.CompProg

/-!
# The grouping of the components of a piece, on the machine

Without a component of more than three quarters of the darts, the split of the machine
(`PlanarFlow.NegSSSP.splitM`) is the grouping `grp` of the components in the order `ord P` of the
darts on the machine (`splitM_small`). Here it is computed in one scan of the darts `x < m` from
their component labels and the sizes of the components, as `compProg` leaves them
(`compProg_spec`).

* `grpL`: the grouping on labels: a set of labels (`ℕ → Bool`) grown by the label of each dart
  scanned, as `grp` grows a set of darts by components (`lset_grpL`: the darts with a label of
  `grpL S xs` are `grp N P (lset S) (xs.map δ)`).
* `grpProg`: clears the flags of the labels, scans the darts keeping the number of darts of the
  group, stops at the first component making the group larger than a quarter (with it, or that
  component alone), then writes a side per dart (`grpProg_exec`, `5 k + 34 m + 20` steps).
* `grpProg_splitM`: **the sides written are those of `splitM N ord cut P`** for the order
  `ord P = [δ 0, …, δ (m - 1)]` of the darts on the machine, when every component has at most
  three quarters of the darts (the case `r856 = 0` of `compProg_spec`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

variable {P : Input} {W : ℕ}

/-! ### The grouping on labels -/

/-- The number of darts `y < m` with a label in `S`. -/
def lcard (m : ℕ) (lb : ℕ → ℕ) (S : ℕ → Bool) : ℕ :=
  ((range m).filter fun y => S (lb y) = true).card

/-- `S` with the label `ℓ`. -/
def addL (S : ℕ → Bool) (ℓ : ℕ) : ℕ → Bool := fun j => S j || j == ℓ

/-- **The grouping on labels**: as `grp`, the set of labels `S` grown by the label of the next
dart while its darts are at most a quarter of the `m` darts; the first label making them more ends
the scan, with the set if they are then at most three quarters, alone otherwise. -/
def grpL (m : ℕ) (lb : ℕ → ℕ) : (ℕ → Bool) → List ℕ → (ℕ → Bool)
  | S, [] => S
  | S, x :: xs =>
    if 4 * lcard m lb (addL S (lb x)) ≤ m then grpL m lb (addL S (lb x)) xs
    else if 4 * lcard m lb (addL S (lb x)) ≤ 3 * m then addL S (lb x)
    else fun j => j == lb x

lemma lcard_le (m : ℕ) (lb : ℕ → ℕ) (S : ℕ → Bool) : lcard m lb S ≤ m :=
  (card_filter_le _ _).trans (card_range m).le

lemma lcard_addL (m : ℕ) (lb : ℕ → ℕ) (S : ℕ → Bool) (ℓ : ℕ) :
    lcard m lb (addL S ℓ) = lcard m lb S + if S ℓ = true then 0 else cntL lb m ℓ := by
  unfold lcard addL cntL
  have e : (range m).filter (fun y => (S (lb y) || lb y == ℓ) = true) =
      (range m).filter (fun y => S (lb y) = true) ∪ (range m).filter (fun y => lb y = ℓ) := by
    rw [← filter_or]; congr 1; ext y; simp
  rw [e]
  split_ifs with h
  · rw [union_eq_left.2 fun y hy => ?_, Nat.add_zero]
    obtain ⟨h1, h2⟩ := mem_filter.1 hy
    exact mem_filter.2 ⟨h1, by rw [h2]; exact h⟩
  · rw [card_union_of_disjoint (disjoint_left.2 fun y h1 h2 => ?_)]
    obtain ⟨-, h1⟩ := mem_filter.1 h1
    obtain ⟨-, h2⟩ := mem_filter.1 h2
    rw [h2] at h1; exact h h1

/-! ### The program -/

/-- Setup (`r880 = m`, `r881 = bL`, `r882 = bC`, `r883 = bG`, `r884 = bO`, `r885 = k + 1`,
`r10 = 1`): `r886 = 0`, the size of the group `r887 = 0`, the stop flag `r888 = 0`, the label of
a lone component `r889 = 0`, `r891 = 3 m`, `r892 = 0`. -/
def gSetup : Stmt := block [.constN 886 0, .constN 887 0, .constN 888 0, .constN 889 0,
  .addN 891 880 880, .addN 891 891 880, .constN 892 0]

/-- Clearing the flag of the label `r892`. -/
def gZero : Stmt := block [.addN 893 883 892, .storeN 893 886, .addN 892 892 10]

/-- The dart `x = r892` of the scan, label `ℓ = r894`: the size `new = r897` of the group with
the component of `x`; with it the group grows (`new ≤ m / 4`), or ends the scan, with the group
(`new ≤ 3 m / 4`) or alone. -/
def gProc : Stmt :=
  .seq (block [.addN 893 881 892, .loadN 894 893, .addN 895 883 894, .loadN 896 895,
    .addN 893 882 894, .loadN 897 893]) <|
  .seq (.ifLtN 896 10 (.instr (.addN 897 887 897)) (.instr (.copyN 897 887))) <|
  .seq (block [.addN 898 897 897, .addN 898 898 898]) <|
  .ifLtN 880 898
    (.ifLtN 891 898 (block [.copyN 889 894, .constN 888 1]) (block [.storeN 895 10, .constN 888 1]))
    (block [.storeN 895 10, .copyN 887 897])

/-- One dart of the scan (nothing once stopped). -/
def gScan : Stmt := .seq (.ifLtN 888 10 gProc .skip) (.instr (.addN 892 892 10))

/-- The side `r899` of the dart `x = r892` at `bO + x`: `0` in the group. -/
def gOut : Stmt :=
  .seq (block [.addN 893 881 892, .loadN 894 893]) <|
  .seq (.ifLtN 889 10
      (.seq (block [.addN 895 883 894, .loadN 896 895])
        (.ifLtN 896 10 (.instr (.constN 899 1)) (.instr (.constN 899 0))))
      (.ifLtN 894 889 (.instr (.constN 899 1))
        (.ifLtN 889 894 (.instr (.constN 899 1)) (.instr (.constN 899 0)))))
    (block [.addN 893 884 892, .storeN 893 899, .addN 892 892 10])

/-- **The grouping of the components.** -/
def grpProg : Stmt :=
  .seq gSetup <| .seq (.whileLtN 892 885 gZero) <| .seq (.instr (.constN 892 0)) <|
  .seq (.whileLtN 892 880 gScan) <| .seq (.instr (.constN 892 0)) (.whileLtN 892 880 gOut)

theorem natS_grpProg : natS grpProg = true := by decide

/-- The registers of `grpProg`. -/
structure GrpIn (m k bL bC bG bO : ℕ) (c : Config) : Prop where
  r10 : c.nreg 10 = 1
  r880 : c.nreg 880 = m
  r881 : c.nreg 881 = bL
  r882 : c.nreg 882 = bC
  r883 : c.nreg 883 = bG
  r884 : c.nreg 884 = bO
  r885 : c.nreg 885 = k + 1

/-- The layout of `grpProg`: the flags `[bG, bG + k + 1)` and the sides `[bO, bO + m)` apart from
each other and from the labels `[bL, bL + m)` and the sizes `[bC, bC + k + 1)`. -/
structure GrpLay (m k bL bC bG bO W : ℕ) : Prop where
  wL : bL + m ≤ W
  wC : bC + k + 1 ≤ W
  wG : bG + k + 1 ≤ W
  wO : bO + m ≤ W
  wm : 4 * m + 3 ≤ W
  dGL : bG + k + 1 ≤ bL ∨ bL + m ≤ bG
  dGC : bG + k + 1 ≤ bC ∨ bC + k + 1 ≤ bG
  dGO : bG + k + 1 ≤ bO ∨ bO + m ≤ bG
  dOL : bO + m ≤ bL ∨ bL + m ≤ bO
  dOC : bO + m ≤ bC ∨ bC + k + 1 ≤ bO

/-! ### The steps -/

theorem gIf_exec {g acc cnt : ℕ} (c : Config) (hw : WordsBounded W c) (h896 : c.nreg 896 = g)
    (h10 : c.nreg 10 = 1) (h887 : c.nreg 887 = acc) (h897 : c.nreg 897 = cnt)
    (hW : acc + cnt ≤ W) :
    ∃ c' t, Exec P W (.ifLtN 896 10 (.instr (.addN 897 887 897)) (.instr (.copyN 897 887))) c c' t ∧
      t ≤ 3 ∧ c' = { c with nreg := upd c.nreg 897 (acc + if g = 0 then cnt else 0) } := by
  by_cases hg : g = 0
  · refine spec_ifLtN_true (by rw [h896, h10]; omega) ?_
    refine spec_instr (Exec.addN ‹_› 897 887 897 (by rw [h887, h897]; omega)) fun _ => ?_
    refine ⟨by omega, ?_⟩
    rw [h887, h897, hg]; rfl
  · refine spec_ifLtN_false (by rw [h896, h10]; omega) ?_
    refine spec_instr (Exec.copyN ‹_› 897 887) fun _ => ?_
    refine ⟨by omega, ?_⟩
    rw [h887]; simp [hg]

theorem gTail_exec {m ℓ a new : ℕ} (c : Config) (hw : WordsBounded W c) (h897 : c.nreg 897 = new)
    (h880 : c.nreg 880 = m) (h891 : c.nreg 891 = m + m + m) (h895 : c.nreg 895 = a)
    (h894 : c.nreg 894 = ℓ) (h10 : c.nreg 10 = 1) (hn : new ≤ m) (wm : 4 * m + 3 ≤ W) :
    ∃ c' t, Exec P W (.seq (block [.addN 898 897 897, .addN 898 898 898]) <|
      .ifLtN 880 898
        (.ifLtN 891 898 (block [.copyN 889 894, .constN 888 1])
          (block [.storeN 895 10, .constN 888 1]))
        (block [.storeN 895 10, .copyN 887 897])) c c' t ∧ t ≤ 7 ∧
      (∀ r, r < 887 ∨ (889 < r ∧ r < 898) ∨ 898 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      (4 * new ≤ m → c'.nmem = upd c.nmem a 1 ∧ c'.nreg 887 = new ∧ c'.nreg 888 = c.nreg 888 ∧
        c'.nreg 889 = c.nreg 889) ∧
      (m < 4 * new → 4 * new ≤ 3 * m → c'.nmem = upd c.nmem a 1 ∧ c'.nreg 887 = c.nreg 887 ∧
        c'.nreg 888 = 1 ∧ c'.nreg 889 = c.nreg 889) ∧
      (3 * m < 4 * new → c'.nmem = c.nmem ∧ c'.nreg 887 = c.nreg 887 ∧ c'.nreg 888 = 1 ∧
        c'.nreg 889 = ℓ) := by
  refine spec_seq ?_
  exec_block
  all_goals try ((try config_simp); (try simp only [h897]) <;> omega)
  by_cases h1 : m < 4 * new
  · refine spec_ifLtN_true (by config_simp; rw [h880, h897]; omega) ?_
    by_cases h2 : 3 * m < 4 * new
    · refine spec_ifLtN_true (by config_simp; rw [h891, h897]; omega) ?_
      exec_block
      all_goals try omega
      refine ⟨by omega, fun r hr => ?_, rfl, rfl, rfl, fun h => absurd h (by omega),
        fun _ h => absurd h (by omega), fun _ => ⟨rfl, by config_simp, by config_simp, ?_⟩⟩
      · config_simp; simp only [upd_apply]; split_ifs <;> omega
      · config_simp; exact h894
    · refine spec_ifLtN_false (by config_simp; rw [h891, h897]; omega) ?_
      exec_block
      all_goals try omega
      refine ⟨by omega, fun r hr => ?_, rfl, rfl, rfl, fun h => absurd h (by omega),
        fun _ _ => ⟨?_, by config_simp, by config_simp, by config_simp⟩,
        fun h => absurd h (by omega)⟩
      · config_simp; simp only [upd_apply]; split_ifs <;> omega
      · config_simp; rw [h895, h10]
  · refine spec_ifLtN_false (by config_simp; rw [h880, h897]; omega) ?_
    exec_block
    refine ⟨by omega, fun r hr => ?_, rfl, rfl, rfl,
      fun _ => ⟨?_, by config_simp; exact h897, by config_simp, by config_simp⟩,
      fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
    · config_simp; rw [h895, h10]

theorem gProc_exec {m bL bC bG i ℓ cnt g acc : ℕ} (c₁ : Config) (hw : WordsBounded W c₁)
    (e881 : c₁.nreg 881 = bL) (e882 : c₁.nreg 882 = bC) (e883 : c₁.nreg 883 = bG)
    (e880 : c₁.nreg 880 = m) (e891 : c₁.nreg 891 = m + m + m) (e10 : c₁.nreg 10 = 1)
    (ha : c₁.nreg 892 = i) (e887 : c₁.nreg 887 = acc) (hL : c₁.nmem (bL + i) = ℓ)
    (hG : c₁.nmem (bG + ℓ) = g) (hC : c₁.nmem (bC + ℓ) = cnt)
    (hnew : acc + (if g = 0 then cnt else 0) ≤ m) (hcnt : cnt ≤ m) (wL : bL + i ≤ W)
    (wG : bG + ℓ ≤ W) (wC : bC + ℓ ≤ W) (wm : 4 * m + 3 ≤ W) :
    ∃ c' t, Exec P W gProc c₁ c' t ∧ t ≤ 16 ∧
      (∀ r, r < 887 ∨ (889 < r ∧ r < 893) ∨ 898 < r → c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output ∧
      (4 * (acc + if g = 0 then cnt else 0) ≤ m → c'.nmem = upd c₁.nmem (bG + ℓ) 1 ∧
        c'.nreg 887 = acc + (if g = 0 then cnt else 0) ∧ c'.nreg 888 = c₁.nreg 888 ∧
        c'.nreg 889 = c₁.nreg 889) ∧
      (m < 4 * (acc + if g = 0 then cnt else 0) → 4 * (acc + if g = 0 then cnt else 0) ≤ 3 * m →
        c'.nmem = upd c₁.nmem (bG + ℓ) 1 ∧ c'.nreg 887 = c₁.nreg 887 ∧ c'.nreg 888 = 1 ∧
        c'.nreg 889 = c₁.nreg 889) ∧
      (3 * m < 4 * (acc + if g = 0 then cnt else 0) → c'.nmem = c₁.nmem ∧
        c'.nreg 887 = c₁.nreg 887 ∧ c'.nreg 888 = 1 ∧ c'.nreg 889 = ℓ) := by
  unfold gProc
  refine spec_seq ?_
  exec_block
  all_goals try ((try config_simp); (try simp only [e881, e882, e883, ha, hL]) <;> omega)
  refine spec_seq ?_
  refine spec_use (gIf_exec (P := P) (g := g) (acc := acc) (cnt := cnt) _ ‹_›
    (by config_simp; simp only [e881, e883, ha, hL, hG]) (by config_simp; exact e10)
    (by config_simp; exact e887) (by config_simp; simp only [e881, e882, ha, hL, hC])
    (by omega)) ?_
  intro c₂ t₂ ht₂ hw₂ hc₂
  subst hc₂
  refine spec_use (gTail_exec (P := P) (m := m) (ℓ := ℓ) (a := bG + ℓ)
    (new := acc + if g = 0 then cnt else 0) _ hw₂ (by config_simp)
    (by config_simp; exact e880) (by config_simp; exact e891)
    (by config_simp; simp only [e881, e883, ha, hL]) (by config_simp; simp only [e881, ha, hL])
    (by config_simp; exact e10) hnew wm) ?_
  intro c₃ t₃ ht₃ hw₃ ⟨hr, hrr, hrm, ho, h1, h2, h3⟩
  config_simp at hr; config_simp at hrr; config_simp at hrm; config_simp at ho
  config_simp at h1; config_simp at h2; config_simp at h3
  refine ⟨by omega, fun r hr' => ?_, hrr, hrm, ho, fun h => ?_, fun h h' => ?_, fun h => ?_⟩
  · rw [hr r (by omega)]; try (simp only [upd_apply]; split_ifs <;> omega)
  · obtain ⟨a1, a2, a3, a4⟩ := h1 h
    exact ⟨a1, a2, by rw [a3]; try (simp only [upd_apply]; split_ifs <;> omega),
      by rw [a4]; try (simp only [upd_apply]; split_ifs <;> omega)⟩
  · obtain ⟨a1, a2, a3, a4⟩ := h2 h h'
    exact ⟨a1, by rw [a2]; try (simp only [upd_apply]; split_ifs <;> omega), a3,
      by rw [a4]; try (simp only [upd_apply]; split_ifs <;> omega)⟩
  · obtain ⟨a1, a2, a3, a4⟩ := h3 h
    exact ⟨a1, by rw [a2]; try (simp only [upd_apply]; split_ifs <;> omega), a3, a4⟩

/-! ### The loops -/

/-- The labels flagged in memory (at `bG + ℓ`, `ℓ ≤ k`). -/
def gp (k bG : ℕ) (mem : ℕ → ℕ) : ℕ → Bool := fun ℓ => decide (ℓ ≤ k ∧ mem (bG + ℓ) ≠ 0)

/-- The labels of the group found: the lone label `solo` if nonzero, the flagged ones otherwise. -/
def rp (k bG : ℕ) (mem : ℕ → ℕ) (solo : ℕ) : ℕ → Bool :=
  if solo = 0 then gp k bG mem else fun j => j == solo

lemma gp_upd {k bG ℓ : ℕ} {mem : ℕ → ℕ} (hℓ : ℓ ≤ k) :
    gp k bG (upd mem (bG + ℓ) 1) = addL (gp k bG mem) ℓ := by
  funext j
  unfold gp addL
  by_cases hj : j = ℓ
  · subst hj; simp [upd_apply, hℓ]
  · have hb : (j == ℓ) = false := by simp [hj]
    simp only [upd_apply, add_right_inj, hj, ↓reduceIte, hb, Bool.or_false]

lemma gp_congr {k bG : ℕ} {mem mem' : ℕ → ℕ} (h : ∀ ℓ ≤ k, mem' (bG + ℓ) = mem (bG + ℓ)) :
    gp k bG mem' = gp k bG mem := by
  funext j; unfold gp
  by_cases hj : j ≤ k
  · rw [h j hj]
  · simp [hj]

lemma drop_range_cons {m i : ℕ} (hi : i < m) :
    (List.range m).drop i = i :: (List.range m).drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using hi), List.getElem_range]

/-- **Clearing the flags** `[bG, bG + k + 1)`. -/
theorem gZeroLoop_exec {k bG : ℕ} (c₁ : Config) (hw : WordsBounded W c₁)
    (e883 : c₁.nreg 883 = bG) (e885 : c₁.nreg 885 = k + 1) (e886 : c₁.nreg 886 = 0)
    (e10 : c₁.nreg 10 = 1) (e892 : c₁.nreg 892 = 0) (wG : bG + k + 1 ≤ W) :
    ∃ c' t, Exec P W (.whileLtN 892 885 gZero) c₁ c' t ∧ t ≤ 5 * k + 7 ∧
      (∀ ℓ < k + 1, c'.nmem (bG + ℓ) = 0) ∧
      (∀ r, r < 892 ∨ 899 < r → c'.nreg r = c₁.nreg r) ∧
      c'.output = c₁.output ∧ (∀ a, (a < bG ∨ bG + k + 1 ≤ a) → c'.nmem a = c₁.nmem a) := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ r, r < 892 ∨ 899 < r → c'.nreg r = c₁.nreg r) ∧ c'.output = c₁.output ∧
      (∀ a, (a < bG ∨ bG + i ≤ a) → c'.nmem a = c₁.nmem a) ∧ (∀ ℓ < i, c'.nmem (bG + ℓ) = 0)
  refine spec_use (forLoop_exec (P := P) (a := 892) (bR := 885) (body := gZero) J (K := 3)
    (n := k + 1) _ hw e892 e885 ?_ (fun i c₂ hi hw₂ ha hb ⟨fr, fo, fm, f0⟩ => ?_)) ?_
  · exact ⟨fun _ _ => rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (by omega)⟩
  · have g883 := (fr _ (by omega)).trans e883
    have g886 := (fr _ (by omega)).trans e886
    have g10 := (fr _ (by omega)).trans e10
    unfold gZero
    exec_block
    all_goals try ((try config_simp); (try simp only [g883, g10, ha]) <;> omega)
    refine ⟨by omega, by config_simp; simp only [g10, ha], by config_simp; exact hb,
      fun r hr => ?_, fo, fun a ha' => ?_, fun ℓ hℓ => ?_⟩
    · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact fr r hr
    · config_simp; simp only [upd_apply, g883, ha]
      split_ifs <;> first | omega | exact fm a (by omega)
    · config_simp; simp only [upd_apply, g883, ha, g886]
      split_ifs <;> first | omega | exact f0 ℓ (by omega)
  · intro c' t ht _ ⟨_, fr, fo, fm, f0⟩
    exact ⟨by omega, f0, fr, fo, fm⟩

set_option maxHeartbeats 1000000 in
/-- **The scan**: the group of labels found is `grpL` from the empty set over the darts
`0, …, m - 1`. -/
theorem gScanLoop_exec {m k bL bC bG bO : ℕ} {lb : ℕ → ℕ} (c₁ : Config) (hw : WordsBounded W c₁)
    (e881 : c₁.nreg 881 = bL) (e882 : c₁.nreg 882 = bC) (e883 : c₁.nreg 883 = bG)
    (e880 : c₁.nreg 880 = m) (e891 : c₁.nreg 891 = m + m + m) (e10 : c₁.nreg 10 = 1)
    (e892 : c₁.nreg 892 = 0) (e887 : c₁.nreg 887 = 0) (e888 : c₁.nreg 888 = 0)
    (e889 : c₁.nreg 889 = 0) (hL : ∀ x < m, c₁.nmem (bL + x) = lb x)
    (hlb : ∀ x < m, 1 ≤ lb x ∧ lb x ≤ k) (hC : ∀ x < m, c₁.nmem (bC + lb x) = cntL lb m (lb x))
    (hG : ∀ ℓ < k + 1, c₁.nmem (bG + ℓ) = 0) (hlay : GrpLay m k bL bC bG bO W) :
    ∃ c' t, Exec P W (.whileLtN 892 880 gScan) c₁ c' t ∧ t ≤ 20 * m + 2 ∧
      grpL m lb (fun _ => false) (List.range m) = rp k bG c'.nmem (c'.nreg 889) ∧
      (∀ r, r < 887 ∨ (889 < r ∧ r < 892) ∨ 898 < r → c'.nreg r = c₁.nreg r) ∧
      c'.output = c₁.output ∧ (∀ a, (a < bG ∨ bG + k + 1 ≤ a) → c'.nmem a = c₁.nmem a) := by
  obtain ⟨wL, wC, wG, wO, wm, dGL, dGC, dGO, dOL, dOC⟩ := hlay
  have hS0 : gp k bG c₁.nmem = fun _ => false := by
    funext j; unfold gp
    by_cases hj : j ≤ k
    · rw [hG j (by omega)]; simp
    · simp [hj]
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ r, r < 887 ∨ (889 < r ∧ r < 892) ∨ 898 < r → c'.nreg r = c₁.nreg r) ∧
      c'.output = c₁.output ∧ (∀ a, (a < bG ∨ bG + k + 1 ≤ a) → c'.nmem a = c₁.nmem a) ∧
      ((c'.nreg 888 = 0 ∧ grpL m lb (fun _ => false) (List.range m) =
          grpL m lb (gp k bG c'.nmem) ((List.range m).drop i) ∧
          c'.nreg 887 = lcard m lb (gp k bG c'.nmem) ∧ c'.nreg 889 = 0) ∨
        (c'.nreg 888 = 1 ∧ grpL m lb (fun _ => false) (List.range m) =
          rp k bG c'.nmem (c'.nreg 889)))
  refine spec_use (forLoop_exec (P := P) (a := 892) (bR := 880) (body := gScan) J (K := 18)
    (n := m) _ hw e892 e880 ?_ (fun i c₂ hi hw₂ ha hb ⟨fr, fo, fm, fs⟩ => ?_)) ?_
  · refine ⟨fun _ _ => rfl, rfl, fun _ _ => rfl, Or.inl ⟨e888, by rw [hS0]; rfl, ?_, e889⟩⟩
    rw [hS0, e887]; simp [lcard]
  · have g881 := (fr _ (by omega)).trans e881
    have g882 := (fr _ (by omega)).trans e882
    have g883 := (fr _ (by omega)).trans e883
    have g891 := (fr _ (by omega)).trans e891
    have g10 := (fr _ (by omega)).trans e10
    have hLi : c₂.nmem (bL + i) = lb i := by rw [fm _ (by omega)]; exact hL i hi
    have hli := hlb i hi
    have hCi : c₂.nmem (bC + lb i) = cntL lb m (lb i) := by
      rw [fm _ (by omega)]; exact hC i hi
    have hcnt := cntL_le lb m (lb i)
    unfold gScan
    refine spec_seq ?_
    rcases fs with ⟨h0, hgr, hacc, h889⟩ | ⟨h1, hgr⟩
    · refine spec_ifLtN_true (by rw [h0, g10]; omega) ?_
      set S := gp k bG c₂.nmem with hS
      have hSl : S (lb i) = true ↔ c₂.nmem (bG + lb i) ≠ 0 := by
        rw [hS]; unfold gp; simp [hli.2]
      have hnew : lcard m lb (addL S (lb i)) =
          c₂.nreg 887 + if c₂.nmem (bG + lb i) = 0 then cntL lb m (lb i) else 0 := by
        rw [lcard_addL, hacc]
        by_cases hz : c₂.nmem (bG + lb i) = 0
        · have : ¬ S (lb i) = true := fun h => hSl.1 h hz
          simp [this, hz]
        · have : S (lb i) = true := hSl.2 hz
          simp only [this, hz, ↓reduceIte]
      have hle := lcard_le m lb (addL S (lb i))
      refine spec_use (gProc_exec (P := P) (m := m) (bL := bL) (bC := bC) (bG := bG) (i := i)
        (ℓ := lb i) (cnt := cntL lb m (lb i)) (g := c₂.nmem (bG + lb i)) (acc := c₂.nreg 887)
        c₂ hw₂ g881 g882 g883 hb g891 g10 ha rfl hLi rfl hCi (by omega) hcnt (by omega)
        (by omega) (by omega) wm) ?_
      intro c₃ t₃ ht₃ hw₃ ⟨hr, hrr, hrm, ho, k1, k2, k3⟩
      rw [← hnew] at k1 k2 k3
      refine spec_instr (Exec.addN ‹_› 892 892 10 (by rw [hr _ (by omega), hr _ (by omega), ha,
        g10] <;> omega)) fun _ => ?_
      have hrest := drop_range_cons hi
      have hstep := hgr
      rw [hrest] at hstep
      simp only [grpL] at hstep
      refine ⟨by omega, by config_simp; rw [hr _ (by omega), hr _ (by omega), ha, g10],
        by config_simp; rw [hr _ (by omega)]; exact hb, fun r hr' => ?_, ?_, fun a ha' => ?_, ?_⟩
      · config_simp; simp only [upd_apply]
        split_ifs <;> first | omega | (rw [hr r (by omega)]; exact fr r hr')
      · config_simp; rw [ho, fo]
      · config_simp
        rcases Nat.lt_or_ge m (4 * lcard m lb (addL S (lb i))) with h2 | h2
        · rcases Nat.lt_or_ge (3 * m) (4 * lcard m lb (addL S (lb i))) with h3 | h3
          · rw [(k3 h3).1]; exact fm a ha'
          · rw [(k2 h2 h3).1, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
            exact fm a ha'
        · rw [(k1 h2).1, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
          exact fm a ha'
      · config_simp
        rcases Nat.lt_or_ge m (4 * lcard m lb (addL S (lb i))) with h2 | h2
        · rcases Nat.lt_or_ge (3 * m) (4 * lcard m lb (addL S (lb i))) with h3 | h3
          · obtain ⟨a1, -, a3, a4⟩ := k3 h3
            refine Or.inr ⟨a3, ?_⟩
            rw [hstep, a4, a1]
            unfold rp
            rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
              ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
              ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
          · obtain ⟨a1, -, a3, a4⟩ := k2 h2 h3
            refine Or.inr ⟨a3, ?_⟩
            rw [hstep, a4, a1, h889]
            unfold rp
            rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
              ite_eq_left_of_eq_true _ _ (eq_true h3), ite_eq_left_of_eq_true _ _ (eq_true rfl),
              gp_upd hli.2]
        · obtain ⟨a1, a2, a3, a4⟩ := k1 h2
          refine Or.inl ⟨by rw [a3, h0], ?_, ?_, by rw [a4, h889]⟩
          · rw [hstep, ite_eq_left_of_eq_true _ _ (eq_true h2), a1, gp_upd hli.2]
          · rw [a2, a1, gp_upd hli.2]
    · refine spec_ifLtN_false (by rw [h1, g10]; omega) ?_
      refine spec_skip hw₂ ?_
      refine spec_instr (Exec.addN ‹_› 892 892 10 (by rw [ha, g10]; omega)) fun _ => ?_
      refine ⟨by omega, by config_simp; rw [ha, g10], by config_simp; exact hb,
        fun r hr' => ?_, by config_simp; exact fo, fun a ha' => by config_simp; exact fm a ha',
        Or.inr ⟨by config_simp; exact h1, by config_simp; exact hgr⟩⟩
      · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact fr r hr'
  · intro c' t ht _ ⟨_, fr, fo, fm, fs⟩
    refine ⟨by omega, ?_, fr, fo, fm⟩
    rcases fs with ⟨_, hgr, _, h889⟩ | ⟨_, hgr⟩
    · rw [hgr, List.drop_eq_nil_of_le (by simp), h889]; rfl
    · exact hgr

/-- The side of one dart: `0` exactly for a label of the group found. -/
theorem gSide_exec {k bG solo ℓ : ℕ} (c : Config) (hw : WordsBounded W c)
    (h889 : c.nreg 889 = solo) (h894 : c.nreg 894 = ℓ) (h883 : c.nreg 883 = bG)
    (h10 : c.nreg 10 = 1) (hℓ : ℓ ≤ k) (wG : bG + ℓ ≤ W) (w1 : 1 ≤ W) :
    ∃ c' t, Exec P W (.ifLtN 889 10
      (.seq (block [.addN 895 883 894, .loadN 896 895])
        (.ifLtN 896 10 (.instr (.constN 899 1)) (.instr (.constN 899 0))))
      (.ifLtN 894 889 (.instr (.constN 899 1))
        (.ifLtN 889 894 (.instr (.constN 899 1)) (.instr (.constN 899 0))))) c c' t ∧ t ≤ 7 ∧
      c'.nreg 899 = (if rp k bG c.nmem solo ℓ = true then 0 else 1) ∧
      (∀ r, r < 895 ∨ (896 < r ∧ r < 899) ∨ 899 < r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.output = c.output := by
  by_cases hs : solo = 0
  · have hrp : rp k bG c.nmem solo ℓ = decide (c.nmem (bG + ℓ) ≠ 0) := by
      unfold rp gp; simp [hs, hℓ]
    refine spec_ifLtN_true (by rw [h889, h10]; omega) ?_
    refine spec_seq ?_
    exec_block
    all_goals try ((try config_simp); (try simp only [h883, h894]) <;> omega)
    by_cases hg : c.nmem (bG + ℓ) = 0
    · refine spec_ifLtN_true (by config_simp; rw [h883, h894, hg, h10]; omega) ?_
      refine spec_instr (Exec.constN ‹_› 899 1 (by omega)) fun _ => ?_
      refine ⟨by omega, by config_simp; rw [hrp]; simp [hg], fun r hr => ?_, rfl, rfl⟩
      config_simp; simp only [upd_apply]; split_ifs <;> omega
    · refine spec_ifLtN_false (by config_simp; rw [h883, h894, h10]; omega) ?_
      refine spec_instr (Exec.constN ‹_› 899 0 (by omega)) fun _ => ?_
      refine ⟨by omega, by config_simp; rw [hrp]; simp [hg], fun r hr => ?_, rfl, rfl⟩
      config_simp; simp only [upd_apply]; split_ifs <;> omega
  · have hrp : rp k bG c.nmem solo ℓ = (ℓ == solo) := by unfold rp; simp [hs]
    refine spec_ifLtN_false (by rw [h889, h10]; omega) ?_
    by_cases h1 : ℓ < solo
    · refine spec_ifLtN_true (by rw [h889, h894]; exact h1) ?_
      refine spec_instr (Exec.constN ‹_› 899 1 (by omega)) fun _ => ?_
      refine ⟨by omega, by config_simp; rw [hrp]; simp; omega, fun r hr => ?_, rfl, rfl⟩
      config_simp; simp only [upd_apply]; split_ifs <;> omega
    · refine spec_ifLtN_false (by rw [h889, h894]; exact h1) ?_
      by_cases h2 : solo < ℓ
      · refine spec_ifLtN_true (by rw [h889, h894]; exact h2) ?_
        refine spec_instr (Exec.constN ‹_› 899 1 (by omega)) fun _ => ?_
        refine ⟨by omega, by config_simp; rw [hrp]; simp; omega, fun r hr => ?_, rfl, rfl⟩
        config_simp; simp only [upd_apply]; split_ifs <;> omega
      · refine spec_ifLtN_false (by rw [h889, h894]; exact h2) ?_
        refine spec_instr (Exec.constN ‹_› 899 0 (by omega)) fun _ => ?_
        refine ⟨by omega, by config_simp; rw [hrp]; simp; omega, fun r hr => ?_, rfl, rfl⟩
        config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **The sides**: at `bO + x` the side `0` for a dart of the group found, `1` otherwise. -/
theorem gOutLoop_exec {m k bL bG bO solo : ℕ} {lb : ℕ → ℕ} (c₁ : Config) (hw : WordsBounded W c₁)
    (e881 : c₁.nreg 881 = bL) (e883 : c₁.nreg 883 = bG) (e884 : c₁.nreg 884 = bO)
    (e880 : c₁.nreg 880 = m) (e889 : c₁.nreg 889 = solo) (e10 : c₁.nreg 10 = 1)
    (e892 : c₁.nreg 892 = 0) (hL : ∀ x < m, c₁.nmem (bL + x) = lb x)
    (hlb : ∀ x < m, lb x ≤ k) (wL : bL + m ≤ W) (wG : bG + k + 1 ≤ W) (wO : bO + m ≤ W)
    (wm : m + 1 ≤ W) (dOL : bO + m ≤ bL ∨ bL + m ≤ bO) (dGO : bG + k + 1 ≤ bO ∨ bO + m ≤ bG) :
    ∃ c' t, Exec P W (.whileLtN 892 880 gOut) c₁ c' t ∧ t ≤ 14 * m + 2 ∧
      (∀ y < m, c'.nmem (bO + y) = if rp k bG c₁.nmem solo (lb y) = true then 0 else 1) ∧
      (∀ r, r < 892 ∨ 899 < r → c'.nreg r = c₁.nreg r) ∧ c'.output = c₁.output ∧
      (∀ a, (a < bO ∨ bO + m ≤ a) → c'.nmem a = c₁.nmem a) := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ r, r < 892 ∨ 899 < r → c'.nreg r = c₁.nreg r) ∧ c'.output = c₁.output ∧
      (∀ a, (a < bO ∨ bO + m ≤ a) → c'.nmem a = c₁.nmem a) ∧
      (∀ y < i, c'.nmem (bO + y) = if rp k bG c₁.nmem solo (lb y) = true then 0 else 1)
  refine spec_use (forLoop_exec (P := P) (a := 892) (bR := 880) (body := gOut) J (K := 12)
    (n := m) _ hw e892 e880 ?_ (fun i c₂ hi hw₂ ha hb ⟨fr, fo, fm, fv⟩ => ?_)) ?_
  · exact ⟨fun _ _ => rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (by omega)⟩
  · have g881 := (fr _ (by omega)).trans e881
    have g883 := (fr _ (by omega)).trans e883
    have g884 := (fr _ (by omega)).trans e884
    have g889 := (fr _ (by omega)).trans e889
    have g10 := (fr _ (by omega)).trans e10
    have hLi : c₂.nmem (bL + i) = lb i := by rw [fm _ (by omega)]; exact hL i hi
    have hli := hlb i hi
    have hgp : rp k bG c₂.nmem solo = rp k bG c₁.nmem solo := by
      unfold rp; rw [gp_congr fun ℓ hℓ => fm _ (by omega)]
    unfold gOut
    refine spec_seq ?_
    exec_block
    all_goals try ((try config_simp); (try simp only [g881, ha]) <;> omega)
    refine spec_seq ?_
    refine spec_use (gSide_exec (P := P) (k := k) (bG := bG) (solo := solo) (ℓ := lb i) _ ‹_›
      (by config_simp; exact g889) (by config_simp; rw [g881, ha, hLi])
      (by config_simp; exact g883) (by config_simp; exact g10) hli (by omega) (by omega)) ?_
    intro c₃ t₃ ht₃ hw₃ ⟨h899, hr, hm, ho⟩
    config_simp at h899
    rw [hgp] at h899
    have q884 : c₃.nreg 884 = bO := by rw [hr _ (by omega)]; config_simp; exact g884
    have q892 : c₃.nreg 892 = i := by rw [hr _ (by omega)]; config_simp; exact ha
    have q10 : c₃.nreg 10 = 1 := by rw [hr _ (by omega)]; config_simp; exact g10
    have q880 : c₃.nreg 880 = m := by rw [hr _ (by omega)]; config_simp; exact hb
    exec_block
    all_goals try ((try config_simp); (try simp only [q884, q892, q10]) <;> omega)
    refine ⟨by omega, ?_, ?_, fun r hr' => ?_, ?_, fun a ha' => ?_, fun y hy => ?_⟩
    · config_simp; rw [q892, q10]
    · config_simp; exact q880
    · have hr2 : c₃.nreg r = c₂.nreg r := by
        rw [hr r (by omega)]; config_simp
        repeat rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      config_simp
      repeat rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      rw [hr2]; exact fr r hr'
    · config_simp; rw [ho, fo]
    · config_simp; rw [hr _ (by omega), hr _ (by omega)]; config_simp
      rw [g884, ha, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hm]
      exact fm a ha'
    · config_simp; rw [hr _ (by omega), hr _ (by omega)]; config_simp
      rw [g884, ha, upd_apply, hm]
      rcases Nat.lt_or_ge y i with hlt | hge
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact fv y hlt
      · have : y = i := by omega
        subst this
        rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]; exact h899
  · intro c' t ht _ ⟨_, fr, fo, fm, fv⟩
    exact ⟨by omega, fv, fr, fo, fm⟩

theorem gSetup_exec {m : ℕ} (c : Config) (hc : WordsBounded W c) (r880 : c.nreg 880 = m)
    (wm : 4 * m + 3 ≤ W) :
    ∃ c' t, Exec P W gSetup c c' t ∧ t ≤ 7 ∧ c'.nreg 886 = 0 ∧ c'.nreg 887 = 0 ∧
      c'.nreg 888 = 0 ∧ c'.nreg 889 = 0 ∧ c'.nreg 891 = m + m + m ∧ c'.nreg 892 = 0 ∧
      (∀ r, r < 886 ∨ r = 890 ∨ 892 < r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.output = c.output := by
  unfold gSetup
  exec_block
  all_goals try ((try config_simp); (try simp only [r880]) <;> omega)
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl⟩
  all_goals config_simp
  all_goals try ((try simp only [r880]) <;> omega)
  repeat rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-- **The grouping on the machine.** From the labels `lb x ∈ [1, k]` of the darts `x < m` at
`bL + x` and the number of darts of the label of each dart at `bC + lb x`, `grpProg` writes at
`bO + x` the side `0` for the darts with a label of `grpL` from the empty set over `0, …, m - 1`,
`1` for the others, within `5 k + 34 m + 20` steps. -/
theorem grpProg_exec {m k bL bC bG bO : ℕ} {lb : ℕ → ℕ} (c : Config) (hc : WordsBounded W c)
    (hI : GrpIn m k bL bC bG bO c) (hlay : GrpLay m k bL bC bG bO W)
    (hL : ∀ x < m, c.nmem (bL + x) = lb x) (hlb : ∀ x < m, 1 ≤ lb x ∧ lb x ≤ k)
    (hC : ∀ x < m, c.nmem (bC + lb x) = cntL lb m (lb x)) :
    ∃ c' t, Exec P W grpProg c c' t ∧ t ≤ 5 * k + 34 * m + 20 ∧
      (∀ x < m, c'.nmem (bO + x) =
        if grpL m lb (fun _ => false) (List.range m) (lb x) = true then 0 else 1) ∧
      (∀ r, r < 886 ∨ r = 890 ∨ 899 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      (∀ a, (a < bG ∨ bG + k + 1 ≤ a) → (a < bO ∨ bO + m ≤ a) → c'.nmem a = c.nmem a) := by
  obtain ⟨r10, r880, r881, r882, r883, r884, r885⟩ := hI
  have hlay' := hlay
  obtain ⟨wL, wC, wG, wO, wm, dGL, dGC, dGO, dOL, dOC⟩ := hlay
  suffices H : ∃ c' t, Exec P W grpProg c c' t ∧ t ≤ 5 * k + 34 * m + 20 ∧
      (∀ x < m, c'.nmem (bO + x) =
        if grpL m lb (fun _ => false) (List.range m) (lb x) = true then 0 else 1) ∧
      (∀ r, r < 886 ∨ r = 890 ∨ 899 < r → c'.nreg r = c.nreg r) ∧ c'.output = c.output ∧
      (∀ a, (a < bG ∨ bG + k + 1 ≤ a) → (a < bO ∨ bO + m ≤ a) → c'.nmem a = c.nmem a) by
    obtain ⟨c', t, hex, ht, h1, h2, h3, h4⟩ := H
    have hrr := Exec.natS_frame hex natS_grpProg
    exact ⟨c', t, hex, ht, h1, h2, hrr.1, hrr.2, h3, h4⟩
  unfold grpProg
  refine spec_seq ?_
  refine spec_use (gSetup_exec (P := P) c hc r880 wm) ?_
  intro c₁ t₁ ht₁ hw₁ ⟨s886, s887, s888, s889, s891, s892, sfr, sm, so⟩
  have s10 := (sfr 10 (by omega)).trans r10
  refine spec_seq ?_
  refine spec_use (gZeroLoop_exec (P := P) (k := k) (bG := bG) c₁ hw₁
    ((sfr _ (by omega)).trans r883) ((sfr _ (by omega)).trans r885) s886 s10 s892 wG) ?_
  intro c₂ t₂ ht₂ hw₂ ⟨hG0, fr₂, fo₂, fm₂⟩
  have g : ∀ r, r < 886 ∨ r = 890 ∨ 899 < r → c₂.nreg r = c.nreg r := fun r hr => by
    rw [fr₂ r (by omega), sfr r (by omega)]
  have g' : ∀ r, 886 ≤ r ∧ r < 892 → c₂.nreg r = c₁.nreg r := fun r hr => fr₂ r (by omega)
  have hm₂ : ∀ a, (a < bG ∨ bG + k + 1 ≤ a) → c₂.nmem a = c.nmem a := fun a ha => by
    rw [fm₂ a ha, sm]
  refine spec_seq ?_
  refine spec_instr (Exec.constN ‹_› 892 0 (by omega)) fun hw₂' => ?_
  refine spec_seq ?_
  refine spec_use (gScanLoop_exec (P := P) (m := m) (k := k) (bL := bL) (bC := bC) (bG := bG)
    (bO := bO) (lb := lb) _ hw₂'
    (by config_simp; rw [g _ (by omega), r881]) (by config_simp; rw [g _ (by omega), r882])
    (by config_simp; rw [g _ (by omega), r883]) (by config_simp; rw [g _ (by omega), r880])
    (by config_simp; rw [g' _ (by omega), s891]) (by config_simp; rw [g _ (by omega), r10])
    (by config_simp) (by config_simp; rw [g' _ (by omega), s887])
    (by config_simp; rw [g' _ (by omega), s888]) (by config_simp; rw [g' _ (by omega), s889])
    (fun x hx => by config_simp; rw [hm₂ _ (by omega)]; exact hL x hx) hlb
    (fun x hx => by
      config_simp; rw [hm₂ _ (by have := hlb x hx; omega)]; exact hC x hx)
    (fun ℓ hℓ => by config_simp; exact hG0 ℓ hℓ) hlay') ?_
  intro c₃ t₃ ht₃ hw₃ ⟨hgr, fr₃, fo₃, fm₃⟩
  have G3 : ∀ r, r < 886 ∨ r = 890 ∨ 899 < r → c₃.nreg r = c.nreg r := fun r hr => by
    rw [fr₃ r (by omega)]; config_simp
    rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), g r hr]
  refine spec_seq ?_
  refine spec_instr (Exec.constN ‹_› 892 0 (by omega)) fun hw₃' => ?_
  refine spec_use (gOutLoop_exec (P := P) (m := m) (k := k) (bL := bL) (bG := bG) (bO := bO)
    (solo := c₃.nreg 889) (lb := lb) _ hw₃'
    (by config_simp; rw [G3 _ (by omega), r881]) (by config_simp; rw [G3 _ (by omega), r883])
    (by config_simp; rw [G3 _ (by omega), r884]) (by config_simp; rw [G3 _ (by omega), r880])
    (by config_simp) (by config_simp; rw [G3 _ (by omega), r10]) (by config_simp)
    (fun x hx => by config_simp; rw [fm₃ _ (by omega), hm₂ _ (by omega)]; exact hL x hx)
    (fun x hx => (hlb x hx).2) wL wG wO (by omega) dOL dGO) ?_
  intro c₄ t₄ ht₄ hw₄ ⟨hO, fr₄, fo₄, fm₄⟩
  refine ⟨by omega, fun x hx => ?_, fun r hr => ?_, ?_, fun a h₁ h₂ => ?_⟩
  · rw [hO x hx, hgr]
  · rw [fr₄ r (by omega)]; config_simp
    rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), G3 r hr]
  · rw [fo₄]; config_simp; rw [fo₃]; config_simp; rw [fo₂, so]
  · rw [fm₄ a h₂]; config_simp; rw [fm₃ a h₁, hm₂ a h₁]

/-! ### The sides are those of `splitM` -/

section Bridge

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {N : CombMap D V F}

/-- The darts `δ y`, `y < m`, with a label in `S`. -/
def lset (m : ℕ) (lb : ℕ → ℕ) (δ : ℕ → D) (S : ℕ → Bool) : Finset D :=
  ((range m).filter fun y => S (lb y) = true).image δ

variable {Pc : Finset D} {m : ℕ} {δ : ℕ → D} {lb : ℕ → ℕ}

lemma mem_lset (he : IsEnum m δ Pc) {S : ℕ → Bool} {x : ℕ} (hx : x < m) :
    δ x ∈ lset m lb δ S ↔ S (lb x) = true := by
  unfold lset
  simp only [mem_image, mem_filter, mem_range]
  constructor
  · rintro ⟨y, ⟨hy, hS⟩, e⟩
    rwa [he.inj y hy x hx e] at hS
  · exact fun h => ⟨x, ⟨hx, h⟩, rfl⟩

lemma card_lset (he : IsEnum m δ Pc) (S : ℕ → Bool) : (lset m lb δ S).card = lcard m lb S := by
  unfold lset lcard
  exact card_image_of_injOn fun x hx y hy e =>
    he.inj x (by simpa using (mem_filter.1 hx).1) y (by simpa using (mem_filter.1 hy).1) e

lemma lset_addL (S : ℕ → Bool) (ℓ : ℕ) :
    lset m lb δ (addL S ℓ) = lset m lb δ S ∪ lset m lb δ (fun j => j == ℓ) := by
  unfold lset addL
  rw [← image_union, ← filter_or]
  congr 1

lemma pcomp_lset (he : IsEnum m δ Pc)
    (hlab : ∀ x < m, ∀ y < m, lb x = lb y ↔ δ y ∈ pcomp N Pc (δ x)) {x : ℕ} (hx : x < m) :
    pcomp N Pc (δ x) = lset m lb δ (fun j => j == lb x) := by
  ext d
  constructor
  · intro hd
    obtain ⟨y, hy, rfl⟩ := he.surj d (pcomp_subset Pc _ hd)
    rw [mem_lset he hy]; simpa using ((hlab x hx y hy).2 hd).symm
  · intro hd
    obtain ⟨y, ⟨hy, hS⟩, rfl⟩ : ∃ y, (y ∈ range m ∧ (lb y == lb x) = true) ∧ δ y = d := by
      simpa [lset] using hd
    simp only [beq_iff_eq] at hS
    exact (hlab x hx y (by simpa using hy)).1 hS.symm

/-- **The grouping on labels is the grouping of the components**: the darts with a label of
`grpL S xs` are `grp N Pc (lset S) (xs.map δ)`, when the labels are the components. -/
theorem lset_grpL (he : IsEnum m δ Pc)
    (hlab : ∀ x < m, ∀ y < m, lb x = lb y ↔ δ y ∈ pcomp N Pc (δ x)) :
    ∀ (xs : List ℕ) (S : ℕ → Bool), (∀ x ∈ xs, x < m) →
      lset m lb δ (grpL m lb S xs) = grp N Pc (lset m lb δ S) (xs.map δ)
  | [], S, _ => rfl
  | x :: xs, S, hxs => by
    have hx : x < m := hxs x (List.mem_cons_self ..)
    have e : lset m lb δ S ∪ pcomp N Pc (δ x) = lset m lb δ (addL S (lb x)) := by
      rw [pcomp_lset he hlab hx, lset_addL]
    have hc := card_lset (lb := lb) he (addL S (lb x))
    have hm := he.card
    simp only [grpL, List.map_cons, grp]
    rw [e, hc, ← hm]
    split_ifs
    · exact lset_grpL he hlab xs _ fun y hy => hxs y (List.mem_cons_of_mem _ hy)
    · rfl
    · exact (pcomp_lset he hlab hx).symm

/-- **The sides written by `grpProg` are those of the split of the machine** when every
component has at most three quarters of the darts: for the order `ord Pc = [δ 0, …, δ (m - 1)]`
of the darts on the machine and labels that are the components, the side of `x < m` is `0`
exactly when `δ x` is in the first part of `splitM N ord cut Pc` (the second part is the rest). -/
theorem grpL_splitM {ord : Finset D → List D} (hord : ord Pc = (List.range m).map δ)
    (cut : Finset D → Finset D) (hsmall : ∀ d ∈ Pc, (pcomp N Pc d).card ≤ 3 * Pc.card / 4)
    (he : IsEnum m δ Pc) (hlab : ∀ x < m, ∀ y < m, lb x = lb y ↔ δ y ∈ pcomp N Pc (δ x))
    {x : ℕ} (hx : x < m) :
    (if grpL m lb (fun _ => false) (List.range m) (lb x) = true then 0 else 1) =
      if δ x ∈ (splitM N ord cut Pc).1 then 0 else 1 := by
  rw [splitM_small cut hsmall, hord,
    List.filter_eq_self.2 fun d hd => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hd
      simpa using he.mem y (List.mem_range.1 hy)]
  have h0 : lset m lb δ (fun _ => false) = ∅ := by simp [lset]
  have := lset_grpL he hlab (List.range m) (fun _ => false) fun y hy => List.mem_range.1 hy
  rw [h0] at this
  simp only [← this, mem_lset he hx]

/-- **The grouping on the machine gives the split of the machine** in the small-component case:
from the labels of the components (as `compProg_spec` leaves them) and the sizes of the
components of the darts, the side written by `grpProg` for the dart `x < m` is `0` exactly when
`δ x` is in the first part of `splitM N ord cut Pc`, for the order `ord Pc = [δ 0, …, δ (m - 1)]`
of the darts on the machine. -/
theorem grpProg_splitM {ord : Finset D → List D} (hord : ord Pc = (List.range m).map δ)
    (cut : Finset D → Finset D) (hsmall : ∀ d ∈ Pc, (pcomp N Pc d).card ≤ 3 * Pc.card / 4)
    (he : IsEnum m δ Pc) {k bL bC bG bO : ℕ} (c : Config) (hc : WordsBounded W c)
    (hI : GrpIn m k bL bC bG bO c) (hlay : GrpLay m k bL bC bG bO W)
    (hlb : ∀ x < m, 1 ≤ c.nmem (bL + x) ∧ c.nmem (bL + x) ≤ k)
    (hlab : ∀ x < m, ∀ y < m,
      c.nmem (bL + x) = c.nmem (bL + y) ↔ δ y ∈ pcomp N Pc (δ x))
    (hC : ∀ x < m, c.nmem (bC + c.nmem (bL + x)) = (pcomp N Pc (δ x)).card) :
    ∃ c' t, Exec P W grpProg c c' t ∧ t ≤ 5 * k + 34 * m + 20 ∧
      (∀ x < m, c'.nmem (bO + x) = if δ x ∈ (splitM N ord cut Pc).1 then 0 else 1) ∧
      (∀ r, r < 886 ∨ r = 890 ∨ 899 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      (∀ a, (a < bG ∨ bG + k + 1 ≤ a) → (a < bO ∨ bO + m ≤ a) → c'.nmem a = c.nmem a) := by
  set lb : ℕ → ℕ := fun x => c.nmem (bL + x)
  have hC' : ∀ x < m, c.nmem (bC + lb x) = cntL lb m (lb x) := fun x hx => by
    rw [hC x hx]
    exact image_filter_enum he (pcomp_subset Pc _) fun y hy => by
      rw [eq_comm]; exact hlab x hx y hy
  obtain ⟨c', t, hex, ht, hO, hr, hrr, hrm, ho, hm⟩ :=
    grpProg_exec (P := P) (lb := lb) c hc hI hlay (fun _ _ => rfl) hlb hC'
  exact ⟨c', t, hex, ht, fun x hx => by rw [hO x hx]; exact grpL_splitM hord cut hsmall he hlab hx,
    hr, hrr, hrm, ho, hm⟩

end Bridge

end NegSSSP

end PlanarFlow
