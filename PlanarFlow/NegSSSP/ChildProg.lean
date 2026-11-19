module

public import PlanarFlow.NegSSSP.ChildSem
public import PlanarFlow.NegSSSP.LinGlue
public import PlanarFlow.Klein.ExecNat

/-!
# The child encodings on the machine, part 1: the list of the child

The child of side `s` of a piece is numbered by a list `L` of indices of the parent's numbering
(`Frame.chL`): the indices `h < m` with side `SD[h] = s` in order (`oldA`), then the reverses
`AL[h]` of these not yet listed, appended in order (`apnd`). `ciProg` computes `L` in two
arrays: `OLD[j] = L[j]` (`j < #L`) and the position table `NI[x] = #(L before x) + 1` for
`x ∈ L`, `0` otherwise (`NIv`), `x < k`.

Registers `2930 … 2965` (free in the split, the node and the driver): `r2930 = s`,
`r2931 = d` (the parent's data), `r2932 = m`, `r2933 = k`, `r2934 = Ob` (the sides),
`r2935 = Xb` (`NI`), `r2936 = Yb` (`OLD`), `r2937` the child's data (read in part 2).

* `NIv`, `NIv_snoc`, `apnd_snoc`, `oldA_succ`.
* **`ciProg_exec`**: within `5 k + 14 m + 17 mₛ + 25` steps (`mₛ` the darts of the side), with
  `AL[x] = nmem (d + 4 + k + x) < k` for `x < k` (the reversal of the parent's frame):
  `r2950 = #oldA`, `r2951 = #L`, `NI[x] = NIv L x` for `x < k`, `OLD[j] = L[j]`, the bases of the
  parent's arrays `r2952 … r2957 = d + 4 + j k`; memory outside `NI`, `OLD` kept; registers
  outside `2938 … 2957` kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Frame

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### Lists -/

/-- The position table of a list: `idx + 1` on its elements, `0` elsewhere. -/
def NIv (L : List ℕ) (x : ℕ) : ℕ := if x ∈ L then L.idxOf x + 1 else 0

theorem NIv_nil (x : ℕ) : NIv [] x = 0 := by simp [NIv]

theorem NIv_snoc {L : List ℕ} {x : ℕ} (hx : x ∉ L) (y : ℕ) :
    NIv (L ++ [x]) y = if y = x then L.length + 1 else NIv L y := by
  unfold NIv
  by_cases hy : y = x
  · subst hy
    simp [List.idxOf_append_of_notMem hx]
  · by_cases hyL : y ∈ L
    · simp [hy, hyL, List.idxOf_append_of_mem hyL]
    · simp [hy, hyL]

theorem NIv_pos_iff {L : List ℕ} {x : ℕ} : 0 < NIv L x ↔ x ∈ L := by
  unfold NIv; split_ifs with h <;> simp [h]

theorem apnd_snoc : ∀ (L xs : List ℕ) (x : ℕ),
    apnd L (xs ++ [x]) = if x ∈ apnd L xs then apnd L xs else apnd L xs ++ [x]
  | L, [], x => by by_cases h : x ∈ L <;> simp [h, apnd]
  | L, y :: ys, x => by
    simp only [List.cons_append, apnd]
    exact apnd_snoc _ ys x

theorem apnd_prefix : ∀ (L xs : List ℕ), L <+: apnd L xs
  | L, [] => by simp [apnd]
  | L, y :: ys => by
    simp only [apnd]
    refine List.IsPrefix.trans ?_ (apnd_prefix _ ys)
    split_ifs
    · exact List.prefix_refl L
    · exact List.prefix_append L [y]

theorem apnd_mem : ∀ (L xs : List ℕ) (x : ℕ), x ∈ apnd L xs → x ∈ L ∨ x ∈ xs
  | L, [], x, h => by simpa [apnd] using h
  | L, y :: ys, x, h => by
    simp only [apnd] at h
    rcases apnd_mem _ ys x h with h | h
    · split_ifs at h
      · exact Or.inl h
      · rcases List.mem_append.1 h with h | h
        · exact Or.inl h
        · rw [List.mem_singleton] at h; exact Or.inr (h ▸ List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem apnd_nodup : ∀ (L xs : List ℕ), L.Nodup → (apnd L xs).Nodup
  | L, [], h => by simpa [apnd] using h
  | L, y :: ys, h => by
    simp only [apnd]
    apply apnd_nodup
    split_ifs with hy
    · exact h
    · rw [List.nodup_append]
      exact ⟨h, List.nodup_singleton y, fun a ha b hb e => by
        rw [List.mem_singleton] at hb; subst hb; subst e; exact hy ha⟩

theorem oldA_succ (s i : ℕ) (SD : ℕ → ℕ) :
    oldA s (i + 1) SD = oldA s i SD ++ (if SD i = s then [i] else []) := by
  unfold oldA
  rw [List.range_succ, List.filter_append]
  congr 1
  by_cases h : SD i = s <;> simp [h]

theorem oldA_lt {s i : ℕ} {SD : ℕ → ℕ} {x : ℕ} (hx : x ∈ oldA s i SD) : x < i := by
  rw [oldA, List.mem_filter, List.mem_range] at hx; exact hx.1

theorem oldA_nodup (s i : ℕ) (SD : ℕ → ℕ) : (oldA s i SD).Nodup :=
  (List.nodup_range).filter _

theorem length_le_of_lt {L : List ℕ} (hL : L.Nodup) {k : ℕ} (h : ∀ x ∈ L, x < k) :
    L.length ≤ k := by
  rw [← List.toFinset_card_of_nodup hL]
  calc L.toFinset.card ≤ (Finset.range k).card :=
        Finset.card_le_card fun x hx => Finset.mem_range.2 (h x (List.mem_toFinset.1 hx))
    _ = k := Finset.card_range k

/-! ### The program -/

/-- `NI[i] := 0` (`i = r2940`). -/
def ciZ : Stmt := block [.addN 2942 2935 2940, .storeN 2942 2938, .addN 2940 2940 2939]

/-- Append `i = r2940` to the list: `NI[i] := len + 1`, `OLD[len] := i`, `len := len + 1`. -/
def ciAddA : Stmt := block [.addN 2944 2941 2939, .addN 2942 2935 2940, .storeN 2942 2944,
  .addN 2942 2936 2941, .storeN 2942 2940, .copyN 2941 2944]

/-- Append `a = r2945` to the list. -/
def ciAddB : Stmt := block [.addN 2944 2941 2939, .addN 2942 2935 2945, .storeN 2942 2944,
  .addN 2942 2936 2941, .storeN 2942 2945, .copyN 2941 2944]

/-- One step of the first pass: `i` appended when `SD[i] = s`. -/
def ciA : Stmt :=
  .seq (block [.addN 2942 2934 2940, .loadN 2943 2942])
    (.seq (.ifLtN 2943 2930 .skip (.ifLtN 2930 2943 .skip ciAddA))
      (block [.addN 2940 2940 2939]))

/-- One step of the second pass: `a = AL[OLD[i]]` appended when not yet listed. -/
def ciB : Stmt :=
  .seq (block [.addN 2942 2936 2940, .loadN 2943 2942, .addN 2942 2953 2943, .loadN 2945 2942,
      .addN 2942 2935 2945, .loadN 2946 2942])
    (.seq (.ifLtN 2946 2939 ciAddB .skip) (block [.addN 2940 2940 2939]))

/-- The constants and the bases of the parent's arrays. -/
def ciSet : Stmt := block [.constN 2938 0, .constN 2939 1, .constN 2940 0, .constN 2941 0,
  .constN 2942 4, .addN 2952 2931 2942, .addN 2953 2952 2933, .addN 2954 2953 2933,
  .addN 2955 2954 2933, .addN 2956 2955 2933, .addN 2957 2956 2933]

/-- **The list of the child** (see the module docstring). -/
def ciProg : Stmt :=
  .seq ciSet <| .seq (.whileLtN 2940 2933 ciZ) <|
  .seq (block [.constN 2940 0]) <| .seq (.whileLtN 2940 2932 ciA) <|
  .seq (block [.copyN 2950 2941, .constN 2940 0]) <| .seq (.whileLtN 2940 2950 ciB) <|
  block [.copyN 2951 2941]

theorem ciProg_natOnly : Klein.natOnly ciProg = true := by kernel_rfl

variable {P : Input} {W : ℕ}

/-! ### The blocks -/

theorem ciZ_exec (c : Config) (hc : WordsBounded W c) {Xb i : ℕ} (r35 : c.nreg 2935 = Xb)
    (r40 : c.nreg 2940 = i) (r38 : c.nreg 2938 = 0) (r39 : c.nreg 2939 = 1)
    (w1 : Xb + i ≤ W) (w2 : i + 1 ≤ W) :
    ∃ c' k, Exec P W ciZ c c' k ∧ k = 3 ∧ c'.nmem = upd c.nmem (Xb + i) 0 ∧
      c'.nreg 2940 = i + 1 ∧ (∀ r, r ≠ 2940 → r ≠ 2942 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ciZ
  exec_block
  all_goals try ((try config_simp); (try simp only [r35, r38, r39, r40]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r35, r38, r40]
  · config_simp; simp only [r39, r40]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem ciAddA_exec (c : Config) (hc : WordsBounded W c) {Xb Yb x len : ℕ}
    (r35 : c.nreg 2935 = Xb) (r36 : c.nreg 2936 = Yb) (r39 : c.nreg 2939 = 1)
    (r40 : c.nreg 2940 = x) (r41 : c.nreg 2941 = len) (w1 : Xb + x ≤ W) (w2 : Yb + len ≤ W)
    (w3 : len + 1 ≤ W) :
    ∃ c' k, Exec P W ciAddA c c' k ∧ k = 6 ∧
      c'.nmem = upd (upd c.nmem (Xb + x) (len + 1)) (Yb + len) x ∧ c'.nreg 2941 = len + 1 ∧
      (∀ r, r ≠ 2941 → r ≠ 2942 → r ≠ 2944 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ciAddA
  exec_block
  all_goals try ((try config_simp); (try simp only [r35, r36, r39, r40, r41]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r35, r36, r39, r40, r41]
  · config_simp; simp only [r39, r41]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem ciAddB_exec (c : Config) (hc : WordsBounded W c) {Xb Yb x len : ℕ}
    (r35 : c.nreg 2935 = Xb) (r36 : c.nreg 2936 = Yb) (r39 : c.nreg 2939 = 1)
    (r45 : c.nreg 2945 = x) (r41 : c.nreg 2941 = len) (w1 : Xb + x ≤ W) (w2 : Yb + len ≤ W)
    (w3 : len + 1 ≤ W) :
    ∃ c' k, Exec P W ciAddB c c' k ∧ k = 6 ∧
      c'.nmem = upd (upd c.nmem (Xb + x) (len + 1)) (Yb + len) x ∧ c'.nreg 2941 = len + 1 ∧
      (∀ r, r ≠ 2941 → r ≠ 2942 → r ≠ 2944 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ciAddB
  exec_block
  all_goals try ((try config_simp); (try simp only [r35, r36, r39, r45, r41]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r35, r36, r39, r45, r41]
  · config_simp; simp only [r39, r41]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- The add-one block closing a loop body. -/
theorem ciInc_exec (c : Config) (hc : WordsBounded W c) {i : ℕ} (r40 : c.nreg 2940 = i)
    (r39 : c.nreg 2939 = 1) (w : i + 1 ≤ W) :
    ∃ c' k, Exec P W (block [.addN 2940 2940 2939]) c c' k ∧ k = 1 ∧ c'.nreg 2940 = i + 1 ∧
      (∀ r, r ≠ 2940 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  all_goals try ((try config_simp); (try simp only [r39, r40]); omega)
  refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r39, r40]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem ciA_exec (c : Config) (hc : WordsBounded W c) {s Ob Xb Yb i len : ℕ}
    (r30 : c.nreg 2930 = s) (r34 : c.nreg 2934 = Ob) (r35 : c.nreg 2935 = Xb)
    (r36 : c.nreg 2936 = Yb) (r39 : c.nreg 2939 = 1) (r40 : c.nreg 2940 = i)
    (r41 : c.nreg 2941 = len) (w0 : Ob + i ≤ W) (w1 : Xb + i ≤ W) (w2 : Yb + len ≤ W)
    (w3 : len + 1 ≤ W) (w4 : i + 1 ≤ W) :
    ∃ c' k, Exec P W ciA c c' k ∧ k ≤ 13 ∧
      c'.nmem = (if c.nmem (Ob + i) = s then upd (upd c.nmem (Xb + i) (len + 1)) (Yb + len) i
        else c.nmem) ∧
      c'.nreg 2941 = (if c.nmem (Ob + i) = s then len + 1 else len) ∧ c'.nreg 2940 = i + 1 ∧
      (∀ r, r ≠ 2940 → r ≠ 2941 → r ≠ 2942 → r ≠ 2943 → r ≠ 2944 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ciA
  obtain ⟨c₁, k₁, e₁, hk₁, g43, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.addN 2942 2934 2940, .loadN 2943 2942]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 2943 = c.nmem (Ob + i) ∧ (∀ r, r ≠ 2942 → r ≠ 2943 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [r34, r40]); omega)
    refine ⟨rfl, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [r34, r40]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have R1 : ∀ r, r ≠ 2942 → r ≠ 2943 → c₁.nreg r = c.nreg r := gn₁
  obtain ⟨c₂, k₂, e₂, hk₂, gm₂, g41, gn₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
      Exec P W (.ifLtN 2943 2930 .skip (.ifLtN 2930 2943 .skip ciAddA)) c₁ c₂ k₂ ∧ k₂ ≤ 10 ∧
      c₂.nmem = (if c.nmem (Ob + i) = s then
        upd (upd c.nmem (Xb + i) (len + 1)) (Yb + len) i else c.nmem) ∧
      c₂.nreg 2941 = (if c.nmem (Ob + i) = s then len + 1 else len) ∧
      (∀ r, r ≠ 2941 → r ≠ 2942 → r ≠ 2944 → c₂.nreg r = c₁.nreg r) ∧
      c₂.rreg = c.rreg ∧ c₂.rmem = c.rmem ∧ c₂.output = c.output := by
    have q30 : c₁.nreg 2930 = s := by rw [R1 _ (by omega) (by omega), r30]
    rcases Nat.lt_trichotomy (c.nmem (Ob + i)) s with hlt | heq | hgt
    · have hne : c.nmem (Ob + i) ≠ s := by omega
      refine ⟨c₁, 0 + 1, .ifLtN_true (by rw [g43, q30]; exact hlt) (.skip e₁.wb_right),
        by omega, ?_, ?_, fun _ _ _ _ => rfl, gr₁, grm₁, go₁⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hne)]; exact gm₁
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hne), R1 _ (by omega) (by omega), r41]
    · obtain ⟨c₃, k₃, e₃, hk₃, h3m, h341, h3n, h3r, h3rm, h3o⟩ := ciAddA_exec (P := P) c₁
        e₁.wb_right (by rw [R1 _ (by omega) (by omega), r35])
        (by rw [R1 _ (by omega) (by omega), r36]) (by rw [R1 _ (by omega) (by omega), r39])
        (by rw [R1 _ (by omega) (by omega), r40]) (by rw [R1 _ (by omega) (by omega), r41])
        w1 w2 w3
      refine ⟨c₃, k₃ + 2 + 2, .ifLtN_false (by rw [g43, q30]; omega)
        (.ifLtN_false (by rw [g43, q30]; omega) e₃), by omega, ?_, ?_, h3n, by rw [h3r, gr₁],
        by rw [h3rm, grm₁], by rw [h3o, go₁]⟩
      · rw [ite_eq_left_of_eq_true _ _ (eq_true heq), h3m, gm₁]
      · rw [ite_eq_left_of_eq_true _ _ (eq_true heq), h341]
    · have hne : c.nmem (Ob + i) ≠ s := by omega
      refine ⟨c₁, 0 + 1 + 2, .ifLtN_false (by rw [g43, q30]; omega)
        (.ifLtN_true (by rw [g43, q30]; exact hgt) (.skip e₁.wb_right)),
        by omega, ?_, ?_, fun _ _ _ _ => rfl, gr₁, grm₁, go₁⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hne)]; exact gm₁
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hne), R1 _ (by omega) (by omega), r41]
  obtain ⟨c₃, k₃, e₃, hk₃, h40, hn₃, hm₃, hr₃, hrm₃, ho₃⟩ := ciInc_exec (P := P) c₂ e₂.wb_right
    (by rw [gn₂ _ (by omega) (by omega) (by omega), R1 _ (by omega) (by omega), r40])
    (by rw [gn₂ _ (by omega) (by omega) (by omega), R1 _ (by omega) (by omega), r39]) w4
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, by rw [hm₃, gm₂],
    by rw [hn₃ _ (by omega), g41], h40, fun r a b d e f => ?_, by rw [hr₃, gr₂],
    by rw [hrm₃, grm₂], by rw [ho₃, go₂]⟩
  rw [hn₃ r a, gn₂ r b d f, R1 r d e]

theorem ciB_exec (c : Config) (hc : WordsBounded W c) {Ab Xb Yb i len : ℕ}
    (r53 : c.nreg 2953 = Ab) (r35 : c.nreg 2935 = Xb)
    (r36 : c.nreg 2936 = Yb) (r39 : c.nreg 2939 = 1) (r40 : c.nreg 2940 = i)
    (r41 : c.nreg 2941 = len) (w0 : Yb + i ≤ W) (w1 : Ab + c.nmem (Yb + i) ≤ W)
    (w2 : Xb + c.nmem (Ab + c.nmem (Yb + i)) ≤ W) (w3 : Yb + len ≤ W)
    (w4 : len + 1 ≤ W) (w5 : i + 1 ≤ W) :
    let a := c.nmem (Ab + c.nmem (Yb + i))
    ∃ c' k, Exec P W ciB c c' k ∧ k ≤ 15 ∧
      c'.nmem = (if c.nmem (Xb + a) < 1 then upd (upd c.nmem (Xb + a) (len + 1)) (Yb + len) a
        else c.nmem) ∧
      c'.nreg 2941 = (if c.nmem (Xb + a) < 1 then len + 1 else len) ∧ c'.nreg 2940 = i + 1 ∧
      (∀ r, r ≠ 2940 → r ≠ 2941 → r ≠ 2942 → r ≠ 2943 → r ≠ 2944 → r ≠ 2945 → r ≠ 2946 →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  intro a
  unfold ciB
  obtain ⟨c₁, k₁, e₁, hk₁, g45, g46, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.addN 2942 2936 2940, .loadN 2943 2942, .addN 2942 2953 2943,
        .loadN 2945 2942, .addN 2942 2935 2945, .loadN 2946 2942]) c c₁ k₁ ∧ k₁ = 6 ∧
      c₁.nreg 2945 = a ∧ c₁.nreg 2946 = c.nmem (Xb + a) ∧
      (∀ r, r ≠ 2942 → r ≠ 2943 → r ≠ 2945 → r ≠ 2946 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [r36, r40, r53, r35]); omega)
    refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [a, r36, r40, r53]
    · config_simp; simp only [a, r36, r40, r53, r35]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have R1 : ∀ r, r ≠ 2942 → r ≠ 2943 → r ≠ 2945 → r ≠ 2946 → c₁.nreg r = c.nreg r := gn₁
  obtain ⟨c₂, k₂, e₂, hk₂, gm₂, g41, gn₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
      Exec P W (.ifLtN 2946 2939 ciAddB .skip) c₁ c₂ k₂ ∧ k₂ ≤ 7 ∧
      c₂.nmem = (if c.nmem (Xb + a) < 1 then
        upd (upd c.nmem (Xb + a) (len + 1)) (Yb + len) a else c.nmem) ∧
      c₂.nreg 2941 = (if c.nmem (Xb + a) < 1 then len + 1 else len) ∧
      (∀ r, r ≠ 2941 → r ≠ 2942 → r ≠ 2944 → c₂.nreg r = c₁.nreg r) ∧
      c₂.rreg = c.rreg ∧ c₂.rmem = c.rmem ∧ c₂.output = c.output := by
    have q39 : c₁.nreg 2939 = 1 := by rw [R1 _ (by omega) (by omega) (by omega) (by omega), r39]
    by_cases hlt : c.nmem (Xb + a) < 1
    · obtain ⟨c₃, k₃, e₃, hk₃, h3m, h341, h3n, h3r, h3rm, h3o⟩ := ciAddB_exec (P := P) c₁
        e₁.wb_right (by rw [R1 _ (by omega) (by omega) (by omega) (by omega), r35])
        (by rw [R1 _ (by omega) (by omega) (by omega) (by omega), r36]) q39 g45
        (by rw [R1 _ (by omega) (by omega) (by omega) (by omega), r41]) w2 w3 w4
      refine ⟨c₃, k₃ + 1, .ifLtN_true (by rw [g46, q39]; exact hlt) e₃, by omega, ?_, ?_, h3n,
        by rw [h3r, gr₁], by rw [h3rm, grm₁], by rw [h3o, go₁]⟩
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hlt), h3m, gm₁]
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hlt), h341]
    · refine ⟨c₁, 0 + 2, .ifLtN_false (by rw [g46, q39]; exact hlt) (.skip e₁.wb_right),
        by omega, ?_, ?_, fun _ _ _ _ => rfl, gr₁, grm₁, go₁⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hlt)]; exact gm₁
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hlt),
          R1 _ (by omega) (by omega) (by omega) (by omega), r41]
  obtain ⟨c₃, k₃, e₃, hk₃, h40, hn₃, hm₃, hr₃, hrm₃, ho₃⟩ := ciInc_exec (P := P) c₂ e₂.wb_right
    (by rw [gn₂ _ (by omega) (by omega) (by omega),
      R1 _ (by omega) (by omega) (by omega) (by omega), r40])
    (by rw [gn₂ _ (by omega) (by omega) (by omega),
      R1 _ (by omega) (by omega) (by omega) (by omega), r39]) w5
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, by rw [hm₃, gm₂],
    by rw [hn₃ _ (by omega), g41], h40, fun r a b d e f g h => ?_, by rw [hr₃, gr₂],
    by rw [hrm₃, grm₂], by rw [ho₃, go₂]⟩
  rw [hn₃ r a, gn₂ r b d f, R1 r d e g h]

set_option maxHeartbeats 2000000 in
theorem ciSet_exec (c : Config) (hc : WordsBounded W c) {d k : ℕ} (r31 : c.nreg 2931 = d)
    (r33 : c.nreg 2933 = k) (w : d + 4 + 5 * k ≤ W) (w4 : 4 ≤ W) :
    ∃ c' t, Exec P W ciSet c c' t ∧ t = 11 ∧ c'.nreg 2938 = 0 ∧ c'.nreg 2939 = 1 ∧
      c'.nreg 2940 = 0 ∧ c'.nreg 2941 = 0 ∧ c'.nreg 2952 = d + 4 ∧
      c'.nreg 2953 = d + 4 + k ∧ c'.nreg 2954 = d + 4 + 2 * k ∧
      c'.nreg 2955 = d + 4 + 3 * k ∧ c'.nreg 2956 = d + 4 + 4 * k ∧
      c'.nreg 2957 = d + 4 + 5 * k ∧
      (∀ r, (r < 2938 ∨ 2957 < r ∨ (2942 < r ∧ r < 2952)) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ciSet
  exec_block
  all_goals try ((try config_simp); (try simp only [r31, r33]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r31, r33] <;> omega)
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

/-- The memory outside the two scratch arrays is kept. -/
def MOut (Xb Yb k : ℕ) (c c' : Config) : Prop :=
  ∀ a, (a < Xb ∨ Xb + k ≤ a) → (a < Yb ∨ Yb + k ≤ a) → c'.nmem a = c.nmem a

/-- The arrays of a list `L`. -/
structure LArr (Xb Yb k : ℕ) (L : List ℕ) (c : Config) : Prop where
  ni : ∀ x < k, c.nmem (Xb + x) = NIv L x
  old : ∀ j < L.length, c.nmem (Yb + j) = L.getD j 0
  len : c.nreg 2941 = L.length

/-- Appending a new element to the arrays. -/
theorem LArr.snoc {Xb Yb k : ℕ} {L : List ℕ} {c c' : Config} (h : LArr Xb Yb k L c) {x : ℕ}
    (hx : x ∉ L) (hxk : x < k) (hlk : L.length < k)
    (hd : Xb + k ≤ Yb ∨ Yb + k ≤ Xb)
    (hm : c'.nmem = upd (upd c.nmem (Xb + x) (L.length + 1)) (Yb + L.length) x)
    (hl : c'.nreg 2941 = L.length + 1) : LArr Xb Yb k (L ++ [x]) c' := by
  refine ⟨fun y hy => ?_, fun j hj => ?_, by rw [hl, List.length_append]; rfl⟩
  · rw [hm, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), upd_apply,
      NIv_snoc hx]
    by_cases e : y = x
    · subst e; simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false e)]
      exact h.ni y hy
  · rw [List.length_append, List.length_singleton] at hj
    rw [hm, upd_apply]
    rcases Nat.lt_or_ge j L.length with hj' | hj'
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), upd_apply,
        ite_eq_right_of_eq_false _ _ (eq_false (by omega)), h.old j hj',
        List.getD_append _ _ _ _ hj']
    · have : j = L.length := by omega
      subst this
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      simp

theorem LArr.congr {Xb Yb k : ℕ} {L : List ℕ} {c c' : Config} (h : LArr Xb Yb k L c)
    (hm : c'.nmem = c.nmem) (hl : c'.nreg 2941 = c.nreg 2941) : LArr Xb Yb k L c' :=
  ⟨fun y hy => by rw [hm]; exact h.ni y hy, fun j hj => by rw [hm]; exact h.old j hj,
    by rw [hl]; exact h.len⟩

/-- The list of the child: the indices of side `s`, then the new reverses. -/
def ciL (s m : ℕ) (SD AL : ℕ → ℕ) : List ℕ := apnd (oldA s m SD) ((oldA s m SD).map AL)

/-- **The list of the child on the machine** (see the module docstring). -/
theorem ciProg_exec (c : Config) (hc : WordsBounded W c) {s d m k Ob Xb Yb : ℕ}
    (r30 : c.nreg 2930 = s) (r31 : c.nreg 2931 = d) (r32 : c.nreg 2932 = m)
    (r33 : c.nreg 2933 = k) (r34 : c.nreg 2934 = Ob) (r35 : c.nreg 2935 = Xb)
    (r36 : c.nreg 2936 = Yb) (hmk : m ≤ k)
    (hAL : ∀ x < k, c.nmem (d + 4 + k + x) < k)
    (wX : Xb + k ≤ W) (wY : Yb + k ≤ W) (wO : Ob + m ≤ W) (wd : d + 4 + 5 * k ≤ W)
    (w4 : k + 4 ≤ W)
    (dXY : Xb + k ≤ Yb ∨ Yb + k ≤ Xb) (dXO : Xb + k ≤ Ob ∨ Ob + m ≤ Xb)
    (dYO : Yb + k ≤ Ob ∨ Ob + m ≤ Yb) (dXA : Xb + k ≤ d + 4 + k ∨ d + 4 + 2 * k ≤ Xb)
    (dYA : Yb + k ≤ d + 4 + k ∨ d + 4 + 2 * k ≤ Yb) :
    let SD := fun x => c.nmem (Ob + x)
    let AL := fun x => c.nmem (d + 4 + k + x)
    ∃ c' t, Exec P W ciProg c c' t ∧
      t ≤ 5 * k + 15 * m + 17 * (oldA s m SD).length + 25 ∧
      c'.nreg 2950 = (oldA s m SD).length ∧ c'.nreg 2951 = (ciL s m SD AL).length ∧
      LArr Xb Yb k (ciL s m SD AL) c' ∧
      c'.nreg 2938 = 0 ∧ c'.nreg 2939 = 1 ∧ c'.nreg 2952 = d + 4 ∧
      c'.nreg 2953 = d + 4 + k ∧ c'.nreg 2954 = d + 4 + 2 * k ∧
      c'.nreg 2955 = d + 4 + 3 * k ∧ c'.nreg 2956 = d + 4 + 4 * k ∧
      c'.nreg 2957 = d + 4 + 5 * k ∧ MOut Xb Yb k c c' ∧
      (∀ r, (r < 2938 ∨ 2957 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  intro SD AL
  unfold ciProg
  obtain ⟨c₁, t₁, e₁, ht₁, s38, s39, s40, s41, s52, s53, s54, s55, s56, s57, fr₁, fm₁, fr₁', frm₁, fo₁⟩ :=
    ciSet_exec (P := P) c hc r31 r33 (by omega) (by omega)
  -- the zeros
  let J₀ : ℕ → Config → Prop := fun i c' =>
    (∀ x < i, c'.nmem (Xb + x) = 0) ∧ (∀ a, (a < Xb ∨ Xb + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 2940 → r ≠ 2942 → c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, t₂, e₂, ht₂, hw₂, z1, z2, z3, zr, zrm, zo⟩ := forLoop_exec (P := P) (a := 2940)
    (bR := 2933) (body := ciZ) J₀ (K := 3) (n := k) c₁ e₁.wb_right s40
    (by rw [fr₁ _ (by omega)]; exact r33)
    ⟨fun x hx => absurd hx (by omega), fun a _ => by rw [fm₁], fun _ _ _ => rfl,
      fr₁', frm₁, fo₁⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j3, jr, jrm, jo⟩ := hJ
      obtain ⟨c'', t, ex, ht, hm, h40, hn, hr, hrm, ho⟩ := ciZ_exec (P := P) (Xb := Xb) (i := i)
        c' hw (by rw [j3 _ (by omega) (by omega), fr₁ _ (by omega)]; exact r35) ha
        (by rw [j3 _ (by omega) (by omega)]; exact s38)
        (by rw [j3 _ (by omega) (by omega)]; exact s39) (by omega) (by omega)
      refine ⟨c'', t, ex, by omega, h40, by rw [hn _ (by omega) (by omega)]; exact hb,
        fun x hx => ?_, fun a h => ?_, fun r h1 h2 => by rw [hn r h1 h2]; exact j3 r h1 h2,
        by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩
      · rw [hm, upd_apply]
        split_ifs with he
        · rfl
        · exact j1 x (by omega)
      · rw [hm, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact j2 a (by omega))
  obtain ⟨c₃, t₃, e₃, ht₃, h40₃, hn₃, hm₃, hr₃, hrm₃, ho₃⟩ : ∃ c₃ t₃,
      Exec P W (block [.constN 2940 0]) c₂ c₃ t₃ ∧ t₃ = 1 ∧ c₃.nreg 2940 = 0 ∧
      (∀ r, r ≠ 2940 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  -- registers of `c₁` kept off the loop registers
  have Q3 : ∀ r, (r < 2940 ∨ 2946 < r) → c₃.nreg r = c₁.nreg r := fun r hr => by
    rw [hn₃ r (by omega), z3 r (by omega) (by omega)]
  have q30 : c₁.nreg 2930 = s := by rw [fr₁ _ (by omega)]; exact r30
  have q34 : c₁.nreg 2934 = Ob := by rw [fr₁ _ (by omega)]; exact r34
  have q35 : c₁.nreg 2935 = Xb := by rw [fr₁ _ (by omega)]; exact r35
  have q36 : c₁.nreg 2936 = Yb := by rw [fr₁ _ (by omega)]; exact r36
  have q32 : c₁.nreg 2932 = m := by rw [fr₁ _ (by omega)]; exact r32
  -- the first pass
  let JA : ℕ → Config → Prop := fun i c' =>
    LArr Xb Yb k (oldA s i SD) c' ∧ MOut Xb Yb k c c' ∧
      (∀ r, (r < 2940 ∨ 2946 < r) → c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  have JA0 : JA 0 c₃ := by
    refine ⟨⟨fun x hx => ?_, fun j hj => ?_, ?_⟩, fun a h1 h2 => ?_, Q3, by rw [hr₃, zr],
      by rw [hrm₃, zrm], by rw [ho₃, zo]⟩
    · rw [hm₃, z1 x hx]; simp [oldA, NIv]
    · simp [oldA] at hj
    · rw [hn₃ _ (by omega), z3 _ (by omega) (by omega), s41]; simp [oldA]
    · rw [hm₃]; exact z2 a h1
  obtain ⟨c₄, t₄, e₄, ht₄, hw₄, a1, a2, a3, ar, arm, ao⟩ := forLoop_exec (P := P) (a := 2940)
    (bR := 2932) (body := ciA) JA (K := 13) (n := m) c₃ e₃.wb_right h40₃
    (by rw [Q3 _ (by omega), q32]) JA0
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j3, jr, jrm, jo⟩ := hJ
      have hlen : (oldA s i SD).length ≤ i :=
        length_le_of_lt (oldA_nodup s i SD) fun x hx => oldA_lt hx
      have eSD : c'.nmem (Ob + i) = SD i := j2 _ (by omega) (by omega)
      obtain ⟨c'', t, ex, ht, hm, h41, h40, hn, hr, hrm, ho⟩ := ciA_exec (P := P) (s := s)
        (Ob := Ob) (Xb := Xb) (Yb := Yb) (i := i) (len := (oldA s i SD).length) c' hw
        (by rw [j3 _ (by omega), q30]) (by rw [j3 _ (by omega), q34])
        (by rw [j3 _ (by omega), q35]) (by rw [j3 _ (by omega), q36])
        (by rw [j3 _ (by omega), s39]) ha j1.len (by omega) (by omega) (by omega) (by omega)
        (by omega)
      rw [eSD] at hm h41
      have hb' : c''.nreg 2932 = m := by
        rw [hn _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hb
      refine ⟨c'', t, ex, ht, h40, hb', ?_, fun a h1 h2 => ?_, fun r hr' => ?_, by rw [hr, jr],
        by rw [hrm, jrm], by rw [ho, jo]⟩
      · rw [oldA_succ]
        by_cases e : SD i = s
        · rw [ite_eq_left_of_eq_true _ _ (eq_true e)] at hm h41 ⊢
          exact j1.snoc (fun h => by have := oldA_lt h; omega) (by omega) (by omega) dXY hm h41
        · rw [ite_eq_right_of_eq_false _ _ (eq_false e)] at hm h41 ⊢
          rw [List.append_nil]
          exact j1.congr hm (by rw [h41]; exact j1.len.symm)
      · rw [hm]
        split_ifs
        · rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), upd_apply,
            ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
          exact j2 a h1 h2
        · exact j2 a h1 h2
      · rw [hn r (by omega) (by omega) (by omega) (by omega) (by omega)]; exact j3 r hr')
  obtain ⟨c₅, t₅, e₅, ht₅, h50, h40₅, hn₅, hm₅, hr₅, hrm₅, ho₅⟩ : ∃ c₅ t₅,
      Exec P W (block [.copyN 2950 2941, .constN 2940 0]) c₄ c₅ t₅ ∧ t₅ = 2 ∧
      c₅.nreg 2950 = c₄.nreg 2941 ∧ c₅.nreg 2940 = 0 ∧
      (∀ r, r ≠ 2940 → r ≠ 2950 → c₅.nreg r = c₄.nreg r) ∧ c₅.nmem = c₄.nmem ∧
      c₅.rreg = c₄.rreg ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  -- the second pass
  set A0 := oldA s m SD with hA0
  have hA0m : ∀ x ∈ A0, x < m := fun x hx => oldA_lt hx
  have hA0nd : A0.Nodup := oldA_nodup s m SD
  have hlenA : A0.length ≤ m := length_le_of_lt hA0nd hA0m
  have q53 : c₁.nreg 2953 = d + 4 + k := s53
  let LB : ℕ → List ℕ := fun i => apnd A0 ((A0.take i).map AL)
  have LBlt : ∀ i, ∀ x ∈ LB i, x < k := fun i x hx => by
    rcases apnd_mem _ _ x hx with h | h
    · have := hA0m x h; omega
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
      have := hA0m y (List.mem_of_mem_take hy)
      exact hAL y (by omega)
  have LBnd : ∀ i, (LB i).Nodup := fun i => apnd_nodup _ _ hA0nd
  have LBpre : ∀ i, A0 <+: LB i := fun i => apnd_prefix _ _
  let JB : ℕ → Config → Prop := fun i c' =>
    LArr Xb Yb k (LB i) c' ∧ MOut Xb Yb k c c' ∧
      (∀ r, (r < 2940 ∨ 2946 < r) → c'.nreg r = c₅.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  have JB0 : JB 0 c₅ := by
    refine ⟨?_, fun a h1 h2 => by rw [hm₅]; exact a2 a h1 h2, fun _ _ => rfl,
      by rw [hr₅, ar], by rw [hrm₅, arm], by rw [ho₅, ao]⟩
    have e : LB 0 = A0 := by simp [LB, apnd]
    rw [e]
    exact a1.congr hm₅ (hn₅ _ (by omega) (by omega))
  have Q5 : ∀ r, (r < 2940 ∨ 2946 < r) → r ≠ 2950 → c₅.nreg r = c₁.nreg r := fun r hr h =>
    by rw [hn₅ r (by omega) h, a3 r hr]
  obtain ⟨c₆, t₆, e₆, ht₆, hw₆, b1, b2, b3, br, brm, bo⟩ := forLoop_exec (P := P) (a := 2940)
    (bR := 2950) (body := ciB) JB (K := 15) (n := A0.length) c₅ e₅.wb_right h40₅
    (by rw [h50, a1.len]) JB0
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j3, jr, jrm, jo⟩ := hJ
      have hiL : i < (LB i).length := lt_of_lt_of_le hi (LBpre i).length_le
      have eOLD : c'.nmem (Yb + i) = A0[i] := by
        rw [j1.old i hiL, List.getD_eq_getElem _ _ hiL]
        exact ((LBpre i).getElem hi).symm
      have hh : A0[i] < m := hA0m _ (List.getElem_mem hi)
      have eA : c'.nmem (d + 4 + k + A0[i]) = AL A0[i] := j2 _ (by omega) (by omega)
      have ha_lt : AL A0[i] < k := hAL _ (by omega)
      have eNI : c'.nmem (Xb + AL A0[i]) = NIv (LB i) (AL A0[i]) := j1.ni _ ha_lt
      have hlk : (LB i).length ≤ k := length_le_of_lt (LBnd i) (LBlt i)
      obtain ⟨c'', t, ex, ht, hm, h41, h40, hn, hr, hrm, ho⟩ := ciB_exec (P := P)
        (Ab := d + 4 + k) (Xb := Xb) (Yb := Yb) (i := i) (len := (LB i).length) c' hw
        (by rw [j3 _ (by omega), Q5 _ (by omega) (by omega), q53])
        (by rw [j3 _ (by omega), Q5 _ (by omega) (by omega), q35])
        (by rw [j3 _ (by omega), Q5 _ (by omega) (by omega), q36])
        (by rw [j3 _ (by omega), Q5 _ (by omega) (by omega), s39]) ha j1.len (by omega)
        (by rw [eOLD]; omega) (by rw [eOLD, eA]; omega) (by omega) (by omega) (by omega)
      simp only [eOLD, eA, eNI] at hm h41
      have hb' : c''.nreg 2950 = A0.length := by
        rw [hn _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact hb
      have eL : LB (i + 1) = if AL A0[i] ∈ LB i then LB i else LB i ++ [AL A0[i]] := by
        simp only [LB]
        rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.map_append,
          List.map_singleton, apnd_snoc]
      have hlt_of : NIv (LB i) (AL A0[i]) < 1 → (LB i).length < k := fun h0 => by
        have e : AL A0[i] ∉ LB i := fun h' => by have := NIv_pos_iff.2 h'; omega
        have := length_le_of_lt (L := LB i ++ [AL A0[i]]) (k := k) (by
          rw [List.nodup_append]
          exact ⟨LBnd i, List.nodup_singleton _, fun a ha b hb e' => by
            rw [List.mem_singleton] at hb; subst hb; subst e'; exact e ha⟩) (fun x hx => by
          rcases List.mem_append.1 hx with hx | hx
          · exact LBlt i x hx
          · rw [List.mem_singleton] at hx; subst hx; exact ha_lt)
        rw [List.length_append, List.length_singleton] at this; omega
      refine ⟨c'', t, ex, by omega, h40, hb', ?_, fun a h1 h2 => ?_, fun r hr' => ?_,
        by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩
      · rw [eL]
        by_cases e : AL A0[i] ∈ LB i
        · have : ¬ NIv (LB i) (AL A0[i]) < 1 := by have := NIv_pos_iff.2 e; omega
          rw [ite_eq_left_of_eq_true _ _ (eq_true e)]
          rw [ite_eq_right_of_eq_false _ _ (eq_false this)] at hm h41
          exact j1.congr hm (by rw [h41]; exact j1.len.symm)
        · have : NIv (LB i) (AL A0[i]) < 1 := by
            have := mt NIv_pos_iff.1 e; omega
          rw [ite_eq_right_of_eq_false _ _ (eq_false e)]
          rw [ite_eq_left_of_eq_true _ _ (eq_true this)] at hm h41
          exact j1.snoc e ha_lt (hlt_of this) dXY hm h41
      · rw [hm]
        split_ifs with h0
        · have := hlt_of h0
          rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), upd_apply,
            ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
          exact j2 a h1 h2
        · exact j2 a h1 h2
      · rw [hn r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact j3 r hr')
  obtain ⟨c₇, t₇, e₇, ht₇, h51, hn₇, hm₇, hr₇, hrm₇, ho₇⟩ : ∃ c₇ t₇,
      Exec P W (block [.copyN 2951 2941]) c₆ c₇ t₇ ∧ t₇ = 1 ∧
      c₇.nreg 2951 = c₆.nreg 2941 ∧ (∀ r, r ≠ 2951 → c₇.nreg r = c₆.nreg r) ∧
      c₇.nmem = c₆.nmem ∧ c₇.rreg = c₆.rreg ∧ c₇.rmem = c₆.rmem ∧ c₇.output = c₆.output := by
    exec_block
    refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  have eLB : LB A0.length = ciL s m SD AL := by
    show apnd A0 ((A0.take A0.length).map AL) = _
    rw [List.take_length]; rfl
  rw [eLB] at b1
  have R7 : ∀ r, (r < 2940 ∨ 2946 < r) → r ≠ 2950 → r ≠ 2951 → c₇.nreg r = c₁.nreg r :=
    fun r h1 h2 h3 => by rw [hn₇ r h3, b3 r h1, Q5 r h1 h2]
  refine ⟨c₇, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + t₇))))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄
    (.seq e₅ (.seq e₆ e₇))))), by omega, ?_, by rw [h51, b1.len], b1.congr hm₇ (by
      rw [hn₇ _ (by omega)]), by rw [R7 _ (by omega) (by omega) (by omega)]; exact s38,
    by rw [R7 _ (by omega) (by omega) (by omega)]; exact s39,
    by rw [R7 _ (by omega) (by omega) (by omega)]; exact s52,
    by rw [R7 _ (by omega) (by omega) (by omega)]; exact s53,
    by rw [R7 _ (by omega) (by omega) (by omega)]; exact s54,
    by rw [R7 _ (by omega) (by omega) (by omega)]; exact s55,
    by rw [R7 _ (by omega) (by omega) (by omega)]; exact s56,
    by rw [R7 _ (by omega) (by omega) (by omega)]; exact s57,
    fun a h1 h2 => by rw [hm₇]; exact b2 a h1 h2, fun r hr => ?_, by rw [hr₇, br],
    by rw [hrm₇, brm], by rw [ho₇, bo]⟩
  · rw [hn₇ _ (by omega), b3 _ (by omega), h50, a1.len]
  · rw [R7 r (by omega) (by omega) (by omega), fr₁ r (by omega)]

end Frame

end NegSSSP

end PlanarFlow
