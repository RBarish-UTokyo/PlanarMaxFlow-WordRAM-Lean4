module

public import PlanarFlow.BKMNW.ItemsD

/-!
# `pruneI` on the machine: one fill of labels

`pruneI Hs N K a₀ ρ I` (the items of a pruned certificate) is, on label arrays, the fill of the
indices of `N \ K` with one label (`pruneI_rep`). Here the program:

* `prSel` (the label `v = L` if the test flag `bt ≠ 0` or `lab i₀ = 0`, else `lab i₀`),
  `flBody`, **`prProg`** (registers `4500 = s`, `4501 = IXb`, `4502 = LABb`, `4503 = L`,
  `4504 = i₀`, `4505 = bt`; written `4506 … 4511`; the indices of `N \ K` at `IX[j]`, `j < s`);
* **`prProg_exec`**: within `7 s + 14` steps `LAB[i] = fillL S v lab i` (`S = {IX[j] | j < s}`),
  memory outside `LAB` kept;
* **`prProg_pruneI`**: with `ItemRep e n I lab` and the hypotheses of `pruneI_rep`, the labels
  after `prProg` represent `pruneI Hs N K (e i₀) ρ I`.

The cost is `O(|N \ K|)` (the indices of the pruned darts are given as a list), not `O(n)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- The label of the fill: `L` if `bt ≠ 0` or `LAB[i₀] = 0`, else `LAB[i₀]` (in `r4506`). -/
def prSel : Stmt :=
  .seq (block [.constN 4508 0, .addN 4510 4502 4504, .loadN 4506 4510])
    (.ifLtN 4508 4505 (block [.copyN 4506 4503])
      (.ifLtN 4508 4506 .skip (block [.copyN 4506 4503])))

/-- `LAB[IX[j]] := v`. -/
def flBody : Stmt :=
  block [.addN 4510 4501 4509, .loadN 4510 4510, .addN 4510 4502 4510, .storeN 4510 4506,
    .addN 4509 4509 4507]

/-- **The prune of the items on labels.** -/
def prProg : Stmt :=
  .seq prSel (.seq (block [.constN 4507 1, .constN 4509 0]) (.whileLtN 4509 4500 flBody))

/-- The items of a label array depend only on the labels below `n`. -/
lemma labItems_congr {D : Type*} [DecidableEq D] {e : ℕ → D} {n : ℕ} {lab lab' : ℕ → ℕ}
    (h : ∀ i < n, lab i = lab' i) : labItems e n lab = labItems e n lab' := by
  have hc : ∀ l, clsL e n lab l = clsL e n lab' l := fun l => by
    ext d; simp only [mem_clsL]
    exact ⟨fun ⟨j, hj, a, b⟩ => ⟨j, hj, (h j hj) ▸ a, b⟩,
      fun ⟨j, hj, a, b⟩ => ⟨j, hj, (h j hj).symm ▸ a, b⟩⟩
  ext X
  simp only [mem_labItems]
  exact ⟨fun ⟨i, hi, a, b⟩ => ⟨i, hi, (h i hi) ▸ a, by rw [b, hc, h i hi]⟩,
    fun ⟨i, hi, a, b⟩ => ⟨i, hi, (h i hi).symm ▸ a, by rw [b, ← hc, h i hi]⟩⟩

/-- The memory after the fill of the first `j` indices. -/
def flMem (m : ℕ → ℕ) (IXb LABb v j : ℕ) (a : ℕ) : ℕ :=
  if ∃ j' < j, a = LABb + m (IXb + j') then v else m a

section Exec

variable {P : Input} {W : ℕ}

theorem prSel_exec (c : Config) (hc : WordsBounded W c) {LABb L i₀ bt : ℕ}
    (r2 : c.nreg 4502 = LABb) (r3 : c.nreg 4503 = L) (r4 : c.nreg 4504 = i₀)
    (r5 : c.nreg 4505 = bt) (w : LABb + i₀ ≤ W) :
    ∃ c' t, Exec P W prSel c c' t ∧ t ≤ 8 ∧
      c'.nreg 4506 = (if bt ≠ 0 ∨ c.nmem (LABb + i₀) = 0 then L else c.nmem (LABb + i₀)) ∧
      c'.nmem = c.nmem ∧
      (∀ x, x ≠ 4506 → x ≠ 4508 → x ≠ 4510 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold prSel
  obtain ⟨c₁, t₁, e₁, ht₁, g6, g8, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ t₁,
      Exec P W (block [.constN 4508 0, .addN 4510 4502 4504, .loadN 4506 4510]) c c₁ t₁ ∧
      t₁ = 3 ∧ c₁.nreg 4506 = c.nmem (LABb + i₀) ∧ c₁.nreg 4508 = 0 ∧
      (∀ x, x ≠ 4506 → x ≠ 4508 → x ≠ 4510 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try (first | omega | (config_simp; simp only [r2, r4]; omega))
    refine ⟨rfl, ?_, ?_, fun x a b d => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [r2, r4]
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 4506 → x ≠ 4508 → x ≠ 4510 → c₁.nreg x = c.nreg x := gn₁
  have k3 : c₁.nreg 4503 = L := by rw [q _ (by omega) (by omega) (by omega), r3]
  have k5 : c₁.nreg 4505 = bt := by rw [q _ (by omega) (by omega) (by omega), r5]
  -- the copy of `L`
  have hcp : ∃ c₂, Exec P W (block [.copyN 4506 4503]) c₁ c₂ 1 ∧ c₂.nreg 4506 = L ∧
      c₂.nmem = c.nmem ∧
      (∀ x, x ≠ 4506 → x ≠ 4508 → x ≠ 4510 → c₂.nreg x = c.nreg x) ∧
      c₂.rreg = c.rreg ∧ c₂.rmem = c.rmem ∧ c₂.output = c.output := by
    obtain ⟨c₂, t₂, e₂, ht₂, h6, gn₂, gm₂, gr₂, grm₂, go₂⟩ : ∃ c₂ t₂,
        Exec P W (block [.copyN 4506 4503]) c₁ c₂ t₂ ∧ t₂ = 1 ∧ c₂.nreg 4506 = L ∧
        (∀ x, x ≠ 4506 → c₂.nreg x = c₁.nreg x) ∧ c₂.nmem = c₁.nmem ∧
        c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
      exec_block
      refine ⟨rfl, ?_, fun x h => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; simp only [k3]
      · config_simp; simp only [upd_apply]; split_ifs <;> omega
    subst ht₂
    exact ⟨c₂, e₂, h6, by rw [gm₂, gm₁], fun x a b d => by rw [gn₂ x a, q x a b d],
      by rw [gr₂, gr₁], by rw [grm₂, grm₁], by rw [go₂, go₁]⟩
  obtain ⟨c₂, e₂, h6, gm₂, gn₂, gr₂, grm₂, go₂⟩ := hcp
  by_cases hb : c₁.nreg 4508 < c₁.nreg 4505
  · have hb' : bt ≠ 0 := by rw [g8, k5] at hb; omega
    refine ⟨c₂, t₁ + (1 + 1), .seq e₁ (.ifLtN_true hb e₂), by omega, by rw [h6, iteT (Or.inl hb')], gm₂, gn₂,
      gr₂, grm₂, go₂⟩
  · have hb' : bt = 0 := by rw [g8, k5] at hb; omega
    by_cases hl : c₁.nreg 4508 < c₁.nreg 4506
    · have hl' : c.nmem (LABb + i₀) ≠ 0 := by rw [g8, g6] at hl; omega
      refine ⟨c₁, t₁ + (0 + 1 + 2), .seq e₁ (.ifLtN_false hb (.ifLtN_true hl (.skip hw₁))), by omega, ?_, gm₁,
        q, gr₁, grm₁, go₁⟩
      rw [g6, iteF (by omega)]
    · have hl' : c.nmem (LABb + i₀) = 0 := by rw [g8, g6] at hl; omega
      refine ⟨c₂, t₁ + (1 + 2 + 2), .seq e₁ (.ifLtN_false hb (.ifLtN_false hl e₂)), by omega, ?_, gm₂, gn₂,
        gr₂, grm₂, go₂⟩
      rw [h6, iteT (Or.inr hl')]

theorem flBody_exec (c : Config) (hc : WordsBounded W c) {IXb LABb v j : ℕ}
    (r1 : c.nreg 4501 = IXb) (r2 : c.nreg 4502 = LABb) (r6 : c.nreg 4506 = v)
    (r7 : c.nreg 4507 = 1) (r9 : c.nreg 4509 = j) (w1 : IXb + j ≤ W)
    (w2 : LABb + c.nmem (IXb + j) ≤ W) (w3 : j + 1 ≤ W) :
    ∃ c' t, Exec P W flBody c c' t ∧ t = 5 ∧ c'.nreg 4509 = j + 1 ∧
      c'.nmem = upd c.nmem (LABb + c.nmem (IXb + j)) v ∧
      (∀ x, x ≠ 4509 → x ≠ 4510 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold flBody
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r6, r7, r9]; omega)
  refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r7, r9]
  · config_simp; simp only [r1, r2, r6, r9]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **The prune on the machine.** With `LAB[i] = lab i` (`i < n`), the indices `IX[j] < n`
(`j < s`) below or above the labels, within `7 s + 14` steps the labels are the fill of
`S = {IX[j] | j < s}` with `v = if bt ≠ 0 ∨ lab i₀ = 0 then L else lab i₀`; the memory outside
`[LABb, LABb + n)` and the registers outside `4506 … 4511` are kept. -/
theorem prProg_exec (c : Config) (hc : WordsBounded W c) {s n IXb LABb L i₀ bt : ℕ}
    (r0 : c.nreg 4500 = s) (r1 : c.nreg 4501 = IXb) (r2 : c.nreg 4502 = LABb)
    (r3 : c.nreg 4503 = L) (r4 : c.nreg 4504 = i₀) (r5 : c.nreg 4505 = bt) (hi₀ : i₀ < n)
    (hIX : ∀ j < s, c.nmem (IXb + j) < n)
    (lay : (IXb + s ≤ LABb ∨ LABb + n ≤ IXb) ∧ LABb + n ≤ W ∧ IXb + s ≤ W ∧ s + 1 ≤ W) :
    ∃ c' t, Exec P W prProg c c' t ∧ t ≤ 7 * s + 14 ∧
      (∀ i < n, c'.nmem (LABb + i) =
        fillL ((range s).image fun j => c.nmem (IXb + j))
          (if bt ≠ 0 ∨ c.nmem (LABb + i₀) = 0 then L else c.nmem (LABb + i₀))
          (fun i => c.nmem (LABb + i)) i) ∧
      (∀ a, (a < LABb ∨ LABb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4506 ∨ 4511 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4⟩ := lay
  unfold prProg
  set v := if bt ≠ 0 ∨ c.nmem (LABb + i₀) = 0 then L else c.nmem (LABb + i₀) with hv
  obtain ⟨c₁, t₁, e₁, ht₁, h6, gm₁, gn₁, gr₁, grm₁, go₁⟩ :=
    prSel_exec (P := P) c hc r2 r3 r4 r5 (by omega)
  have hw₁ := e₁.wb_right
  obtain ⟨c₂, t₂, e₂, ht₂, g7, g9, gn₂, gm₂, gr₂, grm₂, go₂⟩ : ∃ c₂ t₂,
      Exec P W (block [.constN 4507 1, .constN 4509 0]) c₁ c₂ t₂ ∧ t₂ = 2 ∧
      c₂.nreg 4507 = 1 ∧ c₂.nreg 4509 = 0 ∧
      (∀ x, x ≠ 4507 → x ≠ 4509 → c₂.nreg x = c₁.nreg x) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₂ := e₂.wb_right
  have q : ∀ x, (x < 4506 ∨ 4511 < x) → c₂.nreg x = c.nreg x := fun x hx => by
    rw [gn₂ x (by omega) (by omega), gn₁ x (by omega) (by omega) (by omega)]
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun j c' =>
    (∀ x, x ≠ 4509 → x ≠ 4510 → c'.nreg x = c₂.nreg x) ∧
    c'.nmem = flMem m₀ IXb LABb v j ∧
    c'.rreg = c₂.rreg ∧ c'.rmem = c₂.rmem ∧ c'.output = c₂.output
  have hflM0 : flMem m₀ IXb LABb v 0 = m₀ := by
    funext a; simp [flMem]
  obtain ⟨c₃, t₃, e₃, ht₃, hw₃, h09, j1, j2, j3, j4, j5⟩ := tgRange (P := P) (a := 4509)
    (b := 4500) (body := flBody) J (B := 5) c₂ hw₂ g9 (by rw [q _ (by omega), r0])
    (Nat.zero_le s) ⟨fun _ _ _ => rfl, by rw [gm₂, gm₁, hflM0], rfl, rfl, rfl⟩
    (fun j c' hlo hhi hw h09 h00 ⟨j1, j2, j3, j4, j5⟩ => by
      have eIX : c'.nmem (IXb + j) = m₀ (IXb + j) := by
        rw [j2]; unfold flMem
        rw [iteF]
        rintro ⟨j', hj', he⟩
        have := hIX j' (by omega)
        omega
      obtain ⟨c'', t, ex, ht, h09', hm', hn', hr', hrm', ho'⟩ := flBody_exec (P := P) c' hw
        (by rw [j1 _ (by omega) (by omega), q _ (by omega), r1])
        (by rw [j1 _ (by omega) (by omega), q _ (by omega), r2])
        (by rw [j1 _ (by omega) (by omega), gn₂ _ (by omega) (by omega), h6])
        (by rw [j1 _ (by omega) (by omega), g7]) h09 (by omega)
        (by rw [eIX]; have := hIX j hhi; omega) (by omega)
      refine ⟨c'', t, ex, ht.le, h09', by rw [hn' _ (by omega) (by omega)]; exact h00,
        fun x a b => by rw [hn' x a b, j1 x a b], ?_, by rw [hr', j3], by rw [hrm', j4],
        by rw [ho', j5]⟩
      rw [hm', eIX, j2]
      funext a
      unfold flMem
      rw [upd_apply]
      by_cases ha : a = LABb + m₀ (IXb + j)
      · rw [iteT (q := a = LABb + m₀ (IXb + j)) ha,
          iteT (q := ∃ j' < j + 1, a = LABb + m₀ (IXb + j')) ⟨j, by omega, ha⟩]
      · rw [iteF (q := a = LABb + m₀ (IXb + j)) ha]
        by_cases hex : ∃ j' < j, a = LABb + m₀ (IXb + j')
        · rw [iteT (q := ∃ j' < j, a = LABb + m₀ (IXb + j')) hex,
            iteT (q := ∃ j' < j + 1, a = LABb + m₀ (IXb + j'))
              (by obtain ⟨j', hj', h⟩ := hex; exact ⟨j', by omega, h⟩)]
        · rw [iteF (q := ∃ j' < j, a = LABb + m₀ (IXb + j')) hex,
            iteF (q := ∃ j' < j + 1, a = LABb + m₀ (IXb + j'))]
          rintro ⟨j', hj', h⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
          · exact hex ⟨j', hj', h⟩
          · exact ha h)
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, fun i hi => ?_, fun a ha => ?_,
    fun x hx => ?_, by rw [j3, gr₂, gr₁], by rw [j4, grm₂, grm₁], by rw [j5, go₂, go₁]⟩
  · rw [j2]
    unfold flMem fillL
    simp only [mem_image, mem_range]
    have hiff : (∃ j' < s, LABb + i = LABb + m₀ (IXb + j')) ↔
        ∃ a, a < s ∧ m₀ (IXb + a) = i :=
      ⟨fun ⟨j', hj', h⟩ => ⟨j', hj', by omega⟩, fun ⟨j', hj', h⟩ => ⟨j', hj', by omega⟩⟩
    by_cases hex : ∃ a, a < s ∧ m₀ (IXb + a) = i
    · rw [iteT (hiff.2 hex), iteT (q := ∃ a, a < s ∧ m₀ (IXb + a) = i) hex]
    · rw [iteF (fun h => hex (hiff.1 h)), iteF (q := ∃ a, a < s ∧ m₀ (IXb + a) = i) hex]
  · rw [j2]
    unfold flMem
    rw [iteF]
    rintro ⟨j', hj', h⟩
    have := hIX j' hj'
    omega
  · rw [j1 x (by omega) (by omega), q x hx]

/-- **The prune of a certificate on the machine**: the labels after `prProg` represent
`pruneI Hs N K (e i₀) ρ I` (hypotheses of `pruneI_rep`; `bt ≠ 0` the test
`tail (e i₀) ∈ newHole Hs ρ.mverts`, `S = {IX[j]}` the indices of `N \ K`). -/
theorem prProg_pruneI {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {M : CombMap D V F} {e : ℕ → D} {n : ℕ}
    (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j)
    (c : Config) (hc : WordsBounded W c) {s IXb LABb L i₀ bt : ℕ}
    (r0 : c.nreg 4500 = s) (r1 : c.nreg 4501 = IXb) (r2 : c.nreg 4502 = LABb)
    (r3 : c.nreg 4503 = L) (r4 : c.nreg 4504 = i₀) (r5 : c.nreg 4505 = bt) (hi₀ : i₀ < n)
    (hIX : ∀ j < s, c.nmem (IXb + j) < n)
    (lay : (IXb + s ≤ LABb ∨ LABb + n ≤ IXb) ∧ LABb + n ≤ W ∧ IXb + s ≤ W ∧ s + 1 ≤ W)
    {Hs : List (Finset V)} {N K : Finset D} {ρ : HPath M} {I : Finset (Finset D)}
    (hrep : ItemRep e n I fun i => c.nmem (LABb + i))
    (hdisj : ∀ X ∈ I, ∀ Y ∈ I, X ≠ Y → Disjoint X Y) (hIK : ∀ X ∈ I, X ⊆ K)
    (hSN : ((range s).image fun j => c.nmem (IXb + j)).image e = N \ K) (hs : 0 < s)
    (hL : L ≠ 0) (hfresh : ∀ i < n, c.nmem (LABb + i) ≠ L)
    (hb : bt ≠ 0 ↔ M.tail (e i₀) ∈ newHole Hs ρ.mverts) :
    ∃ c' t, Exec P W prProg c c' t ∧ t ≤ 7 * s + 14 ∧
      ItemRep e n (pruneI Hs N K (e i₀) ρ I) (fun i => c'.nmem (LABb + i)) ∧
      (∀ a, (a < LABb ∨ LABb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4506 ∨ 4511 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', t, ex, ht, hlab, hm, hr, hrr, hrm, ho⟩ :=
    prProg_exec (P := P) c hc r0 r1 r2 r3 r4 r5 hi₀ hIX lay
  refine ⟨c', t, ex, ht, ?_, hm, hr, hrr, hrm, ho⟩
  have hS : ((range s).image fun j => c.nmem (IXb + j)) ⊆ range n := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hi
    exact mem_range.2 (hIX j (mem_range.1 hj))
  have hSne : ((range s).image fun j => c.nmem (IXb + j)).Nonempty :=
    ⟨_, mem_image_of_mem _ (mem_range.2 hs)⟩
  have key := pruneI_rep (Hs := Hs) (N := N) (K := K) (ρ := ρ) hinj hrep hdisj hIK hS hSN hSne
    hi₀ hL hfresh (bt ≠ 0) hb
  unfold ItemRep at key ⊢
  rw [key]
  exact labItems_congr fun i hi => (hlab i hi).symm

end Exec

end BKMNW

end PlanarFlow
