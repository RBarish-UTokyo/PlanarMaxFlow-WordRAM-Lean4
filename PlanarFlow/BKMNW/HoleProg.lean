module

public import PlanarFlow.BKMNW.PrepProg
public import PlanarSeparator.Machine.Frame

/-!
# The hole choice of `scChoiceE` on the machine: a loop over the holes

`scChoiceE.hole N` is the first hole of the list `Hs` that is a cut vertex of `N`
(`List.find?` of `CutH`), and `NoCut M N Hs` holds iff there is none. On the machine: a loop over
`j < |Hs|`; while no cut hole is found, the hole test `phCut` of `Hs[j]` (`J1 = j + 1`), and on a
positive test `found := 1`, `J := j`.

* pure: `find?_getD`, `find?_none_getD`, `HlInv` (the loop invariant), `hlInv_find?`;
* `hlTest`, `hlBody`, **`hlProg`** (registers `4874 = |Hs|`; written `4845`, `4870 … 4873`,
  `4875`; the flag in `4871`, the hole index in `4872`), `hlTest_exec`;
* **`hlProg_exec`**: within `|Hs| · (160 n + 36) + 7` steps, `Hs.find? (CutH …) = none` and
  `r4871 = 0`, or `r4871 = 1`, `r4872 < |Hs|` and `Hs.find? (CutH …) = some Hs[r4872]`;
  **`hlProg_hole`** (the same for `(scChoiceE …).hole N` and `NoCut M N Hs ↔ r4871 = 0`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Relation WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The first element, purely -/

lemma find?_getD {α : Type*} (d : α) (q : α → Bool) :
    ∀ (l : List α) (J : ℕ), J < l.length → q (l.getD J d) = true →
      (∀ j < J, q (l.getD j d) = false) → l.find? q = some (l.getD J d)
  | [], J, h, _, _ => absurd h (by simp)
  | a :: l, 0, _, hq, _ => by simp only [List.getD_cons_zero] at hq ⊢; simp [List.find?_cons, hq]
  | a :: l, J + 1, h, hq, hj => by
    have h0 := hj 0 (by omega)
    simp only [List.getD_cons_zero] at h0
    simp only [List.getD_cons_succ] at hq ⊢
    rw [List.find?_cons, h0]
    exact find?_getD d q l J (by simp at h; omega) hq
      (fun j hj' => by simpa using hj (j + 1) (by omega))

lemma find?_none_getD {α : Type*} (d : α) (q : α → Bool) (l : List α)
    (h : ∀ j < l.length, q (l.getD j d) = false) : l.find? q = none := by
  rw [List.find?_eq_none]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
  have := h j hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this
  simp [this]

/-- The invariant of the loop after the holes `< i`: no test positive and `f = 0`, or `f = 1`
and `J < i` is the first positive test. -/
def HlInv (p : ℕ → Prop) (i f J : ℕ) : Prop :=
  (f = 0 ∧ ∀ j < i, ¬ p j) ∨ (f = 1 ∧ J < i ∧ p J ∧ ∀ j < J, ¬ p j)

lemma hlInv_zero (p : ℕ → Prop) (J : ℕ) : HlInv p 0 0 J := Or.inl ⟨rfl, fun j hj => absurd hj (by omega)⟩

lemma hlInv_skip {p : ℕ → Prop} {i J : ℕ} (h : HlInv p i 1 J) : HlInv p (i + 1) 1 J := by
  rcases h with ⟨h, -⟩ | ⟨-, h1, h2, h3⟩
  · omega
  · exact Or.inr ⟨rfl, by omega, h2, h3⟩

lemma hlInv_found {p : ℕ → Prop} {i J : ℕ} (h : HlInv p i 0 J) (hp : p i) :
    HlInv p (i + 1) 1 i := by
  rcases h with ⟨-, h⟩ | ⟨h, -⟩
  · exact Or.inr ⟨rfl, by omega, hp, h⟩
  · omega

lemma hlInv_not {p : ℕ → Prop} {i J : ℕ} (h : HlInv p i 0 J) (hp : ¬ p i) :
    HlInv p (i + 1) 0 J := by
  rcases h with ⟨-, h⟩ | ⟨h, -⟩
  · refine Or.inl ⟨rfl, fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact h j hj
    · exact hp
  · omega

/-- **The invariant at the end is `List.find?`.** -/
lemma hlInv_find? {α : Type*} (d : α) (q : α → Bool) (l : List α) {f J : ℕ}
    (h : HlInv (fun j => q (l.getD j d) = true) l.length f J) :
    (f = 0 ∧ l.find? q = none) ∨ (f = 1 ∧ J < l.length ∧ l.find? q = some (l.getD J d)) := by
  rcases h with ⟨h0, h⟩ | ⟨h1, h2, h3, h4⟩
  · exact Or.inl ⟨h0, find?_none_getD d q l fun j hj => by simpa using h j hj⟩
  · exact Or.inr ⟨h1, h2, find?_getD d q l J h2 h3 fun j hj => by simpa using h4 j hj⟩

/-! ### The program -/

/-- The test of hole `j = r4870` (`4873 = 1`, `4875 = 0`): `J1 := j + 1`, `phCut`, record. -/
def hlTest : Stmt :=
  .seq (block [.addN 4845 4870 4873])
    (.seq phCut (.ifLtN 4875 4767 (block [.copyN 4871 4873, .copyN 4872 4870]) .skip))

/-- One hole: the test while none is found, then `j := j + 1`. -/
def hlBody : Stmt := .seq (.ifLtN 4871 4873 hlTest .skip) (block [.addN 4870 4870 4873])

/-- **The hole choice.** -/
def hlProg : Stmt :=
  .seq (block [.constN 4870 0, .constN 4871 0, .constN 4872 0, .constN 4873 1, .constN 4875 0])
    (.whileLtN 4870 4874 hlBody)

/-- The registers kept by the loop. -/
def HlFr (x : ℕ) : Prop :=
  x < 4405 ∨ (4416 < x ∧ x < 4427) ∨ (4436 < x ∧ x < 4763) ∨ (4771 < x ∧ x < 4845) ∨
    (4845 < x ∧ x < 4853) ∨ (4865 < x ∧ x < 4870) ∨ 4872 < x

/-- The registers `4417 … 4426` (inputs of `ccProg`) are not written by the hole test. -/
lemma phCut_wr_mid : ∀ k < 10, phCut.wr (4417 + k) = false := by decide

section Exec

variable {P : Input} {W : ℕ}
variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

theorem hlInc_exec (c : Config) (hc : WordsBounded W c) {i : ℕ} (v0 : c.nreg 4870 = i)
    (v3 : c.nreg 4873 = 1) (hw : i + 1 ≤ W) :
    ∃ c' k, Exec P W (block [.addN 4870 4870 4873]) c c' k ∧ k = 1 ∧ c'.nreg 4870 = i + 1 ∧
      (∀ x, x ≠ 4870 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  all_goals try (config_simp; simp only [v0, v3]; omega)
  refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [v0, v3]
  · simp only [Config.nreg_mk, upd_other _ _ _ h1]

/-- **The test of one hole.** -/
theorem hlTest_exec {B N : Finset D} {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint)
    {e : ℕ → D} {n NFb THb RV0b GNb RVb TKb YFb LSb OFFb ADJb LABb Qb j : ℕ}
    (hj : j < Hs.length) (hmem : ∀ i < n, e i ∈ B)
    (hsurj : ∀ d ∈ B, ∃ i < n, e i = d) (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j)
    (hsub : N ⊆ B) (c : Config) (hc : WordsBounded W c)
    (hL : CgLay n n RVb TKb YFb LSb OFFb ADJb) (hB : BfLay n (3 * n) OFFb ADJb LABb Qb W)
    (hGN : GNb + n ≤ RVb) (hin : NFb + n ≤ GNb ∧ THb + n ≤ GNb ∧ RV0b + n ≤ GNb)
    (hW : 2 * n + 2 ≤ W) (hjW : Hs.length + 1 ≤ W)
    (hrv0 : ∀ i < n, c.nmem (RV0b + i) < n ∧ e (c.nmem (RV0b + i)) = M.rev (e i))
    (hnf : ∀ i < n, (c.nmem (NFb + i) ≠ 0 ↔ e i ∈ N))
    (hth : ∀ i < n, (c.nmem (THb + i) = j + 1 ↔ M.tail (e i) ∈ Hs.getD j ∅))
    (hTK : ∀ i < n, c.nmem (TKb + i) < n)
    (hkey : ∀ i < n, ∀ j < n, (c.nmem (TKb + i) = c.nmem (TKb + j) ↔
      HRel Hs (M.tail (e i)) (M.tail (e j))))
    (p0 : c.nreg 4840 = n) (p1 : c.nreg 4841 = NFb) (p2 : c.nreg 4842 = THb)
    (p3 : c.nreg 4843 = RV0b) (p6 : c.nreg 4846 = YFb)
    (p7 : c.nreg 4847 = GNb) (p8 : c.nreg 4848 = RVb) (p9 : c.nreg 4849 = LABb)
    (p10 : c.nreg 4866 = LSb)
    (r0 : c.nreg 4420 = n) (r1 : c.nreg 4421 = RVb) (r2 : c.nreg 4422 = TKb)
    (r3 : c.nreg 4423 = YFb) (r4 : c.nreg 4424 = LSb) (r5 : c.nreg 4425 = OFFb)
    (r6 : c.nreg 4426 = ADJb) (s0 : c.nreg 4400 = n) (s1 : c.nreg 4401 = OFFb)
    (s2 : c.nreg 4402 = ADJb) (s3 : c.nreg 4403 = LABb) (s4 : c.nreg 4404 = Qb)
    (u0 : c.nreg 4760 = n) (u1 : c.nreg 4761 = GNb) (u2 : c.nreg 4762 = LABb)
    (v0 : c.nreg 4870 = j) (v3 : c.nreg 4873 = 1) (v5 : c.nreg 4875 = 0) :
    ∃ c' k, Exec P W hlTest c c' k ∧ k ≤ 160 * n + 32 ∧
      (CutH M N Hs (Hs.getD j ∅) → c'.nreg 4871 = 1 ∧ c'.nreg 4872 = j) ∧
      (¬ CutH M N Hs (Hs.getD j ∅) → c'.nreg 4871 = c.nreg 4871 ∧ c'.nreg 4872 = c.nreg 4872) ∧
      c'.nreg 4870 = j ∧ (∀ a, (a < GNb ∨ (TKb ≤ a ∧ a < TKb + n) ∨ Qb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, HlFr x → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hg : Hs.getD j ∅ ∈ Hs := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    exact List.getElem_mem hj
  obtain ⟨c₁, k₁, e₁, hk₁, g45, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.addN 4845 4870 4873]) c c₁ k₁ ∧ k₁ = 1 ∧ c₁.nreg 4845 = j + 1 ∧
      (∀ x, x ≠ 4845 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try (config_simp; simp only [v0, v3]; omega)
    refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [v0, v3]
    · simp only [Config.nreg_mk, upd_other _ _ _ h1]
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 4845 → c₁.nreg x = c.nreg x := gn₁
  obtain ⟨c₂, k₂, e₂, hk₂, G1, G2, G3, G4, G5, G6⟩ := phCut_cutH (P := P) (M := M) (B := B)
    (N := N) hd hg hmem hsurj hinj hsub c₁ hw₁ hL hB hGN hin hW
    (fun i hi => by rw [gm₁]; exact hrv0 i hi) (fun i hi => by rw [gm₁]; exact hnf i hi)
    (fun i hi => by rw [gm₁]; exact hth i hi) (fun i hi => by rw [gm₁]; exact hTK i hi)
    (fun i hi j hj => by rw [gm₁]; exact hkey i hi j hj)
    (by rw [q _ (by omega), p0]) (by rw [q _ (by omega), p1]) (by rw [q _ (by omega), p2])
    (by rw [q _ (by omega), p3]) g45 (by rw [q _ (by omega), p6]) (by rw [q _ (by omega), p7])
    (by rw [q _ (by omega), p8]) (by rw [q _ (by omega), p9]) (by rw [q _ (by omega), p10])
    (by rw [q _ (by omega), r0]) (by rw [q _ (by omega), r1]) (by rw [q _ (by omega), r2])
    (by rw [q _ (by omega), r3]) (by rw [q _ (by omega), r4]) (by rw [q _ (by omega), r5])
    (by rw [q _ (by omega), r6]) (by rw [q _ (by omega), s0]) (by rw [q _ (by omega), s1])
    (by rw [q _ (by omega), s2]) (by rw [q _ (by omega), s3]) (by rw [q _ (by omega), s4])
    (by rw [q _ (by omega), u0]) (by rw [q _ (by omega), u1]) (by rw [q _ (by omega), u2])
  have hw₂ := e₂.wb_right
  have q2 : ∀ x, HlFr x → c₂.nreg x = c.nreg x := fun x hx => by
    unfold HlFr at hx
    by_cases hm : 4416 < x ∧ x < 4427
    · obtain ⟨k, hk, rfl⟩ : ∃ k < 10, x = 4417 + k := ⟨x - 4417, by omega, by omega⟩
      rw [e₂.nreg_of_wr (phCut_wr_mid k hk), q _ (by omega)]
    · rw [G3 x (by omega), q x (by omega)]
  have h70 : c₂.nreg 4870 = j := by rw [G3 _ (by omega), q _ (by omega), v0]
  have h73 : c₂.nreg 4873 = 1 := by rw [q2 _ (by unfold HlFr; omega), v3]
  have h75 : c₂.nreg 4875 = 0 := by rw [q2 _ (by unfold HlFr; omega), v5]
  have h71 : c₂.nreg 4871 = c.nreg 4871 := by
    rw [G3 _ (by omega), q _ (by omega)]
  have h72 : c₂.nreg 4872 = c.nreg 4872 := by
    rw [G3 _ (by omega), q _ (by omega)]
  have fr : ∀ a, (a < GNb ∨ (TKb ≤ a ∧ a < TKb + n) ∨ Qb + n ≤ a) → c₂.nmem a = c.nmem a :=
    fun a ha => by rw [G2 a ha, gm₁]
  by_cases hcut : CutH M N Hs (Hs.getD j ∅)
  · have hlt : c₂.nreg 4875 < c₂.nreg 4767 := by
      rw [h75]; exact Nat.pos_of_ne_zero (G1.2 hcut)
    obtain ⟨c₃, k₃, e₃, hk₃, b71, b72, bn, bm, br, brm, bo⟩ : ∃ c₃ k₃,
        Exec P W (block [.copyN 4871 4873, .copyN 4872 4870]) c₂ c₃ k₃ ∧ k₃ = 2 ∧
        c₃.nreg 4871 = 1 ∧ c₃.nreg 4872 = j ∧
        (∀ x, x ≠ 4871 → x ≠ 4872 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧
        c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
      exec_block
      refine ⟨rfl, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; exact h73
      · config_simp; exact h70
      · simp only [Config.nreg_mk, upd_other _ _ _ h1, upd_other _ _ _ h2]
    refine ⟨c₃, k₁ + (k₂ + (k₃ + 1)), .seq e₁ (.seq e₂ (.ifLtN_true hlt e₃)), by omega,
      fun _ => ⟨b71, b72⟩, fun h => absurd hcut h, by rw [bn _ (by omega) (by omega), h70],
      fun a ha => by rw [bm, fr a ha],
      fun x hx => ?_, by rw [br, G4, gr₁], by rw [brm, G5, grm₁], by rw [bo, G6, go₁]⟩
    unfold HlFr at hx
    rw [bn x (by omega) (by omega), q2 x hx]
  · have hnlt : ¬ c₂.nreg 4875 < c₂.nreg 4767 := by
      rw [h75]; intro h; exact hcut (G1.1 (by omega))
    refine ⟨c₂, k₁ + (k₂ + (0 + 2)), .seq e₁ (.seq e₂ (.ifLtN_false hnlt (.skip hw₂))),
      by omega, fun h => absurd h hcut, fun _ => ⟨h71, h72⟩, h70, fr, q2,
      by rw [G4, gr₁], by rw [G5, grm₁], by rw [G6, go₁]⟩

open Classical in
/-- **The hole choice on the machine**: within `|Hs| · (160 n + 36) + 7` steps, either `r4871 = 0`
and no hole of the list is a cut vertex (`find? = none`), or `r4871 = 1`, `r4872 < |Hs|` and
`Hs[r4872]` is the first cut-vertex hole of the list. -/
theorem hlProg_exec {B N : Finset D} {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint)
    {e : ℕ → D} {n NFb THb RV0b GNb RVb TKb YFb LSb OFFb ADJb LABb Qb : ℕ}
    (hmem : ∀ i < n, e i ∈ B)
    (hsurj : ∀ d ∈ B, ∃ i < n, e i = d) (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j)
    (hsub : N ⊆ B) (c : Config) (hc : WordsBounded W c)
    (hL : CgLay n n RVb TKb YFb LSb OFFb ADJb) (hB : BfLay n (3 * n) OFFb ADJb LABb Qb W)
    (hGN : GNb + n ≤ RVb) (hin : NFb + n ≤ GNb ∧ THb + n ≤ GNb ∧ RV0b + n ≤ GNb)
    (hW : 2 * n + 2 ≤ W) (hjW : Hs.length + 1 ≤ W)
    (hrv0 : ∀ i < n, c.nmem (RV0b + i) < n ∧ e (c.nmem (RV0b + i)) = M.rev (e i))
    (hnf : ∀ i < n, (c.nmem (NFb + i) ≠ 0 ↔ e i ∈ N))
    (hth : ∀ i < n, ∀ j < Hs.length, (c.nmem (THb + i) = j + 1 ↔ M.tail (e i) ∈ Hs.getD j ∅))
    (hTK : ∀ i < n, c.nmem (TKb + i) < n)
    (hkey : ∀ i < n, ∀ j < n, (c.nmem (TKb + i) = c.nmem (TKb + j) ↔
      HRel Hs (M.tail (e i)) (M.tail (e j))))
    (p0 : c.nreg 4840 = n) (p1 : c.nreg 4841 = NFb) (p2 : c.nreg 4842 = THb)
    (p3 : c.nreg 4843 = RV0b) (p6 : c.nreg 4846 = YFb)
    (p7 : c.nreg 4847 = GNb) (p8 : c.nreg 4848 = RVb) (p9 : c.nreg 4849 = LABb)
    (p10 : c.nreg 4866 = LSb)
    (r0 : c.nreg 4420 = n) (r1 : c.nreg 4421 = RVb) (r2 : c.nreg 4422 = TKb)
    (r3 : c.nreg 4423 = YFb) (r4 : c.nreg 4424 = LSb) (r5 : c.nreg 4425 = OFFb)
    (r6 : c.nreg 4426 = ADJb) (s0 : c.nreg 4400 = n) (s1 : c.nreg 4401 = OFFb)
    (s2 : c.nreg 4402 = ADJb) (s3 : c.nreg 4403 = LABb) (s4 : c.nreg 4404 = Qb)
    (u0 : c.nreg 4760 = n) (u1 : c.nreg 4761 = GNb) (u2 : c.nreg 4762 = LABb)
    (v4 : c.nreg 4874 = Hs.length) :
    ∃ c' k, Exec P W hlProg c c' k ∧ k ≤ Hs.length * (160 * n + 36) + 7 ∧
      ((c'.nreg 4871 = 0 ∧ Hs.find? (fun g => decide (CutH M N Hs g)) = none) ∨
        (c'.nreg 4871 = 1 ∧ c'.nreg 4872 < Hs.length ∧
          Hs.find? (fun g => decide (CutH M N Hs g)) = some (Hs.getD (c'.nreg 4872) ∅))) ∧
      (∀ a, (a < GNb ∨ (TKb ≤ a ∧ a < TKb + n) ∨ Qb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (HlFr x ∧ x ≠ 4873 ∧ x ≠ 4875) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold hlProg
  obtain ⟨c₁, k₁, e₁, hk₁, g70, g71, g72, g73, g75, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 4870 0, .constN 4871 0, .constN 4872 0, .constN 4873 1,
        .constN 4875 0]) c c₁ k₁ ∧ k₁ = 5 ∧
      c₁.nreg 4870 = 0 ∧ c₁.nreg 4871 = 0 ∧ c₁.nreg 4872 = 0 ∧ c₁.nreg 4873 = 1 ∧
      c₁.nreg 4875 = 0 ∧
      (∀ x, x ≠ 4870 → x ≠ 4871 → x ≠ 4872 → x ≠ 4873 → x ≠ 4875 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x h1 h2 h3 h4 h5 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; done)
    simp only [Config.nreg_mk, upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3,
      upd_other _ _ _ h4, upd_other _ _ _ h5]
  have hw₁ := e₁.wb_right
  have q : ∀ x, (HlFr x ∧ x ≠ 4873 ∧ x ≠ 4875) → c₁.nreg x = c.nreg x := fun x ⟨hx, h4, h5⟩ => by
    unfold HlFr at hx
    exact gn₁ x (by omega) (by omega) (by omega) h4 h5
  set m₀ := c.nmem with hm₀
  set pp : ℕ → Prop := fun j => decide (CutH M N Hs (Hs.getD j ∅)) = true with hpp
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, HlFr x → c'.nreg x = c₁.nreg x) ∧
    (∀ a, (a < GNb ∨ (TKb ≤ a ∧ a < TKb + n) ∨ Qb + n ≤ a) → c'.nmem a = m₀ a) ∧
    HlInv pp i (c'.nreg 4871) (c'.nreg 4872) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  have hc1 : ∀ x, HlFr x → x ≠ 4873 → x ≠ 4875 → c₁.nreg x = c.nreg x := fun x hx h1 h2 =>
    q x ⟨hx, h1, h2⟩
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h70, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P)
    (a := 4870) (b := 4874) (body := hlBody) J (B := 160 * n + 34) c₁ hw₁ g70
    (by rw [hc1 _ (by unfold HlFr; omega) (by omega) (by omega), v4]) (Nat.zero_le _)
    ⟨fun _ _ => rfl, fun a _ => by rw [gm₁], by rw [g71]; exact hlInv_zero pp _, rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h70 h74 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, HlFr x → x ≠ 4873 → x ≠ 4875 → c'.nreg x = c.nreg x := fun x hx h1 h2 => by
        rw [j1 x hx, hc1 x hx h1 h2]
      have f73 : c'.nreg 4873 = 1 := by rw [j1 _ (by unfold HlFr; omega), g73]
      have f75 : c'.nreg 4875 = 0 := by rw [j1 _ (by unfold HlFr; omega), g75]
      have fm : ∀ a, (a < GNb ∨ (TKb ≤ a ∧ a < TKb + n) ∨ Qb + n ≤ a) → c'.nmem a = c.nmem a :=
        j2
      obtain ⟨l1, l2, l3, l4, l5⟩ := hL
      obtain ⟨b1, b2, b3, b4⟩ := hB
      obtain ⟨i1, i2, i3⟩ := hin
      have hf : c'.nreg 4871 = 0 ∨ c'.nreg 4871 = 1 := by
        rcases j3 with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
      rcases hf with hf | hf
      · have hlt : c'.nreg 4871 < c'.nreg 4873 := by rw [hf, f73]; omega
        obtain ⟨c₃, k₃, e₃, hk₃, T2, T3, t70, T4, T5, T6, T7, T8⟩ := hlTest_exec (P := P) (M := M)
          (B := B) (N := N) hd (j := i) (by omega) hmem hsurj hinj hsub c' hw
          ⟨l1, l2, l3, l4, l5⟩ ⟨b1, b2, b3, b4⟩ hGN ⟨i1, i2, i3⟩ hW hjW
          (fun k hk => by rw [fm _ (by omega)]; exact hrv0 k hk)
          (fun k hk => by rw [fm _ (by omega)]; exact hnf k hk)
          (fun k hk => by rw [fm _ (by omega)]; exact hth k hk i (by omega))
          (fun k hk => by rw [fm _ (by omega)]; exact hTK k hk)
          (fun k hk l hl => by rw [fm _ (by omega), fm _ (by omega)]; exact hkey k hk l hl)
          (by rw [f _ (by unfold HlFr; omega) (by omega) (by omega), p0])
          (by rw [f _ (by unfold HlFr; omega) (by omega) (by omega), p1])
          (by rw [f _ (by unfold HlFr; omega) (by omega) (by omega), p2])
          (by rw [f _ (by unfold HlFr; omega) (by omega) (by omega), p3])
          (by rw [f _ (by unfold HlFr; omega) (by omega) (by omega), p6])
          (by rw [f _ (by unfold HlFr; omega) (by omega) (by omega), p7])
          (by rw [f _ (by unfold HlFr; omega) (by omega) (by omega), p8])
          (by rw [f _ (by unfold HlFr; omega) (by omega) (by omega), p9])
          (by rw [f _ (by unfold HlFr; omega) (by omega) (by omega), p10])
          (by rw [f _ (by unfold HlFr; omega) (by omega) (by omega), r0])
          (by rw [f _ (by unfold HlFr; omega) (by omega) (by omega), r1])
          (by rw [f _ (by unfold HlFr; omega) (by omega) (by omega), r2])
          (by rw [f _ (by unfold HlFr; omega) (by omega) (by omega), r3])
          (by rw [f _ (by unfold HlFr; omega) (by omega) (by omega), r4])
          (by rw [f _ (by unfold HlFr; omega) (by omega) (by omega), r5])
          (by rw [f _ (by unfold HlFr; omega) (by omega) (by omega), r6])
          (by rw [f _ (by unfold HlFr; omega) (by omega) (by omega), s0])
          (by rw [f _ (by unfold HlFr; omega) (by omega) (by omega), s1])
          (by rw [f _ (by unfold HlFr; omega) (by omega) (by omega), s2])
          (by rw [f _ (by unfold HlFr; omega) (by omega) (by omega), s3])
          (by rw [f _ (by unfold HlFr; omega) (by omega) (by omega), s4])
          (by rw [f _ (by unfold HlFr; omega) (by omega) (by omega), u0])
          (by rw [f _ (by unfold HlFr; omega) (by omega) (by omega), u1])
          (by rw [f _ (by unfold HlFr; omega) (by omega) (by omega), u2])
          h70 f73 f75
        have hw₃ := e₃.wb_right
        have t73 : c₃.nreg 4873 = 1 := by rw [T5 _ (by unfold HlFr; omega)]; exact f73
        obtain ⟨c₄, k₄, e₄, hk₄, a70, an, am, ar, arm, ao⟩ := hlInc_exec (P := P) c₃ hw₃ t70 t73
          (by omega)
        refine ⟨c₄, (k₃ + 1) + k₄, .seq (.ifLtN_true hlt e₃) e₄, by omega, a70,
          by rw [an _ (by omega), T5 _ (by unfold HlFr; omega)]; exact h74,
          fun x hx => ?_, fun a ha => by rw [am, T4 a ha, j2 a ha], ?_,
          by rw [ar, T6, j4], by rw [arm, T7, j5], by rw [ao, T8, j6]⟩
        · have hx' := hx; unfold HlFr at hx'
          rw [an x (by omega), T5 x hx, j1 x hx]
        · rw [an _ (by omega), an _ (by omega)]
          by_cases hcut : CutH M N Hs (Hs.getD i ∅)
          · obtain ⟨a1, a2⟩ := T2 hcut
            rw [a1, a2]
            rw [hf] at j3
            exact hlInv_found j3 (by simp only [hpp, decide_eq_true_eq]; exact hcut)
          · obtain ⟨a1, a2⟩ := T3 hcut
            rw [a1, a2, hf]
            rw [hf] at j3
            exact hlInv_not j3 (by simp only [hpp, decide_eq_true_eq]; exact hcut)
      · have hnlt : ¬ c'.nreg 4871 < c'.nreg 4873 := by rw [hf, f73]; omega
        obtain ⟨c₄, k₄, e₄, hk₄, a70, an, am, ar, arm, ao⟩ := hlInc_exec (P := P) c' hw h70 f73
          (by omega)
        refine ⟨c₄, (0 + 2) + k₄, .seq (.ifLtN_false hnlt (.skip hw)) e₄, by omega, a70,
          by rw [an _ (by omega)]; exact h74, fun x hx => ?_, fun a ha => by rw [am, j2 a ha], ?_,
          by rw [ar, j4], by rw [arm, j5], by rw [ao, j6]⟩
        · have hx' := hx; unfold HlFr at hx'
          rw [an x (by omega), j1 x hx]
        · rw [an _ (by omega), an _ (by omega), hf]
          rw [hf] at j3
          exact hlInv_skip j3)
  have hmul : (160 * n + 34 + 2) * (Hs.length - 0) = Hs.length * (160 * n + 36) := by
    rw [Nat.sub_zero, Nat.mul_comm]
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, ?_, fun a ha => by rw [j2 a ha], fun x hx => ?_,
    by rw [j4, gr₁], by rw [j5, grm₁], by rw [j6, go₁]⟩
  · exact hlInv_find? ∅ (fun g => decide (CutH M N Hs g)) Hs j3
  · rw [j1 x hx.1, q x hx]

end Exec

/-! ### The hole of `scChoiceE` -/

section Hole

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

open Classical in
lemma scChoiceE_hole (sepF : SepFn M) (e : ℕ → D) (n : ℕ) (Hs : List (Finset V)) (A W : ℕ)
    (N : Finset D) :
    (scChoiceE M sepF e n Hs A W).hole N = Hs.find? (fun g => decide (CutH M N Hs g)) := by
  show List.find? _ Hs = _
  congr 1
  funext g
  unfold CutH
  exact decide_eq_decide.2 Iff.rfl

open Classical in
/-- **The result of the hole loop is the hole of `scChoiceE`** (and decides `NoCut`). -/
theorem hl_hole (sepF : SepFn M) (e : ℕ → D) (n : ℕ) {Hs : List (Finset V)} (A W : ℕ)
    {N : Finset D} {f J : ℕ}
    (h : (f = 0 ∧ Hs.find? (fun g => decide (CutH M N Hs g)) = none) ∨
      (f = 1 ∧ J < Hs.length ∧
        Hs.find? (fun g => decide (CutH M N Hs g)) = some (Hs.getD J ∅))) :
    (f = 0 ∧ NoCut M N Hs ∧ (scChoiceE M sepF e n Hs A W).hole N = none) ∨
    (f = 1 ∧ J < Hs.length ∧ ¬ NoCut M N Hs ∧ CutH M N Hs (Hs.getD J ∅) ∧
      (scChoiceE M sepF e n Hs A W).hole N = some (Hs.getD J ∅)) := by
  rw [scChoiceE_hole]
  rcases h with ⟨h0, h⟩ | ⟨h1, h2, h⟩
  · refine Or.inl ⟨h0, noCut_iff.2 fun g hg hc => ?_, h⟩
    rw [List.find?_eq_none] at h
    exact h g hg (by simpa using hc)
  · have hc : CutH M N Hs (Hs.getD J ∅) := by simpa using List.find?_some h
    refine Or.inr ⟨h1, h2, fun hn => noCut_iff.1 hn _ (List.mem_of_find?_eq_some h) hc, hc, h⟩

end Hole

end BKMNW

end PlanarFlow
