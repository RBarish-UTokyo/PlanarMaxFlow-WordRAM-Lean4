module

public import PlanarFlow.BKMNW.SepSegs
public import PlanarFlow.BKMNW.MfStepZ

/-!
# The number of holes of a piece map read from its frame (math of `cntP`)

At a node call the step `stepPO` needs the number of parts of the separator, `π.segs.length`,
and the number of holes of the piece map, `(pholes …).length`. The holes of the call are pairwise
disjoint (`CallOk`), and the frame (`Lay`) holds the hole label `hlab Hs (tail (en i))` of every
dart (`HL`). A hole `Hs[j]` is a hole of the piece map (`pholes` keeps it) iff some dart of the
piece map has its tail in it, i.e. iff the label `j + 1` occurs in `HL`:

* `length_filter_eq_sum` (the length of a filtered list as a sum over the indices);
* `vimg_nonempty_iff`, **`pholes_length_eq`**: `(pholes …).length = Σ_{j < #Hs} [∃ i < m,
  HL[i] = j + 1]`.

The parts of the separator are read from the split's output `SegsOut` (`SepSegs.lean`), which is
overwritten by the children's runs before the step: **`SegsAt`** asks for it, at the step, in
`[e, b)` (between the frame and the heap top of the subroutines) with its base in `r6807`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit WordRAM WordRAM.Machine

universe w

/-- **The length of a filtered list** as a sum over its indices. -/
lemma length_filter_eq_sum {α : Type*} (p : α → Bool) (a₀ : α) :
    ∀ L : List α, (L.filter p).length =
      ∑ j ∈ range L.length, (if p (L.getD j a₀) then 1 else 0)
  | [] => by simp
  | a :: L => by
    rw [List.filter_cons, List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    have := length_filter_eq_sum p a₀ L
    split_ifs with h <;> simp [this]

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- The image of a vertex set in a piece map is nonempty iff some dart of the piece has its tail
in it. -/
lemma vimg_nonempty_iff {σ : Perm D} {B : Finset D} {X : Finset V} :
    (vimg M σ B X).Nonempty ↔ ∃ y ∈ B, M.tail y ∈ X := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨x, hx, -⟩ := mem_vimg.1 hw
    exact ⟨x.1, x.2, hx⟩
  · rintro ⟨y, hy, hX⟩
    exact ⟨_, mem_vimg.2 ⟨⟨y, hy⟩, hX, rfl⟩⟩

variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-- **The number of holes of the piece map from the frame's labels.** -/
theorem pholes_length_eq {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (hd : x.2.1.Pairwise Disjoint) :
    (pholes M x.2.2 (pdarts M x.1.piece x.2.1) x.2.1).length =
      ∑ j ∈ range x.2.1.length,
        (if ∃ i < m, mem (d + 4 + 5 * m + i) = j + 1 then 1 else 0) := by
  classical
  unfold pholes
  rw [List.filter_map, List.length_map, length_filter_eq_sum _ ∅]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  have key : (vimg M x.2.2 (pdarts M x.1.piece x.2.1) (x.2.1.getD j ∅)).Nonempty ↔
      ∃ i < m, mem (d + 4 + 5 * m + i) = j + 1 := by
    rw [vimg_nonempty_iff]
    constructor
    · rintro ⟨y, hy, ht⟩
      obtain ⟨i, hi, rfl⟩ := hL.en_surj y hy
      exact ⟨i, hi, by rw [hL.hl i hi]; exact (hlab_eq_succ_iff hd hj).2 ht⟩
    · rintro ⟨i, hi, he⟩
      rw [hL.hl i hi] at he
      exact ⟨en i, hL.en_mem i hi, (hlab_eq_succ_iff hd hj).1 he⟩
  simp only [Function.comp_apply, decide_eq_true_eq]
  by_cases h : ∃ i < m, mem (d + 4 + 5 * m + i) = j + 1
  · simp only [key.2 h, h, ↓reduceIte]
  · simp only [show ¬ (vimg M x.2.2 (pdarts M x.1.piece x.2.1) (x.2.1.getD j ∅)).Nonempty from
      fun h' => h (key.1 h'), h, ↓reduceIte]

variable (M) in
/-- **The parts of the separator for the step**: `SegsOut` from the base `Gb = r6807` (a register
of the step's loops, kept by every subroutine program, `SRegKeep`), the block inside `[e, b)`
(between the end of the frame and the heap top given to the subroutines, so that it is kept by
every `FlowProg`). -/
def SegsAt (en : ℕ → D) (m : ℕ) (π : HSep M) (e b : ℕ) (c : Config) : Prop :=
  SegsOut M en m π e b (c.nreg 6807) c.nmem

/-- `SegsAt` depends only on `r6807` and the memory in `[e, b)`. -/
lemma SegsAt.congr {en : ℕ → D} {m : ℕ} {π : HSep M} {e b : ℕ} {c c' : Config}
    (h : SegsAt M en m π e b c) (hr : c'.nreg 6807 = c.nreg 6807)
    (he : ∀ a, e ≤ a → a < b → c'.nmem a = c.nmem a) : SegsAt M en m π e b c' := by
  unfold SegsAt at h ⊢
  rw [hr]
  exact h.congr fun a h1 h2 => he a (by obtain ⟨h1', -⟩ := h; omega) h2

variable (M) in
/-- **`CntPSpec` with the parts of the separator** (`SegsAt`). The original
`CntPSpec` gives the program only the frame (`Lay`), which does not determine `π`. -/
def CntPSpecS (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ) (S T : Finset V) (Z : ℕ)
    (I : Input) (W : ℕ) (cntP : Stmt) (cnT rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (d e b m : ℕ)
    (en : ℕ → D) (c : Config),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) →
    Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem → SegsAt M en m π e b c →
    d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → WordsBounded W c → c.nreg 3004 = d →
    c.nreg 3005 = e → c.nreg 3006 = b + 5 →
    ∃ c' t, Exec I W cntP c c' t ∧ t ≤ cnT (.node l r π, Hs, σ) ∧
      DRegKeep c c' ∧
      (∀ a, a < b → c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      (∀ x, 6807 ≤ x → x ≤ 6819 → c'.nreg x = c.nreg x) ∧ c'.nreg 6801 = π.segs.length ∧
      c'.nreg 6806 = (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs).length + π.segs.length

end MfDrv

end BKMNW

end PlanarFlow
