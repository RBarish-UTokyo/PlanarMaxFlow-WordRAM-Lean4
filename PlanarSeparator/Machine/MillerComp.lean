module

public import WordRAM
public import PlanarSeparator.Machine.Frame

/-!
# Miller's separator on the machine: the components of a set of faces

A triangulated map is held as in `PlanarSeparator/Machine/Search.lean`: `k` faces, `3 k` darts,
the darts of face `f` are `3 f, 3 f + 1, 3 f + 2`, and the reversal `A x` of dart `x` lies on
the face `A x / 3`. Given flags `Av f` on the faces (a face is *selected* if `0 < Av f`), the
program `clab` labels the selected faces by their components: two selected faces get the same
label exactly when they are joined by a sequence of selected faces, each adjacent to the next
across a dart (`FA`); unselected faces keep the label `0`, selected ones get labels
`1, 2, …, cc` with `cc ≤ k` (`clab_exec`), within `68 k + 4` steps.

In Miller's algorithm (`PlanarSeparator/Machine/Miller.lean`) the selected faces are the faces
avoiding the levels `< l` of a breadth-first tree, and the labels are the components
`PlanarSeparator.Map.comp` at level `l`, used to find the heavy levels and to concentrate the
weights of the components of the outer level.

The program is a depth-first search with an explicit stack: the faces are scanned in order, and
an unlabelled selected face starts a new label; a face taken from the stack labels and pushes its
unlabelled selected neighbours.

## Registers and memory

Constants: `r140 = 0`, `r141 = 1`, `r142 = 3`, `r143 = k`, and the bases `r144 = bA` (the flags
`Av f` at `bA + f`), `r145 = bL` (the labels at `bL + f`), `r146 = bS` (the stack at `bS + i`),
`r147 = bR` (the reversals `A x` at `bR + x`). The program writes only `r150 … r159`: `r150` the
scanned face, `r151` the number of labels, `r154` the size of the stack, `r155` the visited
dart.

The proof follows a pure model (`vstep`, `PI`): a labelling `lb` and a stack `s`; the memory
holds them (`MC`).
-/

@[expose] public section

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### The pure model -/

section Pure

variable (k : ℕ) (A Av : ℕ → ℕ)

/-- Two selected faces adjacent across a dart of the first. -/
def FA (f g : ℕ) : Prop := f < k ∧ 0 < Av f ∧ 0 < Av g ∧ ∃ j < 3, A (3 * f + j) / 3 = g

/-- The reversals of a triangulated map. -/
def RevOk : Prop := ∀ x < 3 * k, A x < 3 * k ∧ A (A x) = x

variable {k A Av}

theorem FA.lt {f g : ℕ} (hA : RevOk k A) (h : FA k A Av f g) : g < k := by
  obtain ⟨hf, -, -, j, hj, rfl⟩ := h
  have := (hA (3 * f + j) (by omega)).1
  omega

theorem FA.symm {f g : ℕ} (hA : RevOk k A) (h : FA k A Av f g) : FA k A Av g f := by
  obtain ⟨hf, h1, h2, j, hj, rfl⟩ := h
  have hx := hA (3 * f + j) (by omega)
  refine ⟨by omega, h2, h1, A (3 * f + j) % 3, Nat.mod_lt _ (by omega), ?_⟩
  rw [Nat.div_add_mod, hx.2]
  omega

/-- One neighbour `h` seen from a face of label `cc`: if `h` is selected and unlabelled, it gets
the label `cc` and is pushed. -/
def vstep (cc : ℕ) (st : (ℕ → ℕ) × List ℕ) (h : ℕ) : (ℕ → ℕ) × List ℕ :=
  if 0 < Av h ∧ st.1 h = 0 then (upd st.1 h cc, st.2 ++ [h]) else st

variable (k A Av) in
/-- The invariant of the search, with the label count `cc`, the labels `lb`, the stack `s`, and
an exceptional face `e` (being processed) that need not be closed yet. -/
structure PI (cc e : ℕ) (lb : ℕ → ℕ) (s : List ℕ) : Prop where
  le : ∀ g < k, lb g ≤ cc
  av : ∀ g < k, lb g ≠ 0 → 0 < Av g
  conn : ∀ g < k, ∀ h < k, lb g ≠ 0 → lb h = lb g → Relation.ReflTransGen (FA k A Av) g h
  closed : ∀ g < k, lb g ≠ 0 → g ∉ s → g ≠ e → ∀ h, FA k A Av g h → lb h = lb g
  nodup : s.Nodup
  stk : ∀ g ∈ s, g < k ∧ lb g = cc

/-- The selected unlabelled faces. -/
noncomputable def unl (k : ℕ) (Av lb : ℕ → ℕ) : ℕ :=
  #((range k).filter fun g => 0 < Av g ∧ lb g = 0)

theorem unl_le (lb : ℕ → ℕ) : unl k Av lb ≤ k :=
  (card_le_card (filter_subset _ _)).trans (card_range k).le

theorem unl_upd {lb : ℕ → ℕ} {h cc : ℕ} (hh : h < k) (hA : 0 < Av h) (h0 : lb h = 0)
    (hcc : cc ≠ 0) : unl k Av (upd lb h cc) + 1 = unl k Av lb := by
  classical
  unfold unl
  have e1 : (range k).filter (fun g => 0 < Av g ∧ upd lb h cc g = 0) =
      ((range k).filter fun g => 0 < Av g ∧ lb g = 0).erase h := by
    ext g
    simp only [mem_filter, mem_erase, mem_range]
    by_cases hg : g = h
    · subst hg; simp [hcc]
    · simp [hg]
  rw [e1, card_erase_add_one]
  simp [hh, hA, h0]

/-- **One neighbour.** The invariant with exception `e` is kept when `e` (of label `cc`, not on
the stack) looks at the face across one of its darts. -/
theorem PI.step (hA : RevOk k A) {cc e : ℕ} {lb : ℕ → ℕ} {s : List ℕ} (hI : PI k A Av cc e lb s)
    (he : e < k) (hle : lb e = cc) (hcc : cc ≠ 0) {j : ℕ} (hj : j < 3) :
    PI k A Av cc e (vstep (Av := Av) cc (lb, s) (A (3 * e + j) / 3)).1
      (vstep (Av := Av) cc (lb, s) (A (3 * e + j) / 3)).2 := by
  set h := A (3 * e + j) / 3 with hh
  have hhk : h < k := by have := (hA (3 * e + j) (by omega)).1; omega
  unfold MillerProg.vstep
  dsimp only
  split_ifs with hc
  swap
  · exact hI
  obtain ⟨hAv, h0⟩ := hc
  have hFA : FA k A Av e h := ⟨he, hI.av e he (by omega), hAv, j, hj, rfl⟩
  have hns : h ∉ s := fun hm => by have := (hI.stk h hm).2; omega
  refine ⟨fun g hg => ?_, fun g hg => ?_, fun g hg g' hg' => ?_, fun g hg => ?_, ?_, ?_⟩
  · simp only [upd_apply]; split_ifs
    · exact le_rfl
    · exact hI.le g hg
  · simp only [upd_apply]; split_ifs with h1
    · exact fun _ => h1 ▸ hAv
    · exact hI.av g hg
  · simp only [upd_apply]
    -- every face of label `cc` is connected to `e`, hence to `h`
    have toE : ∀ x < k, lb x = cc → Relation.ReflTransGen (FA k A Av) x h := fun x hx hxl =>
      (hI.conn x hx e he (by omega) (by rw [hxl, hle])).tail hFA
    have fromE : ∀ x < k, lb x = cc → Relation.ReflTransGen (FA k A Av) h x := fun x hx hxl =>
      Relation.ReflTransGen.head (hFA.symm hA) (hI.conn e he x hx (by omega) (by rw [hxl, hle]))
    split_ifs with h1 h2 h2
    · subst h1; subst h2; exact fun _ _ => Relation.ReflTransGen.refl
    · subst h1; intro _ e2; exact fromE g' hg' e2
    · subst h2; intro _ e2; exact toE g hg e2.symm
    · exact hI.conn g hg g' hg'
  · simp only [upd_apply]
    intro hg0 hgs hge x hx
    have hgs' : g ∉ s := fun hm => hgs (List.mem_append_left _ hm)
    have hgh : g ≠ h := fun e' => hgs (by rw [e']; exact List.mem_append_right _ (by simp))
    simp only [hgh, ↓reduceIte] at hg0 ⊢
    have := hI.closed g hg hg0 hgs' hge x hx
    split_ifs with hxh
    · subst hxh; omega
    · exact this
  · exact List.nodup_append.2 ⟨hI.nodup, List.nodup_singleton _, fun a ha b hb => by
      simp only [List.mem_singleton] at hb; subst hb; exact fun e' => hns (e' ▸ ha)⟩
  · intro g hg
    simp only [upd_apply]
    rcases List.mem_append.1 hg with hg | hg
    · have := hI.stk g hg
      refine ⟨this.1, ?_⟩
      split_ifs <;> first | rfl | exact this.2
    · simp only [List.mem_singleton] at hg; subst hg; exact ⟨hhk, by simp⟩

theorem vstep_lb_ne {cc : ℕ} {lb : ℕ → ℕ} {s : List ℕ} (h x : ℕ) (hcc : cc ≠ 0)
    (hx : lb x ≠ 0) : (vstep (Av := Av) cc (lb, s) h).1 x ≠ 0 := by
  unfold vstep
  split_ifs with hc
  · simp only [upd_apply]; split_ifs with e
    · exact hcc
    · exact hx
  · exact hx

theorem vstep_lb_of_ne {cc : ℕ} {lb : ℕ → ℕ} {s : List ℕ} (h x : ℕ) (hx : lb x ≠ 0) :
    (vstep (Av := Av) cc (lb, s) h).1 x = lb x := by
  unfold vstep
  split_ifs with hc
  · simp only [upd_apply]; split_ifs with e
    · subst e; exact absurd hc.2 hx
    · rfl
  · rfl

theorem vstep_self {cc : ℕ} {lb : ℕ → ℕ} {s : List ℕ} (h : ℕ) (hcc : cc ≠ 0) (hh : 0 < Av h) :
    (vstep (Av := Av) cc (lb, s) h).1 h ≠ 0 := by
  unfold vstep
  split_ifs with hc
  · simp [hcc]
  · intro h0; exact hc ⟨hh, h0⟩

theorem vstep_of {cc h : ℕ} {lb : ℕ → ℕ} {s : List ℕ} (hc : 0 < Av h ∧ lb h = 0) :
    vstep (Av := Av) cc (lb, s) h = (upd lb h cc, s ++ [h]) := by
  unfold vstep; dsimp only; simp only [hc, and_self, ↓reduceIte]

theorem vstep_of_not {cc h : ℕ} {lb : ℕ → ℕ} {s : List ℕ} (hc : ¬ (0 < Av h ∧ lb h = 0)) :
    vstep (Av := Av) cc (lb, s) h = (lb, s) := by
  unfold vstep; dsimp only; simp only [hc, ↓reduceIte]

theorem len_le {l : List ℕ} (hn : l.Nodup) (hk : ∀ g ∈ l, g < k) : l.length ≤ k := by
  rw [← List.toFinset_card_of_nodup hn]
  calc #l.toFinset ≤ #(range k) :=
        card_le_card fun g hg => mem_range.2 (hk g (List.mem_toFinset.1 hg))
    _ = k := card_range k

theorem vstep_not_mem {cc x : ℕ} {st : (ℕ → ℕ) × List ℕ} (h : ℕ) (hx : x ∉ st.2)
    (h0 : st.1 x ≠ 0) : x ∉ (vstep (Av := Av) cc st h).2 := by
  unfold vstep
  split_ifs with hc
  · simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨hx, fun e => by rw [e] at h0; exact h0 hc.2⟩
  · exact hx

theorem unl_vstep {cc h : ℕ} {st : (ℕ → ℕ) × List ℕ} (hh : h < k) (hcc : cc ≠ 0) :
    unl k Av (vstep (Av := Av) cc st h).1 + (vstep (Av := Av) cc st h).2.length =
      unl k Av st.1 + st.2.length := by
  unfold vstep
  split_ifs with hc
  · have := unl_upd hh hc.1 hc.2 hcc (Av := Av) (lb := st.1)
    simp only [List.length_append, List.length_singleton]
    omega
  · rfl

/-- The three neighbours of `e`. -/
def vstep3 (cc e : ℕ) (st : (ℕ → ℕ) × List ℕ) : (ℕ → ℕ) × List ℕ :=
  vstep (Av := Av) cc (vstep (Av := Av) cc (vstep (Av := Av) cc st (A (3 * e) / 3))
    (A (3 * e + 1) / 3)) (A (3 * e + 2) / 3)

theorem unl_vstep3 (hA : RevOk k A) {cc e : ℕ} {st : (ℕ → ℕ) × List ℕ} (he : e < k)
    (hcc : cc ≠ 0) :
    unl k Av (vstep3 (A := A) (Av := Av) cc e st).1 +
      (vstep3 (A := A) (Av := Av) cc e st).2.length =
      unl k Av st.1 + st.2.length := by
  have h0 : ∀ j < 3, A (3 * e + j) / 3 < k := fun j hj => by
    have := (hA (3 * e + j) (by omega)).1; omega
  unfold vstep3
  rw [unl_vstep (h0 2 (by omega)) hcc, unl_vstep (h0 1 (by omega)) hcc,
    unl_vstep (by simpa using h0 0 (by omega)) hcc]

theorem vstep3_lb_of_ne {cc e x : ℕ} {lb : ℕ → ℕ} {s : List ℕ} (hcc : cc ≠ 0) (hx : lb x ≠ 0) :
    (vstep3 (A := A) (Av := Av) cc e (lb, s)).1 x = lb x := by
  unfold vstep3
  have h1 := vstep_lb_ne (Av := Av) (s := s) (A (3 * e) / 3) x hcc hx
  have h2 := vstep_lb_ne (Av := Av) (lb := (vstep (Av := Av) cc (lb, s) (A (3 * e) / 3)).1)
    (s := (vstep (Av := Av) cc (lb, s) (A (3 * e) / 3)).2) (A (3 * e + 1) / 3) x hcc h1
  rw [vstep_lb_of_ne _ _ h2, vstep_lb_of_ne _ _ h1, vstep_lb_of_ne _ _ hx]

theorem unl_mono {lb lb' : ℕ → ℕ} (hcc : ∀ g < k, lb' g = 0 → lb g = 0) :
    unl k Av lb' ≤ unl k Av lb :=
  card_le_card fun g hg => by
    simp only [mem_filter, mem_range] at hg ⊢
    exact ⟨hg.1, hg.2.1, hcc g hg.1 hg.2.2⟩

theorem PI.unpop {cc e : ℕ} {lb : ℕ → ℕ} {s : List ℕ} (hI : PI k A Av cc k lb (s ++ [e])) :
    PI k A Av cc e lb s ∧ e < k ∧ lb e = cc ∧ e ∉ s := by
  have hek := hI.stk e (List.mem_append_right _ (by simp))
  have hes : e ∉ s := fun hm => (List.nodup_append.1 hI.nodup).2.2 e hm e (by simp) rfl
  exact ⟨⟨hI.le, hI.av, hI.conn,
    fun g hg h1 h2 h3 => hI.closed g hg h1 (fun hm => by
      rcases List.mem_append.1 hm with hm | hm
      · exact h2 hm
      · simp only [List.mem_singleton] at hm; exact h3 hm) (by omega),
    (List.nodup_append.1 hI.nodup).1, fun g hg => hI.stk g (List.mem_append_left _ hg)⟩,
    hek.1, hek.2, hes⟩

/-- **A face taken from the stack.** After its three neighbours, `e` is closed. -/
theorem PI.pop (hA : RevOk k A) {cc e : ℕ} {lb : ℕ → ℕ} {s : List ℕ}
    (hI : PI k A Av cc k lb (s ++ [e])) (hcc : cc ≠ 0) :
    PI k A Av cc k (vstep3 (A := A) (Av := Av) cc e (lb, s)).1
      (vstep3 (A := A) (Av := Av) cc e (lb, s)).2 := by
  have hek := hI.stk e (List.mem_append_right _ (by simp))
  have hes : e ∉ s := fun hm => (List.nodup_append.1 hI.nodup).2.2 e hm e (by simp) rfl
  have hI0 : PI k A Av cc e lb s := ⟨hI.le, hI.av, hI.conn,
    fun g hg h1 h2 h3 => hI.closed g hg h1 (fun hm => by
      rcases List.mem_append.1 hm with hm | hm
      · exact h2 hm
      · simp only [List.mem_singleton] at hm; exact h3 hm) (by omega),
    (List.nodup_append.1 hI.nodup).1, fun g hg => hI.stk g (List.mem_append_left _ hg)⟩
  -- the three steps
  set st1 := vstep (Av := Av) cc (lb, s) (A (3 * e) / 3) with hst1
  have hI1 : PI k A Av cc e st1.1 st1.2 := by
    have := hI0.step hA hek.1 hek.2 hcc (j := 0) (by omega); simpa using this
  have hle1 : st1.1 e = cc := by rw [hst1, vstep_lb_of_ne _ _ (by omega)]; exact hek.2
  have hes1 : e ∉ st1.2 := vstep_not_mem _ hes (by simp only; omega)
  set st2 := vstep (Av := Av) cc (st1.1, st1.2) (A (3 * e + 1) / 3) with hst2
  have hI2 : PI k A Av cc e st2.1 st2.2 := hI1.step hA hek.1 hle1 hcc (by omega)
  have hle2 : st2.1 e = cc := by rw [hst2, vstep_lb_of_ne _ _ (by omega)]; exact hle1
  have hes2 : e ∉ st2.2 := vstep_not_mem _ hes1 (by simp only; omega)
  set st3 := vstep (Av := Av) cc (st2.1, st2.2) (A (3 * e + 2) / 3) with hst3
  have hI3 : PI k A Av cc e st3.1 st3.2 := hI2.step hA hek.1 hle2 hcc (by omega)
  have hle3 : st3.1 e = cc := by rw [hst3, vstep_lb_of_ne _ _ (by omega)]; exact hle2
  have hv3 : vstep3 (A := A) (Av := Av) cc e (lb, s) = st3 := rfl
  -- every selected neighbour of `e` is labelled at the end
  have hlab : ∀ j < 3, 0 < Av (A (3 * e + j) / 3) → st3.1 (A (3 * e + j) / 3) ≠ 0 := by
    intro j hj hav
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · rw [hst3]; refine vstep_lb_ne _ _ hcc ?_
      rw [hst2]; refine vstep_lb_ne _ _ hcc ?_
      rw [hst1]; simpa using vstep_self (s := s) (lb := lb) _ hcc hav
    · rw [hst3]; refine vstep_lb_ne _ _ hcc ?_
      rw [hst2]; exact vstep_self _ hcc hav
    · rw [hst3]; exact vstep_self _ hcc hav
  rw [hv3]
  refine ⟨hI3.le, hI3.av, hI3.conn, fun g hg h1 h2 h3 => ?_, hI3.nodup, hI3.stk⟩
  by_cases hge : g = e
  · subst hge
    intro x hx
    obtain ⟨-, -, hxa, j, hj, rfl⟩ := hx
    have hx0 := hlab j hj hxa
    have hxk : A (3 * g + j) / 3 < k := by have := (hA (3 * g + j) (by omega)).1; omega
    by_cases hxs : A (3 * g + j) / 3 ∈ st3.2
    · rw [(hI3.stk _ hxs).2, hle3]
    · by_cases hxg : A (3 * g + j) / 3 = g
      · rw [hxg]
      · exact (hI3.closed _ hxk hx0 hxs hxg g ((show FA k A Av g _ from
          ⟨hek.1, hI3.av g hek.1 h1, hxa, j, hj, rfl⟩).symm hA)).symm
  · exact hI3.closed g hg h1 h2 hge

/-- **A new label.** -/
theorem PI.start {cc : ℕ} {lb : ℕ → ℕ} (hI : PI k A Av cc k lb []) {f : ℕ} (hf : f < k)
    (hAv : 0 < Av f) (h0 : lb f = 0) : PI k A Av (cc + 1) k (upd lb f (cc + 1)) [f] := by
  refine ⟨fun g hg => ?_, fun g hg => ?_, fun g hg g' hg' => ?_, fun g hg => ?_, by simp,
    fun g hg => ?_⟩
  · simp only [upd_apply]; split_ifs
    · exact le_rfl
    · exact (hI.le g hg).trans (by omega)
  · simp only [upd_apply]; split_ifs with h1
    · exact fun _ => h1 ▸ hAv
    · exact hI.av g hg
  · simp only [upd_apply]
    split_ifs with h1 h2 h2
    · subst h1; subst h2; exact fun _ _ => Relation.ReflTransGen.refl
    · intro _ e2; have := hI.le g' hg'; omega
    · intro _ e2; have := hI.le g hg; omega
    · exact hI.conn g hg g' hg'
  · simp only [upd_apply, List.mem_singleton]
    intro hg0 hgs _ x hx
    simp only [hgs, ↓reduceIte] at hg0 ⊢
    have := hI.closed g hg hg0 (by simp) (by omega) x hx
    split_ifs with hxf
    · subst hxf; omega
    · exact this
  · simp only [List.mem_singleton] at hg; subst hg; exact ⟨hf, by simp⟩

/-- **The end.** With an empty stack and every selected face labelled, the labels are the
components. -/
theorem PI.spec (hA : RevOk k A) {cc : ℕ} {lb : ℕ → ℕ} (hI : PI k A Av cc k lb [])
    (hall : ∀ g < k, 0 < Av g → lb g ≠ 0) {f g : ℕ} (hf : f < k) (hg : g < k) (hAf : 0 < Av f)
    (_hAg : 0 < Av g) : lb f = lb g ↔ Relation.ReflTransGen (FA k A Av) f g := by
  refine ⟨fun e => hI.conn f hf g hg (hall f hf hAf) e.symm, fun h => ?_⟩
  have key : ∀ x, Relation.ReflTransGen (FA k A Av) f x → x < k ∧ lb x = lb f := by
    intro x hx
    induction hx with
    | refl => exact ⟨hf, rfl⟩
    | tail _ hyz ih =>
      refine ⟨hyz.lt hA, ?_⟩
      rw [← ih.2]
      exact hI.closed _ ih.1 (by rw [ih.2]; exact hall f hf hAf) (by simp) (by omega) _ hyz
  exact (key g h).2.symm

end Pure

/-! ### The program -/

/-- **One dart** `r155 = x` of the face taken from the stack: the face `h = A x / 3` across it
(`r157`) is labelled `r151` and pushed if it is selected and unlabelled; `r155 := x + 1`. -/
def visit : Stmt :=
  .seq (block [.addN 156 147 155, .loadN 157 156, .divN 157 157 142, .addN 156 144 157,
    .loadN 158 156, .addN 156 145 157, .loadN 159 156])
    (.seq (.ifLtN 159 141 (.ifLtN 158 141 .skip (block [.storeN 156 151, .addN 156 146 154,
      .storeN 156 157, .addN 154 154 141])) .skip) (.instr (.addN 155 155 141)))

/-- **Pop** the face `r152` from the stack and visit its three darts. -/
def pop : Stmt :=
  .seq (block [.subN 154 154 141, .addN 156 146 154, .loadN 152 156, .mulN 155 152 142])
    (.seq visit (.seq visit visit))

/-- **A new label** for the face `r150`: label it, push it, and search until the stack is
empty. -/
def newc : Stmt :=
  .seq (block [.addN 151 151 141, .addN 156 145 150, .storeN 156 151, .storeN 146 150,
    .copyN 154 141]) (.whileLtN 140 154 pop)

/-- **One face** `r150` of the scan. -/
def obody : Stmt :=
  .seq (block [.addN 156 145 150, .loadN 159 156, .addN 156 144 150, .loadN 158 156])
    (.seq (.ifLtN 159 141 (.ifLtN 158 141 .skip newc) .skip) (.instr (.addN 150 150 141)))

/-- **The components of the selected faces.** -/
def clab : Stmt := .seq (block [.copyN 150 140, .copyN 151 140]) (.whileLtN 150 143 obody)

/-- The constant registers of `clab`. -/
structure CR (k bA bL bS bR : ℕ) (c : Config) : Prop where
  r140 : c.nreg 140 = 0
  r141 : c.nreg 141 = 1
  r142 : c.nreg 142 = 3
  r143 : c.nreg 143 = k
  r144 : c.nreg 144 = bA
  r145 : c.nreg 145 = bL
  r146 : c.nreg 146 = bS
  r147 : c.nreg 147 = bR

theorem CR.of {k bA bL bS bR : ℕ} {c c' : Config} (h : CR k bA bL bS bR c)
    (e : ∀ r, r < 150 → c'.nreg r = c.nreg r) : CR k bA bL bS bR c' :=
  ⟨(e _ (by omega)).trans h.r140, (e _ (by omega)).trans h.r141, (e _ (by omega)).trans h.r142,
    (e _ (by omega)).trans h.r143, (e _ (by omega)).trans h.r144, (e _ (by omega)).trans h.r145,
    (e _ (by omega)).trans h.r146, (e _ (by omega)).trans h.r147⟩

/-! ### The proofs -/

section proofs

variable {k : ℕ} {A Av : ℕ → ℕ} {bA bL bS bR : ℕ} {W : ℕ} {P : Input}
  (hA : RevOk k A) (hlay : bR + 3 * k ≤ bA ∧ bA + k ≤ bL ∧ bL + k ≤ bS) (hW : bS + k ≤ W)
include hA hlay hW

theorem visit_exec {cc e j : ℕ} {lb : ℕ → ℕ} {s : List ℕ} (hI : PI k A Av cc e lb s)
    (he : e < k) (hle : lb e = cc) (hcc : cc ≠ 0) (hj : j < 3)
    (c : Config) (hc : WordsBounded W c) (hR : CR k bA bL bS bR c)
    (hAm : ∀ x < 3 * k, c.nmem (bR + x) = A x) (hAvm : ∀ f < k, c.nmem (bA + f) = Av f)
    (hlb : ∀ g < k, c.nmem (bL + g) = lb g)
    (hst : ∀ i (h : i < s.length), c.nmem (bS + i) = s[i])
    (h155 : c.nreg 155 = 3 * e + j) (h151 : c.nreg 151 = cc) (h154 : c.nreg 154 = s.length) :
    ∃ c' t, Exec P W visit c c' t ∧ t ≤ 15 ∧
      (∀ g < k, c'.nmem (bL + g) = (vstep (Av := Av) cc (lb, s) (A (3 * e + j) / 3)).1 g) ∧
      (∀ i (h : i < (vstep (Av := Av) cc (lb, s) (A (3 * e + j) / 3)).2.length),
        c'.nmem (bS + i) = (vstep (Av := Av) cc (lb, s) (A (3 * e + j) / 3)).2[i]) ∧
      c'.nreg 154 = (vstep (Av := Av) cc (lb, s) (A (3 * e + j) / 3)).2.length ∧
      c'.nreg 155 = 3 * e + j + 1 ∧
      (∀ r, r < 154 ∨ 160 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bL ∨ bS + k ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  obtain ⟨r140, r141, r142, r143, r144, r145, r146, r147⟩ := hR
  have hxk : 3 * e + j < 3 * k := by omega
  have hAx := (hA _ hxk).1
  have hhk : A (3 * e + j) / 3 < k := by omega
  have hPI := hI.step hA he hle hcc hj
  have hlen := len_le hPI.nodup fun g hg => (hPI.stk g hg).1
  unfold visit
  refine spec_seq ?_
  exec_block
  · rw [r147, h155]; omega
  · config_simp; rw [r144, r147, h155, r142, hAm _ hxk]; omega
  · config_simp; rw [r145, r147, h155, r142, hAm _ hxk]; omega
  rename_i hwb
  simp only [r144, r145, r147, h155, r142, hAm _ hxk] at hwb ⊢
  generalize hh : A (3 * e + j) / 3 = h at hwb hPI hlen hhk ⊢
  simp only [hAvm h hhk, hlb h hhk] at hwb ⊢
  refine spec_seq ?_
  by_cases hc0 : 0 < Av h ∧ lb h = 0
  · rw [vstep_of hc0] at hlen ⊢
    simp only [List.length_append, List.length_singleton] at hlen
    refine spec_ifLtN_true (by config_simp; rw [hc0.2, r141]; omega) ?_
    refine spec_ifLtN_false (by config_simp; simp only [r141]; omega) ?_
    exec_block
    · config_simp; rw [r146, h154]; omega
    · config_simp; rw [h154, r141]; omega
    refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; simp only [h155, r141]; omega))
      fun hw => ?_
    refine ⟨by omega, fun g hg => ?_, fun i hi => ?_, ?_, ?_, fun r hr => ?_, fun a ha => ?_, ?_⟩
    · config_simp
      rw [r146, h154, h151, upd_other _ _ _ (by omega), upd_apply]
      simp only [upd_apply, Nat.add_left_cancel_iff]
      split_ifs <;> first | rfl | exact hlb g hg
    · config_simp
      rw [r146, h154, h151]
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hil : i = s.length
      · subst hil; simp
      · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), hst i (by omega),
          List.getElem_append_left]
    · config_simp; rw [h154, r141]; simp
    · config_simp; simp only [h155, r141]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
    · config_simp; rw [r146, h154, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
    · config_simp
  · rw [vstep_of_not hc0]
    by_cases hl0 : lb h = 0
    · have hav : Av h = 0 := by by_contra hne; exact hc0 ⟨by omega, hl0⟩
      refine spec_ifLtN_true (by config_simp; rw [hl0, r141]; omega) ?_
      refine spec_ifLtN_true (by config_simp; rw [hav, r141]; omega) ?_
      refine spec_skip ‹_› ?_
      refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; simp only [h155, r141]; omega))
        fun hw => ?_
      refine ⟨by omega, fun g hg => by config_simp; exact hlb g hg, fun i hi => by
        config_simp; exact hst i hi, by config_simp; exact h154,
        by config_simp; simp only [h155, r141],
        fun r hr => ?_, fun a ha => by config_simp, by config_simp⟩
      config_simp; simp only [upd_apply]; split_ifs <;> omega
    · refine spec_ifLtN_false (by config_simp; simp only [r141]; omega) ?_
      refine spec_skip ‹_› ?_
      refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; simp only [h155, r141]; omega))
        fun hw => ?_
      refine ⟨by omega, fun g hg => by config_simp; exact hlb g hg, fun i hi => by
        config_simp; exact hst i hi, by config_simp; exact h154,
        by config_simp; simp only [h155, r141],
        fun r hr => ?_, fun a ha => by config_simp, by config_simp⟩
      config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- The memory holds the labels `lb` and the stack `s`. -/
def MC (k bL bS : ℕ) (lb : ℕ → ℕ) (s : List ℕ) (m : ℕ → ℕ) : Prop :=
  (∀ g < k, m (bL + g) = lb g) ∧ ∀ i (h : i < s.length), m (bS + i) = s[i]

theorem pop_exec {cc e : ℕ} {lb : ℕ → ℕ} {s : List ℕ} (hI : PI k A Av cc k lb (s ++ [e]))
    (hcc : cc ≠ 0) (c : Config) (hc : WordsBounded W c) (hR : CR k bA bL bS bR c)
    (hAm : ∀ x < 3 * k, c.nmem (bR + x) = A x) (hAvm : ∀ f < k, c.nmem (bA + f) = Av f)
    (hM : MC k bL bS lb (s ++ [e]) c.nmem) (h151 : c.nreg 151 = cc)
    (h154 : c.nreg 154 = s.length + 1) :
    ∃ c' t, Exec P W pop c c' t ∧ t ≤ 49 ∧
      MC k bL bS (vstep3 (A := A) (Av := Av) cc e (lb, s)).1
        (vstep3 (A := A) (Av := Av) cc e (lb, s)).2 c'.nmem ∧
      c'.nreg 154 = (vstep3 (A := A) (Av := Av) cc e (lb, s)).2.length ∧
      (∀ r, r < 152 ∨ 160 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bL ∨ bS + k ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  obtain ⟨hI0, hek, hle, hes⟩ := hI.unpop
  have hR' := hR
  obtain ⟨r140, r141, r142, r143, r144, r145, r146, r147⟩ := hR
  have hlen := len_le hI.nodup fun g hg => (hI.stk g hg).1
  simp only [List.length_append, List.length_singleton] at hlen
  have hse : c.nmem (bS + s.length) = e := by
    rw [hM.2 s.length (by simp)]; simp
  unfold pop
  refine spec_seq ?_
  exec_block
  · config_simp; rw [r146, h154, r141]; omega
  · config_simp; rw [r146, h154, r141, Nat.add_sub_cancel, hse, r142]; omega
  rename_i hwb
  simp only [r146, h154, r141, Nat.add_sub_cancel, hse, r142] at hwb ⊢
  -- the three visits
  refine spec_seq ?_
  refine spec_use (visit_exec hA hlay hW hI0 hek hle hcc (j := 0) (by omega) _ hwb
    (hR'.of fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> omega)
    (fun x hx => by config_simp; exact hAm x hx) (fun f hf => by config_simp; exact hAvm f hf)
    (fun g hg => by config_simp; exact hM.1 g hg)
    (fun i hi => by config_simp; rw [hM.2 i (by simp; omega)]; simp [List.getElem_append_left hi])
    (by config_simp; omega) (by config_simp; exact h151) (by config_simp)) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨m1, s1, l1, x1, r1, f1, o1⟩
  config_simp at r1
  config_simp at f1
  config_simp at o1
  set st1 := vstep (Av := Av) cc (lb, s) (A (3 * e + 0) / 3) with hst1
  have hP1 : PI k A Av cc e st1.1 st1.2 := hI0.step hA hek hle hcc (by omega)
  have hle1 : st1.1 e = cc := by rw [hst1, vstep_lb_of_ne _ _ (by omega)]; exact hle
  refine spec_seq ?_
  refine spec_use (visit_exec hA hlay hW hP1 hek hle1 hcc (j := 1) (by omega) _ hw₁
    (hR'.of fun r hr => by rw [r1 r (by omega)]; simp only [upd_apply]; split_ifs <;> omega)
    (fun x hx => by rw [f1 _ (Or.inl (by omega))]; exact hAm x hx)
    (fun f hf => by rw [f1 _ (Or.inl (by omega))]; exact hAvm f hf) m1 s1
    (by rw [x1]) (by rw [r1 151 (by omega)]; simp only [upd_apply]; split_ifs <;> omega) l1) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨m2, s2, l2, x2, r2, f2, o2⟩
  set st2 := vstep (Av := Av) cc (st1.1, st1.2) (A (3 * e + 1) / 3) with hst2
  have hP2 : PI k A Av cc e st2.1 st2.2 := hP1.step hA hek hle1 hcc (by omega)
  have hle2 : st2.1 e = cc := by rw [hst2, vstep_lb_of_ne _ _ (by omega)]; exact hle1
  refine spec_use (visit_exec hA hlay hW hP2 hek hle2 hcc (j := 2) (by omega) _ hw₂
    (hR'.of fun r hr => by
      rw [r2 r (by omega), r1 r (by omega)]; simp only [upd_apply]; split_ifs <;> omega)
    (fun x hx => by rw [f2 _ (Or.inl (by omega)), f1 _ (Or.inl (by omega))]; exact hAm x hx)
    (fun f hf => by rw [f2 _ (Or.inl (by omega)), f1 _ (Or.inl (by omega))]; exact hAvm f hf)
    m2 s2 (by rw [x2]) (by
      rw [r2 151 (by omega), r1 151 (by omega)]; simp only [upd_apply]; split_ifs <;> omega)
    l2) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨m3, s3, l3, x3, r3, f3, o3⟩
  refine ⟨by omega, ⟨m3, s3⟩, l3, fun r hr => ?_, fun a ha => ?_, by rw [o3, o2, o1]⟩
  · rw [r3 r (by omega), r2 r (by omega), r1 r (by omega)]
    simp only [upd_apply]; split_ifs <;> omega
  · rw [f3 a ha, f2 a ha, f1 a ha]

omit hA hlay hW in
/-- The loop rule with a ghost state, keeping the potential left at the end. -/
theorem whileLtN_ghost' {α : Type} {a b : ℕ} {body : Stmt} (I : α → Config → Prop)
    (Φ : α → Config → ℕ) (hI : ∀ x c, I x c → WordsBounded W c)
    (hbody : ∀ x c, I x c → c.nreg a < c.nreg b →
      ∃ x' c' k, Exec P W body c c' k ∧ I x' c' ∧ Φ x' c' + k + 2 ≤ Φ x c)
    {x : α} {c : Config} (hc : I x c) :
    ∃ x' c' k, Exec P W (.whileLtN a b body) c c' k ∧ I x' c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k + Φ x' c' ≤ Φ x c + 2 := by
  induction hn : Φ x c using Nat.strong_induction_on generalizing x c with
  | _ n ih =>
    by_cases ht : c.nreg a < c.nreg b
    · obtain ⟨x₁, c₁, k₁, hb, hI₁, hΦ⟩ := hbody x c hc ht
      obtain ⟨x', c', k₂, hl, hI', ht', hk₂⟩ := ih (Φ x₁ c₁) (by omega) hI₁ rfl
      exact ⟨x', c', k₁ + 2 + k₂, .whileLtN_true ht hb hl, hI', ht', by omega⟩
    · exact ⟨x, c, 2, .whileLtN_false ht (hI x c hc), hc, ht, by omega⟩

/-- **The search** from a stack of faces of label `cc`, until the stack is empty. -/
theorem srch_exec {cc : ℕ} {lb : ℕ → ℕ} {s : List ℕ} (hI : PI k A Av cc k lb s)
    (hcc : cc ≠ 0) (c : Config) (hc : WordsBounded W c) (hR : CR k bA bL bS bR c)
    (hAm : ∀ x < 3 * k, c.nmem (bR + x) = A x) (hAvm : ∀ f < k, c.nmem (bA + f) = Av f)
    (hM : MC k bL bS lb s c.nmem) (h151 : c.nreg 151 = cc) (h154 : c.nreg 154 = s.length) :
    ∃ c' t, Exec P W (.whileLtN 140 154 pop) c c' t ∧ ∃ lb' : ℕ → ℕ,
      t + 51 * unl k Av lb' ≤ 51 * (unl k Av lb + s.length) + 2 ∧
      PI k A Av cc k lb' [] ∧ MC k bL bS lb' [] c'.nmem ∧
      (∀ g < k, lb g ≠ 0 → lb' g = lb g) ∧
      (∀ r, r < 152 ∨ 160 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bL ∨ bS + k ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  let I : (ℕ → ℕ) × List ℕ → Config → Prop := fun x c' => WordsBounded W c' ∧
    PI k A Av cc k x.1 x.2 ∧ MC k bL bS x.1 x.2 c'.nmem ∧ c'.nreg 154 = x.2.length ∧
    (∀ g < k, lb g ≠ 0 → x.1 g = lb g) ∧
    (∀ r, r < 152 ∨ 160 ≤ r → c'.nreg r = c.nreg r) ∧
    (∀ a, a < bL ∨ bS + k ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output
  obtain ⟨x', c', t, e, ⟨hw', hP', hM', h154', hmono, hr', hf', ho'⟩, hn, ht⟩ :=
    whileLtN_ghost' (P := P) (W := W) (a := 140) (b := 154) (body := pop) I
    (fun x _ => 51 * (unl k Av x.1 + x.2.length)) (fun _ _ h => h.1)
    (fun x c₁ ⟨hw, hP, hM₁, h154₁, hmono, hr, hf, ho⟩ hlt => by
      have g140 : c₁.nreg 140 = 0 := by rw [hr 140 (by omega)]; exact hR.r140
      rw [g140, h154₁] at hlt
      obtain ⟨lb₁, s₁⟩ := x
      obtain ⟨s', e, rfl⟩ : ∃ s' e, s₁ = s' ++ [e] := ⟨s₁.dropLast, s₁.getLast
        (List.ne_nil_of_length_pos hlt), (List.dropLast_append_getLast _).symm⟩
      have hek := (hP.unpop).2.1
      obtain ⟨c₂, k₂, e₂, hk₂, hM₂, h154₂, hr₂, hf₂, ho₂⟩ := pop_exec hA hlay hW hP hcc c₁ hw
        (hR.of fun r hr' => hr r (by omega))
        (fun x hx => by rw [hf _ (Or.inl (by omega))]; exact hAm x hx)
        (fun f hf' => by rw [hf _ (Or.inl (by omega))]; exact hAvm f hf') hM₁
        (by rw [hr 151 (by omega)]; exact h151) (by rw [h154₁]; simp)
      refine ⟨vstep3 (A := A) (Av := Av) cc e (lb₁, s'), c₂, k₂, e₂, ⟨e₂.wb_right, hP.pop hA hcc,
        hM₂, h154₂, fun g hg hg0 => ?_, fun r hr' => by rw [hr₂ r hr', hr r hr'],
        fun a ha => by rw [hf₂ a ha, hf a ha], by rw [ho₂, ho]⟩, ?_⟩
      · have h1 : lb₁ g = lb g := hmono g hg hg0
        rw [vstep3_lb_of_ne hcc (by rw [h1]; exact hg0)]; exact h1
      · have := unl_vstep3 hA (Av := Av) (st := (lb₁, s')) hek hcc
        simp only [List.length_append, List.length_singleton] at this ⊢
        omega)
    (x := (lb, s)) ⟨hc, hI, hM, h154, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl⟩
  have g140 : c'.nreg 140 = 0 := by rw [hr' 140 (by omega)]; exact hR.r140
  rw [g140, h154'] at hn
  obtain ⟨lb', s'⟩ := x'
  have hs' : s' = [] := List.eq_nil_of_length_eq_zero (by simpa using hn)
  subst hs'
  refine ⟨c', t, e, lb', by simpa using ht, hP', hM', hmono, hr', hf', ho'⟩

/-- **One face of the scan.** -/
theorem obody_exec {cc f : ℕ} {lb : ℕ → ℕ} (hI : PI k A Av cc k lb []) (hcu : cc + unl k Av lb ≤ k)
    (hf : f < k) (hdone : ∀ g < f, 0 < Av g → lb g ≠ 0)
    (c : Config) (hc : WordsBounded W c) (hR : CR k bA bL bS bR c)
    (hAm : ∀ x < 3 * k, c.nmem (bR + x) = A x) (hAvm : ∀ f < k, c.nmem (bA + f) = Av f)
    (hM : ∀ g < k, c.nmem (bL + g) = lb g) (h150 : c.nreg 150 = f) (h151 : c.nreg 151 = cc) :
    ∃ c' t, Exec P W obody c c' t ∧ ∃ lb', t + 51 * unl k Av lb' + 2 ≤ 51 * unl k Av lb + 17 ∧
      PI k A Av (c'.nreg 151) k lb' [] ∧ c'.nreg 151 + unl k Av lb' ≤ k ∧
      (∀ g < f + 1, 0 < Av g → lb' g ≠ 0) ∧ (∀ g < k, c'.nmem (bL + g) = lb' g) ∧
      c'.nreg 150 = f + 1 ∧
      (∀ r, r < 150 ∨ 160 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bL ∨ bS + k ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  have hR' := hR
  obtain ⟨r140, r141, r142, r143, r144, r145, r146, r147⟩ := hR
  unfold obody
  refine spec_seq ?_
  exec_block
  · rw [r145, h150]; omega
  · config_simp; rw [r144, h150]; omega
  rename_i hwb
  simp only [r144, r145, h150, hM f hf, hAvm f hf] at hwb ⊢
  refine spec_seq ?_
  by_cases hc0 : 0 < Av f ∧ lb f = 0
  · -- a new label
    have hu := unl_upd hf hc0.1 hc0.2 (by omega : cc + 1 ≠ 0) (Av := Av) (lb := lb)
    have hP := hI.start hf hc0.1 hc0.2
    refine spec_ifLtN_true (by config_simp; rw [hc0.2, r141]; omega) ?_
    refine spec_ifLtN_false (by config_simp; rw [r141]; omega) ?_
    unfold newc
    refine spec_seq ?_
    exec_block
    · config_simp; rw [h151, r141]; omega
    · config_simp; rw [r145, h150]; omega
    rename_i hwc
    simp only [h151, r141, r145, r146, h150] at hwc ⊢
    obtain ⟨c₂, t₂, e₂, lb', ht₂, hP₂, hM₂, hmono, hr₂, hf₂, ho₂⟩ := srch_exec hA hlay hW hP
      (by omega) _ hwc
      (hR'.of fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> omega)
      (fun x hx => by
        config_simp; rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact hAm x hx)
      (fun g hg => by
        config_simp; rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact hAvm g hg)
      ⟨fun g hg => by
        config_simp; rw [upd_other _ _ _ (by omega)]
        simp only [upd_apply, Nat.add_left_cancel_iff]
        split_ifs <;> first | rfl | exact hM g hg, fun i hi => by
        simp only [List.length_singleton] at hi
        obtain rfl : i = 0 := by omega
        config_simp; simp⟩
      (by config_simp) (by config_simp; simp)
    refine ⟨c₂, t₂, e₂, ?_⟩
    have g150 : c₂.nreg 150 = f := by rw [hr₂ 150 (by omega)]; config_simp; exact h150
    have g151 : c₂.nreg 151 = cc + 1 := by rw [hr₂ 151 (by omega)]; config_simp
    have g141 : c₂.nreg 141 = 1 := by rw [hr₂ 141 (by omega)]; config_simp; exact r141
    have hunl : unl k Av lb' ≤ unl k Av (upd lb f (cc + 1)) := unl_mono fun g hg h0 => by
      by_contra hne; exact (hmono g hg hne ▸ hne) h0
    refine spec_instr (Exec.addN e₂.wb_right _ _ _ (by rw [g150, g141]; omega)) fun hw => ?_
    simp only [List.length_singleton] at ht₂
    refine ⟨lb', by omega, by config_simp; rw [g151]; exact hP₂, by config_simp; rw [g151]; omega,
      fun g hg hag => ?_, fun g hg => by config_simp; exact hM₂.1 g hg,
      by config_simp; rw [g150, g141], fun r hr => ?_, fun a ha => ?_, by config_simp; rw [ho₂]⟩
    · have hne : upd lb f (cc + 1) g ≠ 0 := by
        simp only [upd_apply]; split_ifs with hgf
        · omega
        · exact hdone g (by omega) hag
      rw [hmono g (by omega) hne]; exact hne
    · config_simp; rw [upd_other _ _ _ (by omega), hr₂ r (by omega)]; config_simp
      simp only [upd_apply]; split_ifs <;> omega
    · config_simp; rw [hf₂ a ha]; config_simp
      rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
  · -- nothing to do
    have hnew : ∀ g < f + 1, 0 < Av g → lb g ≠ 0 := fun g hg hag => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | rfl
      · exact hdone g hg hag
      · exact fun h0 => hc0 ⟨hag, h0⟩
    by_cases hl0 : lb f = 0
    · have hav : Av f = 0 := by by_contra hne; exact hc0 ⟨by omega, hl0⟩
      refine spec_ifLtN_true (by config_simp; rw [hl0, r141]; omega) ?_
      refine spec_ifLtN_true (by config_simp; rw [hav, r141]; omega) ?_
      refine spec_skip ‹_› ?_
      refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h150, r141]; omega))
        fun hw => ?_
      refine ⟨lb, by omega, by config_simp; rw [h151]; exact hI,
        by config_simp; rw [h151]; exact hcu,
        hnew, fun g hg => by config_simp; exact hM g hg, by config_simp; rw [h150, r141],
        fun r hr => ?_, fun a ha => by config_simp, by config_simp⟩
      config_simp; simp only [upd_apply]; split_ifs <;> omega
    · refine spec_ifLtN_false (by config_simp; rw [r141]; omega) ?_
      refine spec_skip ‹_› ?_
      refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h150, r141]; omega))
        fun hw => ?_
      refine ⟨lb, by omega, by config_simp; rw [h151]; exact hI,
        by config_simp; rw [h151]; exact hcu,
        hnew, fun g hg => by config_simp; exact hM g hg, by config_simp; rw [h150, r141],
        fun r hr => ?_, fun a ha => by config_simp, by config_simp⟩
      config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **The components of the selected faces.** Starting from zero labels, `clab` ends within
`68 k + 4` steps with labels `lb` at `bL + f` and their number `cc ≤ k` in `r151`: a face is
labelled if and only if it is selected, and two selected faces have the same label if and only
if they are joined through adjacent selected faces. -/
theorem clab_exec (c : Config) (hc : WordsBounded W c) (hR : CR k bA bL bS bR c)
    (hAm : ∀ x < 3 * k, c.nmem (bR + x) = A x) (hAvm : ∀ f < k, c.nmem (bA + f) = Av f)
    (hz : ∀ g < k, c.nmem (bL + g) = 0) :
    ∃ c' t, Exec P W clab c c' t ∧ t ≤ 68 * k + 4 ∧
      ∃ lb : ℕ → ℕ, (∀ g < k, c'.nmem (bL + g) = lb g) ∧ c'.nreg 151 ≤ k ∧
      (∀ g < k, lb g ≤ c'.nreg 151) ∧ (∀ g < k, lb g = 0 ↔ Av g = 0) ∧
      (∀ f < k, ∀ g < k, 0 < Av f → 0 < Av g →
        (lb f = lb g ↔ Relation.ReflTransGen (FA k A Av) f g)) ∧
      (∀ r, r < 150 ∨ 160 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bL ∨ bS + k ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  have hR' := hR
  obtain ⟨r140, r141, r142, r143, r144, r145, r146, r147⟩ := hR
  let I : (ℕ → ℕ) → Config → Prop := fun lb c' => WordsBounded W c' ∧
    c'.nreg 150 ≤ k ∧ PI k A Av (c'.nreg 151) k lb [] ∧ c'.nreg 151 + unl k Av lb ≤ k ∧
    (∀ g < c'.nreg 150, 0 < Av g → lb g ≠ 0) ∧ (∀ g < k, c'.nmem (bL + g) = lb g) ∧
    (∀ r, r < 150 ∨ 160 ≤ r → c'.nreg r = c.nreg r) ∧
    (∀ a, a < bL ∨ bS + k ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output
  unfold clab
  refine spec_seq ?_
  exec_block
  rename_i hwb
  have hI0 : I (fun _ => 0)
      { c with nreg := upd (upd c.nreg 150 (c.nreg 140)) 151 (c.nreg 140) } := by
    refine ⟨hwb, by config_simp; omega, ?_, ?_,
      fun g hg => absurd hg (by config_simp; rw [r140]; omega),
      fun g hg => by config_simp; exact hz g hg, fun r hr => ?_, fun _ _ => rfl, rfl⟩
    · config_simp; rw [r140]
      exact ⟨fun _ _ => le_rfl, fun _ _ h => absurd rfl h, fun _ _ _ _ h => absurd rfl h,
        fun _ _ h => absurd rfl h, List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
    · config_simp; rw [r140]; have := unl_le (Av := Av) (k := k) (fun _ => 0); omega
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  obtain ⟨lb, c', t, e, ⟨hw', h150', hP', hcu', hdone', hM', hr', hf', ho'⟩, hn, ht⟩ :=
    Exec.whileLtN_ghost (P := P) (W := W) (a := 150) (b := 143) (body := obody) I
    (fun lb c' => 51 * unl k Av lb + 17 * (k - c'.nreg 150)) (fun _ _ h => h.1)
    (fun lb c₁ ⟨hw, h150, hP, hcu, hdone, hM, hr, hf, ho⟩ hlt => by
      have g143 : c₁.nreg 143 = k := by rw [hr 143 (by omega)]; exact r143
      rw [g143] at hlt
      obtain ⟨c₂, t₂, e₂, lb', ht₂, hP₂, hcu₂, hdone₂, hM₂, h150₂, hr₂, hf₂, ho₂⟩ :=
        obody_exec hA hlay hW hP hcu hlt hdone c₁ hw (hR'.of fun r hr' => hr r (Or.inl hr'))
          (fun x hx => by rw [hf _ (Or.inl (by omega))]; exact hAm x hx)
          (fun f hf' => by rw [hf _ (Or.inl (by omega))]; exact hAvm f hf') hM rfl rfl
      refine ⟨lb', c₂, t₂, e₂, ⟨e₂.wb_right, by omega, hP₂, hcu₂, by rw [h150₂]; exact hdone₂,
        hM₂, fun r hr' => by rw [hr₂ r hr', hr r hr'], fun a ha => by rw [hf₂ a ha, hf a ha],
        by rw [ho₂, ho]⟩, ?_⟩
      rw [h150₂]
      omega) hI0
  have g143 : c'.nreg 143 = k := by rw [hr' 143 (by omega)]; exact r143
  rw [g143] at hn
  have hfk : c'.nreg 150 = k := by omega
  refine ⟨c', t, e, ?_, lb, hM', by have := hcu'; omega, hP'.le, fun g hg => ⟨fun h0 => ?_,
    fun h0 => ?_⟩, fun f hf g hg haf hag => hP'.spec hA (fun g hg hag => hdone' g (by omega) hag)
    hf hg haf hag, hr', hf', ho'⟩
  · have := unl_le (Av := Av) (k := k) (fun _ => 0)
    config_simp at ht
    rw [r140] at ht
    omega
  · by_contra hne; exact hdone' g (by omega) (by omega) h0
  · by_contra hne; exact hne (hP'.av g hg hne |>.ne' |> fun h => absurd h0 (by omega))

end proofs

end MillerProg

end PlanarSeparator
