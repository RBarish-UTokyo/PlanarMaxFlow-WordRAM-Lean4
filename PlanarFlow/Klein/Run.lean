module

public import PlanarFlow.Klein.Move

/-!
# The pivot loop of Klein's algorithm, with the colours read from the tree

Klein's multiple-source shortest paths in the form of Cabello, Chambers and Erickson (SIAM J.
Comput. 42, 2013, Section 3): as the source moves from `u` to `v`, the algorithm keeps a forest
rooted at `u` and `v` (the tree of the article without the edge `uv`). A vertex is *blue* when
its path in the forest leads to `v` (`Hang G P v`), *red* otherwise; an arc is *active* when it
goes from a blue vertex to a red one (`RActive`). One step of the algorithm takes an active arc
`b` of least slack (the answer of `MINPATH`) and makes it the parent arc of its head (the pivot).
Unlike the sweep of `PlanarFlow/Klein/Move.lean`, which turns the vertices blue one at a time,
a pivot turns a whole red subtree blue at once, and every pivot changes a parent.

**Ties.** No genericity is assumed: any active arc of least slack may be taken. The invariant
(`RInv`) only asks that the blue vertices have their parents towards `v`, the red ones towards
`u`, and that no red vertex has a larger gap `dist u - dist v` than a blue one.

* `RInv.step`: **a pivot on an active arc of least slack keeps the invariant**; the arc is the
  parent arc of its head in the tree of `v`, it is not tight for `u` (so the pivot changes a
  parent), and the blue vertices stay blue while the head turns blue (the article's
  Lemma 3.1 and Corollary 3.2, with the colours read from the forest).
* `RInv.forest`: under the invariant **the parent function is a forest rooted at `u` and `v`**:
  every vertex of the move leads to `u` or to `v`.
* `run_spec`: **a run ends with the shortest-path tree of `v`, after at most as many pivots as
  arcs tight for `v` and not for `u`**: for any sequence of pivots on active arcs of least slack
  that stops when no arc is active (`IsRun`), every intermediate parent function satisfies the
  invariant, the final one is `tpar G v`, and the number of pivots is at most
  `#(tight v \ tight u)`.
* `pstep`, `exists_run`: the pure algorithm (pivot on a canonical active arc of least slack, as
  long as there is one) is a run, and stops within `#moveSet` steps.
* `klein_run_pivots`: **around a face, the runs make at most `#S` pivots in total** (in the
  setting `PlanarFlow.MSSP.Hyp`, when the roots reach the same vertices off the face).

The slacks are those of `PlanarFlow.Klein.slack`, defined through the distances; an
implementation stores values that differ from them by a constant on the active arcs (which does
not change the arcs of least slack).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset MSSP Function

section Run

variable {X A : Type*} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A]
variable {G : Digraph X A}

variable (G) in
/-- `Hang G P r x`: following the parent arcs `P` from `x` leads to `r`. -/
inductive Hang (P : X → Option A) (r : X) : X → Prop
  | root : Hang P r r
  | step {x : X} {a : A} : P x = some a → Hang P r (G.src a) → Hang P r x

variable (G) in
/-- The gap `dist u x - dist v x`: the vertex `x` turns blue when the parameter passes it. -/
noncomputable def gap (u v x : X) : ℤ := dist G u x - dist G v x

variable (G) in
/-- **An active arc** of the forest `P`: from a blue vertex to a red vertex of the move. -/
def RActive (u v : X) (P : X → Option A) (b : A) : Prop :=
  Hang G P v (G.src b) ∧ G.dst b ∈ moveSet G u v ∧ ¬ Hang G P v (G.dst b)

variable (G) in
/-- **The invariant of the pivot loop**: no parent outside the move, the blue vertices have
their parents in the tree of `v`, the red ones in the tree of `u`, and no red vertex has a larger
gap than a blue one. -/
structure RInv (u v : X) (P : X → Option A) : Prop where
  off : ∀ x, x ∉ moveSet G u v → P x = none
  blue : ∀ x ∈ moveSet G u v, Hang G P v x → P x = tpar G v x
  red : ∀ x ∈ moveSet G u v, ¬ Hang G P v x → P x = tpar G u x
  gap : ∀ x ∈ moveSet G u v, ∀ y ∈ moveSet G u v, Hang G P v x → ¬ Hang G P v y →
    gap G u v y ≤ gap G u v x

section Move

variable {u v : X} (H : MoveHyp G u v)
include H

lemma MoveHyp.not_reach_uv : ¬ Reach G u v := by
  intro h
  obtain ⟨a, -, ha⟩ := exists_tight (fun a => (H.pos a).le) h (Ne.symm H.ne)
  exact H.noV a ha

lemma MoveHyp.tpar_off {r x : X} (hr : r = u ∨ r = v) (hx : x ∉ moveSet G u v) :
    tpar G r x = none := by
  rcases h : tpar G r x with _ | a
  · rfl
  obtain ⟨⟨hz, -⟩, rfl, hne⟩ := tpar_spec h
  exfalso
  refine hx (H.mem_moveSet.2 ⟨H.noU a, H.noV a, ?_⟩)
  rcases hr with rfl | rfl
  · exact hz.arc
  · exact (H.reach _ (H.noU a) (H.noV a)).2 hz.arc

lemma RInv.hang_mem {P : X → Option A} (hI : RInv G u v P) {r x : X} (h : Hang G P r x) :
    x = r ∨ x ∈ moveSet G u v := by
  cases h with
  | root => exact Or.inl rfl
  | step hx _ =>
    right
    by_contra hm
    rw [hI.off _ hm] at hx
    simp at hx

lemma RInv.reach_v {P : X → Option A} (hI : RInv G u v P) {x : X} (h : Hang G P v x) :
    Reach G v x := by
  rcases hI.hang_mem H h with rfl | hx
  · exact Reach.refl _
  · obtain ⟨h1, h2, h3⟩ := H.mem_moveSet.1 hx
    exact (H.reach _ h1 h2).1 h3

/-- **The initial forest**, the tree of `u`, satisfies the invariant (nothing is blue). -/
theorem rInv_init : RInv G u v (tpar G u) := by
  have hb : ∀ x, Hang G (tpar G u) v x → x = v := by
    intro x h
    induction h with
    | root => rfl
    | step ha _ ih =>
      obtain ⟨⟨hz, -⟩, -, -⟩ := tpar_spec ha
      rw [ih] at hz
      exact absurd hz H.not_reach_uv
  refine ⟨fun x hx => H.tpar_off (Or.inl rfl) hx, fun x hx h => ?_, fun _ _ _ => rfl,
    fun x hx y _ h => ?_⟩
  · exact absurd (hb x h) (H.mem_moveSet.1 hx).2.1
  · exact absurd (hb x h) (H.mem_moveSet.1 hx).2.1

/-- **The invariant gives a forest rooted at `u` and `v`**: every vertex of the move leads to `u`
or to `v` along the parent arcs. -/
theorem RInv.forest {P : X → Option A} (hI : RInv G u v P) (x : X) (hx : x ∈ moveSet G u v) :
    Hang G P u x ∨ Hang G P v x := by
  by_cases hb : Hang G P v x
  · exact Or.inr hb
  left
  have hnn : ∀ a, 0 ≤ G.len a := fun a => (H.pos a).le
  -- by strong induction on the distance from `u`
  suffices ∀ n : ℕ, ∀ x ∈ moveSet G u v, ¬ Hang G P v x → (dist G u x).toNat ≤ n → Hang G P u x
    from this _ x hx hb le_rfl
  intro n
  induction n with
  | zero =>
    intro x hx hb hn
    obtain ⟨h1, -, h3⟩ := H.mem_moveSet.1 hx
    obtain ⟨a, ha⟩ := tpar_isSome hnn h3 h1
    obtain ⟨⟨hz, ht⟩, hd, -⟩ := tpar_spec ha
    have := dist_nonneg hnn hz
    have := H.pos a
    rw [hd] at ht
    omega
  | succ n ih =>
    intro x hx hb hn
    obtain ⟨h1, -, h3⟩ := H.mem_moveSet.1 hx
    obtain ⟨a, ha⟩ := tpar_isSome hnn h3 h1
    have hPx : P x = some a := (hI.red x hx hb).trans ha
    obtain ⟨⟨hz, ht⟩, hd, -⟩ := tpar_spec ha
    have hzb : ¬ Hang G P v (G.src a) := fun h => hb (.step hPx h)
    refine .step hPx ?_
    by_cases hzu : G.src a = u
    · rw [hzu]; exact .root
    obtain ⟨-, hzv⟩ := H.ne_of_reach (Or.inl rfl) hz hzu
    have hzW : G.src a ∈ moveSet G u v := H.mem_moveSet.2 ⟨hzu, hzv, hz⟩
    refine ih _ hzW hzb ?_
    have := dist_nonneg hnn hz
    have := H.pos a
    rw [hd] at ht
    omega

section Step

variable {P : X → Option A} (hI : RInv G u v P) (hU : UniqTight G) {b : A}
  (hb : RActive G u v P b) (hmin : ∀ c, RActive G u v P c → slack G u v b ≤ slack G u v c)
include hI hU hb hmin

/-- The facts behind a pivot: the pivot arc is tight for `v`, and the head of the pivot arc has
the largest gap among the red vertices. -/
lemma step_aux :
    Tight G v b ∧ ∀ w ∈ moveSet G u v, ¬ Hang G P v w → gap G u v w ≤ gap G u v (G.dst b) := by
  classical
  have hnn : ∀ a, 0 ≤ G.len a := fun a => (H.pos a).le
  obtain ⟨hbs, hy, hyr⟩ := hb
  set R := (moveSet G u v).filter fun w => ¬ Hang G P v w with hR
  have hRm : ∀ w, w ∈ R ↔ w ∈ moveSet G u v ∧ ¬ Hang G P v w := fun w => by simp [hR]
  have hRne : R.Nonempty := ⟨_, (hRm _).2 ⟨hy, hyr⟩⟩
  obtain ⟨x, hxR, hxmax⟩ := R.exists_max_image (key G u v) hRne
  obtain ⟨hxW, hxr⟩ := (hRm x).1 hxR
  obtain ⟨hxu, hxv, hux⟩ := H.mem_moveSet.1 hxW
  obtain ⟨a, ha⟩ := tpar_isSome hnn ((H.reach x hxu hxv).1 hux) hxv
  obtain ⟨⟨hz, ht⟩, hd, -⟩ := tpar_spec ha
  -- the tail of the parent arc of `x` towards `v` is blue
  have hzb : Hang G P v (G.src a) := by
    by_cases hzv : G.src a = v
    · rw [hzv]; exact .root
    obtain ⟨hzu, -⟩ := H.ne_of_reach (Or.inr rfl) hz hzv
    have huz : Reach G u (G.src a) := (H.reach _ hzu hzv).2 hz
    have hzW : G.src a ∈ moveSet G u v := H.mem_moveSet.2 ⟨hzu, hzv, huz⟩
    by_contra hzr
    have e1 := dist_arc hnn huz
    have hp := H.pos a
    rw [hd] at e1 ht
    have h1 := hxmax _ ((hRm _).2 ⟨hzW, hzr⟩)
    unfold key at h1
    rw [Prod.Lex.toLex_le_toLex] at h1
    simp only at h1
    omega
  have hact : RActive G u v P a := ⟨hzb, hd ▸ hxW, hd ▸ hxr⟩
  have h1 := hmin a hact
  have hvs : Reach G v (G.src b) := hI.reach_v H hbs
  have e2 := dist_arc hnn hvs
  have h2 := hxmax _ ((hRm _).2 ⟨hy, hyr⟩)
  unfold key at h2
  rw [Prod.Lex.toLex_le_toLex] at h2
  simp only at h2
  unfold slack at h1
  rw [hd] at h1 ht
  have hgap : gap G u v (G.dst b) = gap G u v x := by unfold gap; omega
  refine ⟨⟨hvs, by omega⟩, fun w hw hwr => ?_⟩
  have h3 := hxmax _ ((hRm _).2 ⟨hw, hwr⟩)
  unfold key at h3
  rw [Prod.Lex.toLex_le_toLex] at h3
  simp only at h3
  rw [hgap]; unfold gap; omega

lemma step_hang_mono {x : X} (h : Hang G P v x) :
    Hang G (update P (G.dst b) (some b)) v x := by
  induction h with
  | root => exact .root
  | @step x a hx _ ih =>
    have hne : x ≠ G.dst b := by
      rintro rfl
      exact hb.2.2 (.step hx (by assumption))
    exact .step (by rw [update_of_ne hne]; exact hx) ih

lemma step_hang_sub {w : X} (h : Hang G P (G.dst b) w) :
    Hang G (update P (G.dst b) (some b)) v w := by
  induction h with
  | root =>
    exact .step (by rw [update_self]) (step_hang_mono H hI hU hb hmin hb.1)
  | @step x a hx _ ih =>
    by_cases hxe : x = G.dst b
    · subst hxe
      exact .step (by rw [update_self]) (step_hang_mono H hI hU hb hmin hb.1)
    · exact .step (by rw [update_of_ne hxe]; exact hx) ih

lemma step_hang_cases {w : X} (h : Hang G (update P (G.dst b) (some b)) v w) :
    Hang G P v w ∨ Hang G P (G.dst b) w := by
  induction h with
  | root => exact Or.inl .root
  | @step x a hx _ ih =>
    by_cases hxe : x = G.dst b
    · subst hxe; exact Or.inr .root
    rw [update_of_ne hxe] at hx
    rcases ih with h | h
    · exact Or.inl (.step hx h)
    · exact Or.inr (.step hx h)

/-- The red vertices below the head of the pivot arc have the gap of the head, and their parent
arcs are tight for `v` as well. -/
lemma step_sub {w : X} (h : Hang G P (G.dst b) w) (hw : ¬ Hang G P v w) :
    Reach G v w ∧ gap G u v w = gap G u v (G.dst b) ∧ w ∈ moveSet G u v ∧
      (w ≠ G.dst b → tpar G u w = tpar G v w) := by
  have hnn : ∀ a, 0 ≤ G.len a := fun a => (H.pos a).le
  obtain ⟨hT, hmax⟩ := step_aux H hI hU hb hmin
  induction h with
  | root => exact ⟨hT.1.arc, rfl, hb.2.1, fun h => absurd rfl h⟩
  | @step x a hx hz ih =>
    have hxW : x ∈ moveSet G u v := by
      by_contra hm; rw [hI.off _ hm] at hx; simp at hx
    have hzr : ¬ Hang G P v (G.src a) := fun h => hw (.step hx h)
    obtain ⟨hvz, hgz, -, -⟩ := ih hzr
    have hxu : P x = tpar G u x := hI.red x hxW hw
    rw [hxu] at hx
    obtain ⟨⟨huz, htu⟩, hd, hxu'⟩ := tpar_spec hx
    have e1 := dist_arc hnn hvz
    have h1 := hmax x hxW hw
    rw [hd] at e1 htu
    unfold gap at hgz h1 ⊢
    have hgx : dist G u x - dist G v x = dist G u (G.dst b) - dist G v (G.dst b) := by omega
    have htv : Tight G v a := ⟨hvz, by rw [hd]; omega⟩
    refine ⟨hd ▸ hvz.arc, hgx, hxW, fun _ => ?_⟩
    rw [hx, tpar_eq hU htv hd (H.mem_moveSet.1 hxW).2.1]

/-- **A pivot on an active arc of least slack keeps the invariant** (the article's Lemma 3.1 and
Corollary 3.2): the arc is the parent arc of its head in the tree of `v` and is not tight for
`u`, the blue vertices stay blue, and the head turns blue. -/
theorem RInv.step :
    tpar G v (G.dst b) = some b ∧ ¬ Tight G u b ∧
      RInv G u v (update P (G.dst b) (some b)) ∧
      (∀ x, Hang G P v x → Hang G (update P (G.dst b) (some b)) v x) ∧
      Hang G (update P (G.dst b) (some b)) v (G.dst b) := by
  obtain ⟨hT, hmax⟩ := step_aux H hI hU hb hmin
  obtain ⟨hbs, hy, hyr⟩ := hb
  have hyv : G.dst b ≠ v := (H.mem_moveSet.1 hy).2.1
  have htp : tpar G v (G.dst b) = some b := tpar_eq hU hT rfl hyv
  refine ⟨htp, fun htu => ?_, ⟨fun x hx => ?_, fun x hx h => ?_, fun x hx h => ?_,
    fun x hx w hw h1 h2 => ?_⟩, fun x h => step_hang_mono H hI hU ⟨hbs, hy, hyr⟩ hmin h,
    step_hang_sub H hI hU ⟨hbs, hy, hyr⟩ hmin .root⟩
  · -- a pivot changes a parent
    rcases hI.hang_mem H hbs with h | h
    · exact H.not_reach_uv (h ▸ htu.1)
    · have hPy : P (G.dst b) = some b := by
        rw [hI.red _ hy hyr, tpar_eq hU htu rfl (H.mem_moveSet.1 hy).1]
      exact hyr (.step hPy hbs)
  · have hne : x ≠ G.dst b := fun h => hx (h ▸ hy)
    rw [update_of_ne hne]; exact hI.off x hx
  · by_cases hxe : x = G.dst b
    · subst hxe; rw [update_self, htp]
    rw [update_of_ne hxe]
    rcases step_hang_cases H hI hU ⟨hbs, hy, hyr⟩ hmin h with h' | h'
    · exact hI.blue x hx h'
    · by_cases hxb : Hang G P v x
      · exact hI.blue x hx hxb
      rw [hI.red x hx hxb]
      exact (step_sub H hI hU ⟨hbs, hy, hyr⟩ hmin h' hxb).2.2.2 hxe
  · have hxe : x ≠ G.dst b := fun he => h (he ▸ step_hang_sub H hI hU ⟨hbs, hy, hyr⟩ hmin .root)
    rw [update_of_ne hxe]
    exact hI.red x hx fun h' => h (step_hang_mono H hI hU ⟨hbs, hy, hyr⟩ hmin h')
  · have hw' : ¬ Hang G P v w := fun h' => h2 (step_hang_mono H hI hU ⟨hbs, hy, hyr⟩ hmin h')
    have hwy := hmax w hw hw'
    rcases step_hang_cases H hI hU ⟨hbs, hy, hyr⟩ hmin h1 with h' | h'
    · exact hI.gap x hx w hw h' hw'
    · by_cases hxb : Hang G P v x
      · exact hI.gap x hx w hw hxb hw'
      rw [(step_sub H hI hU ⟨hbs, hy, hyr⟩ hmin h' hxb).2.1]
      exact hwy

end Step

/-- While a vertex of the move is red, some arc is active. -/
lemma exists_active (P : X → Option A) {x : X}
    (hx : x ∈ moveSet G u v) (hxr : ¬ Hang G P v x) : ∃ b, RActive G u v P b := by
  classical
  have hnn : ∀ a, 0 ≤ G.len a := fun a => (H.pos a).le
  -- the red vertex of least distance from `v` has its parent arc towards `v` active
  set R := (moveSet G u v).filter fun w => ¬ Hang G P v w with hR
  have hRm : ∀ w, w ∈ R ↔ w ∈ moveSet G u v ∧ ¬ Hang G P v w := fun w => by simp [hR]
  obtain ⟨y, hyR, hymin⟩ := R.exists_min_image (dist G v) ⟨x, (hRm x).2 ⟨hx, hxr⟩⟩
  obtain ⟨hyW, hyr⟩ := (hRm y).1 hyR
  obtain ⟨hyu, hyv, huy⟩ := H.mem_moveSet.1 hyW
  obtain ⟨a, ha⟩ := tpar_isSome hnn ((H.reach y hyu hyv).1 huy) hyv
  obtain ⟨⟨hz, ht⟩, hd, -⟩ := tpar_spec ha
  refine ⟨a, ?_, hd ▸ hyW, hd ▸ hyr⟩
  by_cases hzv : G.src a = v
  · rw [hzv]; exact .root
  obtain ⟨hzu, -⟩ := H.ne_of_reach (Or.inr rfl) hz hzv
  have hzW : G.src a ∈ moveSet G u v :=
    H.mem_moveSet.2 ⟨hzu, hzv, (H.reach _ hzu hzv).2 hz⟩
  by_contra hzr
  have := hymin _ ((hRm _).2 ⟨hzW, hzr⟩)
  have := H.pos a
  rw [hd] at ht
  omega

/-- **When no vertex is red, the forest is the tree of `v`.** -/
lemma RInv.eq_of_blue {P : X → Option A} (hI : RInv G u v P)
    (h : ∀ x ∈ moveSet G u v, Hang G P v x) : P = tpar G v := by
  funext x
  by_cases hx : x ∈ moveSet G u v
  · exact hI.blue x hx (h x hx)
  · rw [hI.off x hx, H.tpar_off (Or.inr rfl) hx]

end Move

variable (G) in
/-- **A run of the pivot loop**: from the tree of `u`, `m` pivots, each on an active arc of least
slack, ending when no arc is active. -/
structure IsRun (u v : X) (P : ℕ → X → Option A) (b : ℕ → A) (m : ℕ) : Prop where
  init : P 0 = tpar G u
  act : ∀ i < m, RActive G u v (P i) (b i)
  min : ∀ i < m, ∀ c, RActive G u v (P i) c → slack G u v (b i) ≤ slack G u v c
  next : ∀ i < m, P (i + 1) = update (P i) (G.dst (b i)) (some (b i))
  stop : ∀ c, ¬ RActive G u v (P m) c

open Classical in
/-- **A run ends with the shortest-path tree of `v`**, every intermediate parent function
satisfies the invariant (so it is a forest rooted at `u` and `v`, `RInv.forest`), every pivot
arc is tight for `v` and not for `u`, and the number of pivots is at most the number of arcs
tight for `v` and not for `u`. -/
theorem run_spec {u v : X} (H : MoveHyp G u v) (hU : UniqTight G) {P : ℕ → X → Option A}
    {b : ℕ → A} {m : ℕ} (hr : IsRun G u v P b m) :
    (∀ i ≤ m, RInv G u v (P i)) ∧
      (∀ i < m, tpar G v (G.dst (b i)) = some (b i) ∧ ¬ Tight G u (b i)) ∧
      P m = tpar G v ∧
      m ≤ ((univ.filter fun a => Tight G v a) \ univ.filter fun a => Tight G u a).card := by
  have hinv : ∀ i ≤ m, RInv G u v (P i) := by
    intro i
    induction i with
    | zero => intro _; rw [hr.init]; exact rInv_init H
    | succ i ih =>
      intro hi
      rw [hr.next i (by omega)]
      exact (RInv.step H (ih (by omega)) hU (hr.act i (by omega)) (hr.min i (by omega))).2.2.1
  have hstep : ∀ i < m, tpar G v (G.dst (b i)) = some (b i) ∧ ¬ Tight G u (b i) ∧
      (∀ x, Hang G (P i) v x → Hang G (P (i + 1)) v x) ∧ Hang G (P (i + 1)) v (G.dst (b i)) := by
    intro i hi
    have := RInv.step H (hinv i hi.le) hU (hr.act i hi) (hr.min i hi)
    rw [hr.next i hi]
    exact ⟨this.1, this.2.1, this.2.2.2⟩
  have hmono : ∀ i j, i ≤ j → j ≤ m → ∀ x, Hang G (P i) v x → Hang G (P j) v x := by
    intro i j hij hj
    induction j, hij using Nat.le_induction with
    | base => exact fun _ h => h
    | succ j hij ih => exact fun x h => (hstep j (by omega)).2.2.1 x (ih (by omega) x h)
  refine ⟨hinv, fun i hi => ⟨(hstep i hi).1, (hstep i hi).2.1⟩, ?_, ?_⟩
  · refine (hinv m le_rfl).eq_of_blue H fun x hx => ?_
    by_contra hxr
    obtain ⟨c, hc⟩ := exists_active H (P m) hx hxr
    exact hr.stop c hc
  · rcases isEmpty_or_nonempty A with hA | ⟨⟨a0⟩⟩
    · rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0]; exact Nat.zero_le _
      · exact isEmptyElim (b 0)
    have := card_le_card_of_injOn (s := range m)
      (t := (univ.filter fun a => Tight G v a) \ univ.filter fun a => Tight G u a) b
      (fun i hi => ?_) (fun i hi j hj hij => ?_)
    · simpa using this
    · have hi' : i < m := mem_range.1 hi
      obtain ⟨hT, -, -⟩ := tpar_spec (hstep i hi').1
      simp only [coe_sdiff, coe_filter, mem_univ, true_and, Set.mem_sdiff, Set.mem_ofPred_eq]
      exact ⟨hT, (hstep i hi').2.1⟩
    · have hi' : i < m := mem_range.1 hi
      have hj' : j < m := mem_range.1 hj
      by_contra hne
      have key : ∀ i j, i < j → j < m → b i ≠ b j := by
        intro i j hij hjm he
        have h1 := hmono (i + 1) j (by omega) hjm.le _ (hstep i (by omega)).2.2.2
        rw [he] at h1
        exact (hr.act j hjm).2.2 h1
      rcases lt_or_gt_of_ne hne with h | h
      · exact key i j h hj' hij
      · exact key j i h hi' hij.symm

/-! ### The pure algorithm -/

variable (G) in
open Classical in
/-- The active arcs of the forest `P`. -/
noncomputable def actives (u v : X) (P : X → Option A) : Finset A :=
  univ.filter fun b => RActive G u v P b

variable (G) in
open Classical in
/-- **`MINPATH`**: an active arc of least slack, if any (a canonical choice). -/
noncomputable def selMin (u v : X) (P : X → Option A) : Option A :=
  if h : (actives G u v P).Nonempty then
    some ((actives G u v P).exists_min_image (slack G u v) h).choose
  else none

variable (G) in
/-- **One step of the algorithm**: pivot on the arc chosen by `selMin`, if any. -/
noncomputable def pstep (u v : X) (P : X → Option A) : X → Option A :=
  match selMin G u v P with
  | some b => update P (G.dst b) (some b)
  | none => P

lemma selMin_some {u v : X} {P : X → Option A} {b : A} (h : selMin G u v P = some b) :
    RActive G u v P b ∧ ∀ c, RActive G u v P c → slack G u v b ≤ slack G u v c := by
  classical
  unfold selMin at h
  split_ifs at h with hne
  obtain rfl := Option.some.inj h
  obtain ⟨h1, h2⟩ := ((actives G u v P).exists_min_image (slack G u v) hne).choose_spec
  refine ⟨by simpa [actives] using h1, fun c hc => h2 c (by simpa [actives] using hc)⟩

lemma selMin_none {u v : X} {P : X → Option A} (h : selMin G u v P = none) (c : A) :
    ¬ RActive G u v P c := by
  classical
  intro hc
  unfold selMin at h
  have hne : (actives G u v P).Nonempty := ⟨c, by simpa [actives] using hc⟩
  simp [hne] at h

/-- **The pure algorithm is a run**: iterating `pstep` from the tree of `u`, the arc chosen by
`selMin` stops within `#moveSet` steps, and the steps before form a run. -/
theorem exists_run [Nonempty A] {u v : X} (H : MoveHyp G u v) (hU : UniqTight G) :
    ∃ m ≤ (moveSet G u v).card, ∃ b : ℕ → A,
      IsRun G u v (fun i => (pstep G u v)^[i] (tpar G u)) b m := by
  classical
  set P : ℕ → X → Option A := fun i => (pstep G u v)^[i] (tpar G u) with hP
  have hPs : ∀ i, P (i + 1) = pstep G u v (P i) := fun i => by
    simp only [hP]; rw [Function.iterate_succ_apply']
  -- the number of blue vertices of the move
  set cnt : ℕ → ℕ := fun i => ((moveSet G u v).filter fun x => Hang G (P i) v x).card
  -- while an arc is selected, the invariant holds and the blue vertices increase
  have hgo : ∀ i, (∀ j < i, selMin G u v (P j) ≠ none) → RInv G u v (P i) ∧ i ≤ cnt i := by
    intro i
    induction i with
    | zero => intro _; exact ⟨by simp [hP]; exact rInv_init H, Nat.zero_le _⟩
    | succ i ih =>
      intro h
      obtain ⟨hI, hc⟩ := ih fun j hj => h j (by omega)
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 (h i (by omega))
      obtain ⟨hba, hbm⟩ := selMin_some hb
      have hst := RInv.step H hI hU hba hbm
      have he : P (i + 1) = update (P i) (G.dst b) (some b) := by
        rw [hPs]; simp [pstep, hb]
      rw [he]
      refine ⟨hst.2.2.1, ?_⟩
      have : cnt i < cnt (i + 1) := by
        simp only [cnt, he]
        refine card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
        · simp only [mem_filter] at hx ⊢
          exact ⟨hx.1, hst.2.2.2.1 x hx.2⟩
        · have := hsub (mem_filter.2 ⟨hba.2.1, hst.2.2.2.2⟩)
          exact hba.2.2 (mem_filter.1 this).2
      omega
  have hcnt : ∀ i, cnt i ≤ (moveSet G u v).card := fun i => card_filter_le _ _
  have hex : ∃ i, selMin G u v (P i) = none := by
    by_contra hcon
    push Not at hcon
    have := (hgo ((moveSet G u v).card + 1) fun j _ => hcon j).2
    have := hcnt ((moveSet G u v).card + 1)
    omega
  set m := Nat.find hex with hm
  have hbefore : ∀ j < m, selMin G u v (P j) ≠ none := fun j hj => Nat.find_min hex hj
  have hmle : m ≤ (moveSet G u v).card := by
    have := (hgo m hbefore).2
    have := hcnt m
    omega
  have hsel : ∀ i < m, ∃ c, selMin G u v (P i) = some c := fun i hi =>
    Option.ne_none_iff_exists'.1 (hbefore i hi)
  refine ⟨m, hmle, fun i => (selMin G u v (P i)).getD (Classical.arbitrary A), ⟨rfl, ?_, ?_, ?_,
    selMin_none (Nat.find_spec hex)⟩⟩
  · intro i hi
    obtain ⟨c, hc⟩ := hsel i hi
    simp only [hc, Option.getD_some]
    exact (selMin_some hc).1
  · intro i hi
    obtain ⟨c, hc⟩ := hsel i hi
    simp only [hc, Option.getD_some]
    exact (selMin_some hc).2
  · intro i hi
    obtain ⟨c, hc⟩ := hsel i hi
    rw [hPs]
    simp [pstep, hc]

end Run

/-! ### Around the face -/

section Face

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

/-- **Around the face, the runs make at most `#S` pivots in total**: for any runs of the pivot
loop moving the source from every root `r j` to the next one `r ((j + 1) % k)`, with `m j`
pivots, `∑ j < k, m j ≤ #S`. -/
theorem klein_run_pivots (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (m : ℕ → ℕ)
    (hm : ∀ j < k, ∃ P b, IsRun (pieceGraph M S ℓ) (M.tail (g j)) (M.tail (g ((j + 1) % k)))
      P b (m j)) :
    ∑ j ∈ range k, m j ≤ S.card := by
  classical
  have hk : 2 ≤ k := H.face.two_le
  refine le_trans (sum_le_sum fun j hj => ?_) (sum_card_sptree_le H hR)
  have hj' : j < k := mem_range.1 hj
  have hne : j ≠ (j + 1) % k := by
    rcases Nat.lt_or_ge (j + 1) k with h | h
    · rw [Nat.mod_eq_of_lt h]; omega
    · rw [show j + 1 = k by omega, Nat.mod_self]; omega
  obtain ⟨P, b, hr⟩ := hm j hj'
  have := (run_spec (moveHyp_of_hyp H hR hj' (Nat.mod_lt _ (by omega)) hne) H.uniq hr).2.2.2
  convert this using 2; ext a; simp [sptree]

/-- **The pure algorithm around the face**: for every root the pure algorithm (`pstep`) is a run
to the next root, and the runs make at most `#S` pivots in total. -/
theorem klein_pure_pivots (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (hS : S.Nonempty) :
    ∃ m : ℕ → ℕ, (∀ j < k, ∃ b, IsRun (pieceGraph M S ℓ) (M.tail (g j))
      (M.tail (g ((j + 1) % k)))
      (fun i => (pstep (pieceGraph M S ℓ) (M.tail (g j)) (M.tail (g ((j + 1) % k))))^[i]
        (tpar (pieceGraph M S ℓ) (M.tail (g j)))) b (m j)) ∧
      ∑ j ∈ range k, m j ≤ S.card := by
  classical
  have : Nonempty {d // d ∈ S} := ⟨⟨_, hS.choose_spec⟩⟩
  have hk : 2 ≤ k := H.face.two_le
  have hex : ∀ j, ∃ m, j < k → ∃ b, IsRun (pieceGraph M S ℓ) (M.tail (g j))
      (M.tail (g ((j + 1) % k)))
      (fun i => (pstep (pieceGraph M S ℓ) (M.tail (g j)) (M.tail (g ((j + 1) % k))))^[i]
        (tpar (pieceGraph M S ℓ) (M.tail (g j)))) b m := by
    intro j
    by_cases hj : j < k
    · have hne : j ≠ (j + 1) % k := by
        rcases Nat.lt_or_ge (j + 1) k with h | h
        · rw [Nat.mod_eq_of_lt h]; omega
        · rw [show j + 1 = k by omega, Nat.mod_self]; omega
      obtain ⟨m, -, b, hb⟩ :=
        exists_run (moveHyp_of_hyp H hR hj (Nat.mod_lt _ (by omega)) hne) H.uniq
      exact ⟨m, fun _ => ⟨b, hb⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose m hm using hex
  exact ⟨m, fun j hj => hm j hj,
    klein_run_pivots H hR m fun j hj => let ⟨b, hb⟩ := hm j hj; ⟨_, b, hb⟩⟩

end Face

end Klein

end PlanarFlow
