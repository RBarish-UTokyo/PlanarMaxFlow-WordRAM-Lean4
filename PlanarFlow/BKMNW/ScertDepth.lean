module

public import PlanarFlow.BKMNW.ChoiceE

/-!
# The recursion of `scertD` has at most as many levels as cut-vertex holes

`scertD` recurses on the heavy component `K = comp M N Hs g z` off a cut-vertex hole `g`. A literal
implementation recomputes the components at every level; it is cheap because the number of levels
is small: **a hole that is not a cut vertex of `N` is not one of `K` either** (a path of `N` off
the hole `h` that leaves `K` leaves and re-enters it at the hole `g`, and can be shortcut there),
and `g` itself is not a cut vertex of `K`. So the set of cut-vertex holes strictly shrinks along the
recursion, and the cut-vertex holes of a connected piece map touch it: the depth is at most the
number of holes touching the piece map (`≤ 6` on the pieces of the decomposition, `DecS.lean`).

* `CutH M N Hs g` (the hole `g` is a cut vertex: the predicate of `scChoiceE`'s `hole`),
  `noCut_iff`, `cutH_touch` (cut-vertex holes of a connected `N` touch it);
* **`not_cutH_comp_self`**, **`not_cutH_comp`** (non-cut holes stay non-cut), `cutHs`,
  **`cutHs_comp_ssubset`**;
* `scDepth` (the number of recursive calls of `scertD`, same recursion), **`scDepth_le`**
  (`≤ #` cut-vertex holes), **`scDepth_le_nTouch`** (`≤ nTouch M N Hs` for a connected piece map),
  **`scDepth_scChoiceE`** (the choices `scChoiceE` meet the hypotheses).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit Relation CombMap PlanarSeparator

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

variable (M) in
/-- **The hole `g` is a cut vertex of the piece map `N`**: two darts of `N` off `g` are not
connected by steps avoiding `g`. -/
def CutH (N : Finset D) (Hs : List (Finset V)) (g : Finset V) : Prop :=
  ∃ x ∈ N, ∃ y ∈ N, M.tail x ∉ g ∧ M.tail y ∉ g ∧ ¬ ReflTransGen (AStep M N Hs g) x y

lemma noCut_iff {N : Finset D} {Hs : List (Finset V)} : NoCut M N Hs ↔ ∀ g ∈ Hs, ¬ CutH M N Hs g := by
  unfold NoCut CutH
  constructor
  · rintro h g hg ⟨x, hx, y, hy, h1, h2, h3⟩; exact h3 (h g hg x hx y hy h1 h2)
  · intro h g hg x hx y hy h1 h2
    by_contra h3; exact h g hg ⟨x, hx, y, hy, h1, h2, h3⟩

/-- **A cut-vertex hole of a connected piece map touches it.** -/
lemma cutH_touch {N : Finset D} {Hs : List (Finset V)}
    (hconn : ∀ x ∈ N, ∀ y ∈ N, ReflTransGen (HStep M N Hs) x y) {g : Finset V}
    (h : CutH M N Hs g) : ∃ d ∈ N, M.tail d ∈ g := by
  by_contra hno
  push Not at hno
  obtain ⟨x, hx, y, hy, -, -, hn⟩ := h
  apply hn
  have key : ∀ z, ReflTransGen (HStep M N Hs) x z → ReflTransGen (AStep M N Hs g) x z := by
    intro z hz
    induction hz with
    | refl => exact .refl
    | tail h1 hst ih =>
      rename_i b c
      have hb : b ∈ N := by
        rcases h1.cases_tail with h | ⟨_, _, h⟩
        · exact h ▸ hx
        · exact h.1
      refine ih.tail ⟨hst.1, ?_⟩
      rcases hst.2 with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, hno b hb⟩
  exact key y (hconn x hx y hy)

section Comp

variable {N : Finset D} {Hs : List (Finset V)}

/-- The steps of `N` from `z` stay in `comp N g z`. -/
lemma rtg_comp_of_rtg {g : Finset V} {z : D} :
    ∀ b, ReflTransGen (AStep M N Hs g) z b → ReflTransGen (AStep M (comp M N Hs g z) Hs g) z b := by
  intro b h
  induction h with
  | refl => exact .refl
  | tail h1 hst ih =>
    exact ih.tail ⟨mem_comp.2 ⟨hst.1, h1.tail hst⟩, hst.2⟩

/-- **The hole `g` is not a cut vertex of its component `comp N g z`.** -/
theorem not_cutH_comp_self (hd : Hs.Pairwise Disjoint) {g : Finset V} (hg : g ∈ Hs) {z : D}
    (hz : z ∈ N) : ¬ CutH M (comp M N Hs g z) Hs g := by
  rintro ⟨x, hx, y, hy, -, -, hn⟩
  apply hn
  have hgc := hClosed_of_mem hd hg
  have hzK : z ∈ comp M N Hs g z := self_mem_comp hz
  have h1 := rtg_comp_of_rtg (M := M) x (mem_comp.1 hx).2
  have h2 := rtg_comp_of_rtg (M := M) y (mem_comp.1 hy).2
  exact (rtg_symm_aStep hgc hzK h1).trans h2

/-- **A hole that is not a cut vertex of `N` is not one of a component `comp N g' z` off another
hole `g'`.** -/
theorem not_cutH_comp (hd : Hs.Pairwise Disjoint) (hB : Stable (revPerm M) N) {g g' : Finset V}
    (hg : g ∈ Hs) (hg' : g' ∈ Hs) (hne : g ≠ g') (hnc : ¬ CutH M N Hs g) (z : D) :
    ¬ CutH M (comp M N Hs g' z) Hs g := by
  rintro ⟨x, hx, y, hy, hxg, hyg, hn⟩
  apply hn
  set K := comp M N Hs g' z with hK
  have hdis : Disjoint g g' := disjoint_of_pairwise hd hg hg' hne
  have hxN : x ∈ N := (mem_comp.1 hx).1
  have hyN : y ∈ N := (mem_comp.1 hy).1
  have hpath : ReflTransGen (AStep M N Hs g) x y := by
    by_contra h; exact hnc ⟨x, hxN, y, hyN, hxg, hyg, h⟩
  -- the invariant along the path of `N`
  have key : ∀ b, ReflTransGen (AStep M N Hs g) x b → b ∈ N ∧
      (b ∈ K → ReflTransGen (AStep M K Hs g) x b) ∧
      (b ∉ K → ∃ a ∈ K, M.tail a ∈ g' ∧ ReflTransGen (AStep M K Hs g) x a) := by
    intro b hb
    induction hb with
    | refl => exact ⟨hxN, fun _ => .refl, fun h => absurd hx h⟩
    | tail _ hst ih =>
      rename_i b c _
      obtain ⟨hbN, ihK, ihO⟩ := ih
      refine ⟨hst.1, fun hc => ?_, fun hc => ?_⟩
      · by_cases hbK : b ∈ K
        · exact (ihK hbK).tail ⟨hc, hst.2⟩
        · obtain ⟨a, haK, hag', hxa⟩ := ihO hbK
          -- the step enters `K` at the hole `g'`
          have hcg' : M.tail c ∈ g' := by
            rcases hst.2 with e | ⟨e, -⟩
            · exact absurd (by have := comp_rev hB hc; rw [e, M.rev_rev] at this; exact this) hbK
            · by_contra hcg
              exact hbK (comp_closed hc ⟨hbN, Or.inr ⟨hRel_symm e, hcg⟩⟩)
          exact hxa.tail ⟨hc, Or.inr ⟨Or.inr ⟨g', hg', hag', hcg'⟩,
            fun h => disjoint_left.1 hdis h hag'⟩⟩
      · by_cases hbK : b ∈ K
        · -- the step leaves `K` at the hole `g'`
          refine ⟨b, hbK, ?_, ihK hbK⟩
          rcases hst.2 with e | ⟨e, -⟩
          · exact absurd (by rw [e]; exact comp_rev hB hbK) hc
          · by_contra hbg
            exact hc (comp_closed hbK ⟨hst.1, Or.inr ⟨e, hbg⟩⟩)
        · exact ihO hbK
  exact (key y hpath).2.1 hy

/-- The cut-vertex holes. -/
noncomputable def cutHs (M : CombMap D V F) (N : Finset D) (Hs : List (Finset V)) :
    Finset (Finset V) := by
  classical exact Hs.toFinset.filter fun g => CutH M N Hs g

lemma mem_cutHs {g : Finset V} : g ∈ cutHs M N Hs ↔ g ∈ Hs ∧ CutH M N Hs g := by
  classical simp [cutHs]

/-- **The cut-vertex holes strictly shrink** from `N` to the component `comp N g z` off a
cut-vertex hole `g` (`z ∈ N`). -/
theorem cutHs_comp_ssubset (hd : Hs.Pairwise Disjoint) (hB : Stable (revPerm M) N)
    {g : Finset V} (hg : g ∈ Hs) (hcut : CutH M N Hs g) {z : D} (hz : z ∈ N) :
    cutHs M (comp M N Hs g z) Hs ⊂ cutHs M N Hs := by
  refine Finset.ssubset_iff_subset_ne.2 ⟨fun h hh => ?_, fun he => ?_⟩
  · rw [mem_cutHs] at hh ⊢
    refine ⟨hh.1, ?_⟩
    by_contra hnc
    by_cases e : h = g
    · subst e; exact not_cutH_comp_self hd hg hz hh.2
    · exact not_cutH_comp hd hB hh.1 hg e hnc z hh.2
  · have : g ∈ cutHs M (comp M N Hs g z) Hs := he ▸ mem_cutHs.2 ⟨hg, hcut⟩
    exact not_cutH_comp_self hd hg hz (mem_cutHs.1 this).2

lemma card_cutHs_le_nTouch (hconn : ∀ x ∈ N, ∀ y ∈ N, ReflTransGen (HStep M N Hs) x y) :
    (cutHs M N Hs).card ≤ nTouch M N Hs := by
  classical
  unfold nTouch
  calc (cutHs M N Hs).card ≤ (Hs.filter fun H => ∃ v ∈ H, Touch M N v).toFinset.card := by
        refine card_le_card fun g hg => ?_
        rw [mem_cutHs] at hg
        obtain ⟨d, hd, hdg⟩ := cutH_touch hconn hg.2
        rw [List.mem_toFinset, List.mem_filter]
        exact ⟨hg.1, decide_eq_true ⟨_, hdg, d, hd, rfl⟩⟩
    _ ≤ _ := List.toFinset_card_le _

end Comp

/-! ### The number of levels of `scertD` -/

open Classical in
/-- **The number of recursive calls of `scertD`** (the same recursion, counting the prunes). -/
noncomputable def scDepth (ch : ScChoice M) (Hs : List (Finset V)) (N : Finset D) (τ : Perm D)
    (ex : D → ℕ) : ℕ :=
  if NoCut M N Hs then 0
  else
    match ch.hole N with
    | none => 0
    | some g =>
      match ch.heavy N g ex with
      | some z =>
        match ch.anchor (comp M N Hs g z) g with
        | none => 0
        | some a₀ =>
          if hK : (comp M N Hs g z).card < N.card then
            scDepth ch Hs (comp M N Hs g z) (ret τ (comp M N Hs g z))
              (fun d => ex d + if d = a₀ then ∑ d ∈ N \ comp M N Hs g z, (1 + ex d) else 0) + 1
          else 0
      | none => 0
termination_by N.card

/-- **`scertD` has at most as many levels as cut-vertex holes**, for choices returning a
cut-vertex hole of the list and a dart of the piece. -/
theorem scDepth_le {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) (ch : ScChoice M)
    (hhole : ∀ N g, ch.hole N = some g → g ∈ Hs ∧ CutH M N Hs g)
    (hheavy : ∀ N g ex z, ch.heavy N g ex = some z → z ∈ N) :
    ∀ (n : ℕ) (N : Finset D) (τ : Perm D) (ex : D → ℕ), N.card = n → Stable (revPerm M) N →
      scDepth ch Hs N τ ex ≤ (cutHs M N Hs).card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro N τ ex hn hB
    rw [scDepth]
    split_ifs with hnc
    · exact Nat.zero_le _
    · split
      · exact Nat.zero_le _
      · rename_i g hgo
        obtain ⟨hgH, hcut⟩ := hhole N g hgo
        split
        · rename_i z hzo
          have hz := hheavy N g ex z hzo
          split
          · exact Nat.zero_le _
          · rename_i a₀ _
            split_ifs with hK
            · have hss := cutHs_comp_ssubset hd hB hgH hcut hz
              have hB' : Stable (revPerm M) (comp M N Hs g z) := fun d hdK => by
                rw [revPerm_apply]; exact comp_rev hB hdK
              have := ih _ (hn ▸ hK) (comp M N Hs g z) (ret τ (comp M N Hs g z))
                (fun d => ex d + if d = a₀ then ∑ d ∈ N \ comp M N Hs g z, (1 + ex d) else 0)
                rfl hB'
              have := card_lt_card hss
              omega
            · exact Nat.zero_le _
        · exact Nat.zero_le _

/-- **The depth bound by the touching holes**: for a connected piece map (e.g. `PMap.conn`),
`scertD` has at most `nTouch M N Hs` levels. -/
theorem scDepth_le_nTouch {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) (ch : ScChoice M)
    (hhole : ∀ N g, ch.hole N = some g → g ∈ Hs ∧ CutH M N Hs g)
    (hheavy : ∀ N g ex z, ch.heavy N g ex = some z → z ∈ N) {N : Finset D} {τ : Perm D}
    (ex : D → ℕ) (hB : Stable (revPerm M) N)
    (hconn : ∀ x ∈ N, ∀ y ∈ N, ReflTransGen (HStep M N Hs) x y) :
    scDepth ch Hs N τ ex ≤ nTouch M N Hs :=
  (scDepth_le hd ch hhole hheavy _ N τ ex rfl hB).trans (card_cutHs_le_nTouch hconn)

open Classical in
/-- **The choices `scChoiceE` meet the hypotheses of `scDepth_le`.** -/
theorem scDepth_scChoiceE (sepF : SepFn M) (e : ℕ → D) (n : ℕ) (Hs : List (Finset V))
    (A W : ℕ) :
    (∀ N g, (scChoiceE M sepF e n Hs A W).hole N = some g → g ∈ Hs ∧ CutH M N Hs g) ∧
    (∀ N g ex z, (scChoiceE M sepF e n Hs A W).heavy N g ex = some z → z ∈ N) := by
  refine ⟨fun N g h => ?_, fun N g ex z h => ?_⟩
  · have h' : Hs.find? _ = some g := h
    exact ⟨List.mem_of_find?_eq_some h', by have := List.find?_some h'; simpa only [CutH, decide_eq_true_eq] using this⟩
  · exact (mem_filter.1 (findE_some h)).1

end BKMNW

end PlanarFlow
