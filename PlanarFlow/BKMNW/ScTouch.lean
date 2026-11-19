module

public import PlanarFlow.BKMNW.ScertDepth

/-!
# `scertD` sees only the holes that touch the piece map

The certificate recursion `scertD (scChoiceE … Hs …) Hs N τ ex` iterates (on the machine) over all
the holes `Hs` at every level (`hlProg`, `|Hs| · (160 n + 36)` steps per level). Only the holes
that **touch** the darts `B ⊇ N` matter: a hole containing no tail of a dart of `B` relates no two
tails of `B`, never meets the new hole of a dart of `B`, and is not a cut vertex of a connected `N`
(`cutH_touch`). So the recursion with the list `tHs B Hs` of the touching holes (in order) is the
same function:

* `tHs B Hs := Hs.filter (∃ d ∈ B, tail d ∈ ·)`, `mem_tHs`, `length_tHs_le` (`≤ |Hs|`),
  `length_tHs_le_nTouch` (`≤ nTouch M P Hs` for `B ⊆ P`);
* `hRel_tHs`, `aStep_tHs`, `rtg_congr_on`, `rtg_aStep_tHs`, `comp_tHs`, `cutH_tHs`,
  `noCut_tHs`, `newHole_tHs`, `pruneI_tHs`, `cutCert_tHs`, `hStep_conn_tHs`, `find?_filter_eq`,
  `conn_comp` (a component off a hole of the list is connected);
* **`scertD_tHs`**: for `N ⊆ B` connected (`HStep`), `scertD (scChoiceE … Hs …) Hs N τ ex =
  scertD (scChoiceE … (tHs B Hs) …) (tHs B Hs) N τ ex`;
* **`scDepth_tHs_le`**: the depth of the latter is at most `|tHs B Hs|`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit Relation CombMap PlanarSeparator

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

open Classical in
variable (M) in
/-- **The holes touching the darts `B`**, in the order of the list. -/
noncomputable def tHs (B : Finset D) (Hs : List (Finset V)) : List (Finset V) :=
  Hs.filter fun g => decide (∃ d ∈ B, M.tail d ∈ g)

lemma mem_tHs {B : Finset D} {Hs : List (Finset V)} {g : Finset V} :
    g ∈ tHs M B Hs ↔ g ∈ Hs ∧ ∃ d ∈ B, M.tail d ∈ g := by
  classical
  unfold tHs; simp [List.mem_filter]

lemma length_tHs_le (B : Finset D) (Hs : List (Finset V)) : (tHs M B Hs).length ≤ Hs.length :=
  List.length_filter_le _ _

lemma tHs_pairwise {B : Finset D} {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) :
    (tHs M B Hs).Pairwise Disjoint :=
  List.Pairwise.filter _ hd

open Classical in
/-- **At most `nTouch` touching holes** when `B ⊆ P`. -/
lemma length_tHs_le_nTouch {B P : Finset D} (hBP : B ⊆ P) (Hs : List (Finset V)) :
    (tHs M B Hs).length ≤ nTouch M P Hs := by
  unfold tHs nTouch
  refine (List.Sublist.length_le ?_)
  refine List.monotone_filter_right _ ?_
  intro g hg
  simp only [decide_eq_true_eq] at hg ⊢
  obtain ⟨d, hd, hdg⟩ := hg
  exact ⟨_, hdg, d, hBP hd, rfl⟩

/-- The relation of the holes at a tail of `B` is that of the touching holes. -/
lemma hRel_tHs {B : Finset D} {Hs : List (Finset V)} {a : D} (ha : a ∈ B) (w : V) :
    HRel Hs (M.tail a) w ↔ HRel (tHs M B Hs) (M.tail a) w := by
  unfold HRel
  constructor
  · rintro (h | ⟨H, hH, h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨H, mem_tHs.2 ⟨hH, a, ha, h1⟩, h1, h2⟩
  · rintro (h | ⟨H, hH, h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨H, (mem_tHs.1 hH).1, h1, h2⟩

lemma aStep_tHs {B N : Finset D} {Hs : List (Finset V)} {g : Finset V} {a b : D} (ha : a ∈ B) :
    AStep M N Hs g a b ↔ AStep M N (tHs M B Hs) g a b := by
  unfold AStep
  rw [hRel_tHs ha]

lemma hStep_tHs {B N : Finset D} {Hs : List (Finset V)} {a b : D} (ha : a ∈ B) :
    HStep M N Hs a b ↔ HStep M N (tHs M B Hs) a b := by
  unfold HStep
  rw [hRel_tHs ha]

/-- Two relations agreeing on a set closed under both give the same paths from the set. -/
lemma rtg_congr_on {α : Type*} {R R' : α → α → Prop} {S : α → Prop}
    (hRR : ∀ a b, S a → (R a b ↔ R' a b)) (hS : ∀ a b, R a b → S b) {x y : α} (hx : S x) :
    ReflTransGen R x y ↔ ReflTransGen R' x y := by
  have hS' : ∀ a b, S a → R' a b → S b := fun a b ha h => hS a b ((hRR a b ha).2 h)
  constructor
  · intro h
    have key : S y ∧ ReflTransGen R' x y := by
      induction h with
      | refl => exact ⟨hx, .refl⟩
      | tail _ hst ih => exact ⟨hS _ _ hst, ih.2.tail ((hRR _ _ ih.1).1 hst)⟩
    exact key.2
  · intro h
    have key : S y ∧ ReflTransGen R x y := by
      induction h with
      | refl => exact ⟨hx, .refl⟩
      | tail _ hst ih => exact ⟨hS' _ _ ih.1 hst, ih.2.tail ((hRR _ _ ih.1).2 hst)⟩
    exact key.2

lemma rtg_aStep_tHs {B N : Finset D} (hNB : N ⊆ B) {Hs : List (Finset V)} {g : Finset V}
    {x y : D} (hx : x ∈ N) :
    ReflTransGen (AStep M N Hs g) x y ↔ ReflTransGen (AStep M N (tHs M B Hs) g) x y :=
  rtg_congr_on (S := (· ∈ N)) (fun a b ha => aStep_tHs (hNB ha)) (fun a b h => h.1) hx

lemma rtg_hStep_tHs {B N : Finset D} (hNB : N ⊆ B) {Hs : List (Finset V)} {x y : D}
    (hx : x ∈ N) :
    ReflTransGen (HStep M N Hs) x y ↔ ReflTransGen (HStep M N (tHs M B Hs)) x y :=
  rtg_congr_on (S := (· ∈ N)) (fun a b ha => hStep_tHs (hNB ha)) (fun a b h => h.1) hx

lemma comp_tHs {B N : Finset D} (hNB : N ⊆ B) {Hs : List (Finset V)} {g : Finset V} {z : D}
    (hz : z ∈ N) : comp M N Hs g z = comp M N (tHs M B Hs) g z := by
  ext y
  rw [mem_comp, mem_comp, rtg_aStep_tHs hNB hz]

lemma cutH_tHs {B N : Finset D} (hNB : N ⊆ B) {Hs : List (Finset V)} {g : Finset V} :
    CutH M N Hs g ↔ CutH M N (tHs M B Hs) g := by
  unfold CutH
  refine exists_congr fun x => and_congr_right fun hx => exists_congr fun y =>
    and_congr_right fun hy => ?_
  rw [rtg_aStep_tHs hNB hx]

lemma conn_tHs {B N : Finset D} (hNB : N ⊆ B) {Hs : List (Finset V)}
    (hconn : ∀ x ∈ N, ∀ y ∈ N, ReflTransGen (HStep M N Hs) x y) :
    ∀ x ∈ N, ∀ y ∈ N, ReflTransGen (HStep M N (tHs M B Hs)) x y :=
  fun x hx y hy => (rtg_hStep_tHs hNB hx).1 (hconn x hx y hy)

/-- **`NoCut` sees only the touching holes** (for a connected `N ⊆ B`). -/
lemma noCut_tHs {B N : Finset D} (hNB : N ⊆ B) {Hs : List (Finset V)}
    (hconn : ∀ x ∈ N, ∀ y ∈ N, ReflTransGen (HStep M N Hs) x y) :
    NoCut M N Hs ↔ NoCut M N (tHs M B Hs) := by
  rw [noCut_iff, noCut_iff]
  constructor
  · intro h g hg hc
    exact h g (mem_tHs.1 hg).1 ((cutH_tHs hNB).2 hc)
  · intro h g hg hc
    obtain ⟨d, hd, hdg⟩ := cutH_touch hconn hc
    exact h g (mem_tHs.2 ⟨hg, d, hNB hd, hdg⟩) ((cutH_tHs hNB).1 hc)

/-- `find?` on a filtered list, when the dropped elements fail the predicate. -/
lemma find?_filter_eq {α : Type*} (p q q' : α → Bool) :
    ∀ (l : List α), (∀ a ∈ l, p a = false → q a = false) → (∀ a ∈ l, p a = true → q a = q' a) →
      l.find? q = (l.filter p).find? q'
  | [], _, _ => rfl
  | a :: l, h1, h2 => by
    have ih := find?_filter_eq p q q' l (fun b hb => h1 b (List.mem_cons_of_mem _ hb))
      (fun b hb => h2 b (List.mem_cons_of_mem _ hb))
    rw [List.find?_cons]
    cases hp : p a
    · rw [h1 a List.mem_cons_self hp, List.filter_cons_of_neg (by simp [hp])]
      exact ih
    · rw [List.filter_cons_of_pos hp, List.find?_cons, h2 a List.mem_cons_self hp]
      cases q' a
      · exact ih
      · rfl

open Classical in
/-- **The hole choice of `scChoiceE` sees only the touching holes.** -/
lemma scChoiceE_hole_tHs (sepF : SepFn M) (e : ℕ → D) (n : ℕ) (A W : ℕ) {B N : Finset D}
    (hNB : N ⊆ B) {Hs : List (Finset V)}
    (hconn : ∀ x ∈ N, ∀ y ∈ N, ReflTransGen (HStep M N Hs) x y) :
    (scChoiceE M sepF e n Hs A W).hole N = (scChoiceE M sepF e n (tHs M B Hs) A W).hole N := by
  show Hs.find? _ = (Hs.filter _).find? _
  refine find?_filter_eq _ _ _ Hs (fun g hg hp => ?_) (fun g hg hp => ?_)
  · simp only [decide_eq_false_iff_not] at hp ⊢
    intro hc
    obtain ⟨d, hd, hdg⟩ := cutH_touch hconn (show CutH M N Hs g from hc)
    exact hp ⟨d, hNB hd, hdg⟩
  · have := cutH_tHs (M := M) hNB (Hs := Hs) (g := g)
    unfold CutH at this
    simp only [this]

lemma scChoiceE_heavy_tHs (sepF : SepFn M) (e : ℕ → D) (n : ℕ) (A W : ℕ) {B N : Finset D}
    (hNB : N ⊆ B) {Hs : List (Finset V)} (g : Finset V) (ex : D → ℕ) :
    (scChoiceE M sepF e n Hs A W).heavy N g ex =
      (scChoiceE M sepF e n (tHs M B Hs) A W).heavy N g ex := by
  classical
  show findE e n _ = findE e n _
  congr 1
  exact filter_congr fun z hz => by rw [comp_tHs hNB hz]

lemma newHole_tHs {B : Finset D} {Hs : List (Finset V)} {a : D} (ha : a ∈ B) (C : Finset V) :
    M.tail a ∈ newHole Hs C ↔ M.tail a ∈ newHole (tHs M B Hs) C := by
  classical
  unfold newHole
  rw [mem_union, mem_union, mem_hunion, mem_hunion]
  refine or_congr_right ⟨fun ⟨H, hH, h⟩ => ⟨H, ?_, h⟩, fun ⟨H, hH, h⟩ => ⟨H, ?_, h⟩⟩
  · rw [List.mem_filter] at hH ⊢
    exact ⟨mem_tHs.2 ⟨hH.1, a, ha, h⟩, hH.2⟩
  · rw [List.mem_filter] at hH ⊢
    exact ⟨(mem_tHs.1 hH.1).1, hH.2⟩

lemma pruneI_tHs {B N K : Finset D} {Hs : List (Finset V)} {a₀ : D} (ha : a₀ ∈ B) (ρ : HPath M)
    (I : Finset (Finset D)) : pruneI Hs N K a₀ ρ I = pruneI (tHs M B Hs) N K a₀ ρ I := by
  unfold pruneI
  have h := newHole_tHs (M := M) (Hs := Hs) ha ρ.mverts
  by_cases h1 : M.tail a₀ ∈ newHole Hs ρ.mverts
  · simp only [h1, h.1 h1, ↓reduceIte]
  · have h2 : M.tail a₀ ∉ newHole (tHs M B Hs) ρ.mverts := fun h2 => h1 (h.2 h2)
    simp only [h1, h2, ↓reduceIte]

lemma cutCert_tHs {B N : Finset D} (hNB : N ⊆ B) {Hs : List (Finset V)} (g : Finset V) (a : D) :
    cutCert M Hs N g a = cutCert M (tHs M B Hs) N g a := by
  unfold cutCert
  congr 1
  exact image_congr fun z hz => comp_tHs hNB hz

/-- **A component off a hole of the list is connected.** -/
lemma conn_comp {N : Finset D} {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {g : Finset V}
    (hg : g ∈ Hs) {z : D} (hz : z ∈ N) :
    ∀ x ∈ comp M N Hs g z, ∀ y ∈ comp M N Hs g z,
      ReflTransGen (HStep M (comp M N Hs g z) Hs) x y := by
  intro x hx y hy
  have hgc := hClosed_of_mem hd hg
  have hzK : z ∈ comp M N Hs g z := self_mem_comp hz
  have h1 := rtg_comp_of_rtg (M := M) x (mem_comp.1 hx).2
  have h2 := rtg_comp_of_rtg (M := M) y (mem_comp.1 hy).2
  exact Relation.ReflTransGen.mono (fun a b (h : AStep M (comp M N Hs g z) Hs g a b) => h.hStep) _ _ ((rtg_symm_aStep hgc hzK h1).trans h2)

lemma comp_subset {N : Finset D} {Hs : List (Finset V)} {g : Finset V} {z : D} :
    comp M N Hs g z ⊆ N := fun y hy => (mem_comp.1 hy).1

open Classical in
/-- **`scertD` under `scChoiceE` sees only the holes touching `B`**: for a connected `N ⊆ B`, the
recursion with the holes `Hs` and with the touching holes `tHs B Hs` agree. -/
theorem scertD_tHs (sepF : SepFn M) (e : ℕ → D) (n : ℕ) (A W : ℕ) {B : Finset D}
    {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) :
    ∀ (k : ℕ) (N : Finset D) (τ : Perm D) (ex : D → ℕ), N.card = k → N ⊆ B →
      (∀ x ∈ N, ∀ y ∈ N, ReflTransGen (HStep M N Hs) x y) →
      scertD (scChoiceE M sepF e n Hs A W) Hs N τ ex =
        scertD (scChoiceE M sepF e n (tHs M B Hs) A W) (tHs M B Hs) N τ ex := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro N τ ex hk hNB hconn
    conv_lhs => rw [scertD]
    conv_rhs => rw [scertD]
    have hnc := noCut_tHs (M := M) hNB hconn
    by_cases h : NoCut M N Hs
    · have h' : NoCut M N (tHs M B Hs) := hnc.1 h
      simp only [h, h', ↓reduceIte]
      rfl
    have h' : ¬ NoCut M N (tHs M B Hs) := fun h' => h (hnc.2 h')
    simp only [h, h', ↓reduceIte]
    rw [scChoiceE_hole_tHs sepF e n A W hNB hconn]
    rcases hh : (scChoiceE M sepF e n (tHs M B Hs) A W).hole N with _ | g
    · rfl
    · have hgH : g ∈ Hs := by
        have h'' : (tHs M B Hs).find? _ = some g := hh
        exact (mem_tHs.1 (List.mem_of_find?_eq_some h'')).1
      simp only
      rw [scChoiceE_heavy_tHs sepF e n A W hNB g ex]
      rcases hz : (scChoiceE M sepF e n (tHs M B Hs) A W).heavy N g ex with _ | z
      · simp only
        have ha : (scChoiceE M sepF e n Hs A W).anchor N g =
            (scChoiceE M sepF e n (tHs M B Hs) A W).anchor N g := rfl
        rw [ha]
        rcases ha1 : (scChoiceE M sepF e n (tHs M B Hs) A W).anchor N g with _ | a₁
        · rfl
        · simp only [Option.some.injEq]
          exact cutCert_tHs hNB g a₁
      · have hzN : z ∈ N := (mem_filter.1 (findE_some hz)).1
        simp only
        rw [← comp_tHs hNB hzN]
        have ha : (scChoiceE M sepF e n Hs A W).anchor (comp M N Hs g z) g =
            (scChoiceE M sepF e n (tHs M B Hs) A W).anchor (comp M N Hs g z) g := rfl
        rw [ha]
        rcases ha0 : (scChoiceE M sepF e n (tHs M B Hs) A W).anchor (comp M N Hs g z) g
          with _ | a₀
        · rfl
        · have ha₀ : a₀ ∈ comp M N Hs g z := (mem_filter.1 (findE_some ha0)).1
          simp only
          by_cases hK : (comp M N Hs g z).card < N.card
          · simp only [hK, ↓reduceDIte]
            rw [ih _ (hk ▸ hK) (comp M N Hs g z) _ _ rfl (comp_subset.trans hNB)
              (conn_comp hd hgH hzN)]
            congr 1
            funext r
            rw [pruneI_tHs (hNB (comp_subset ha₀))]
          · simp only [hK, ↓reduceDIte]

/-- **The depth of the recursion with the touching holes is at most their number.** -/
theorem scDepth_tHs_le (sepF : SepFn M) (e : ℕ → D) (n : ℕ) (A W : ℕ) {B N : Finset D}
    (hNB : N ⊆ B) {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {τ : Perm D} (ex : D → ℕ)
    (hB : Stable (revPerm M) N) (hconn : ∀ x ∈ N, ∀ y ∈ N, ReflTransGen (HStep M N Hs) x y) :
    scDepth (scChoiceE M sepF e n (tHs M B Hs) A W) (tHs M B Hs) N τ ex ≤ (tHs M B Hs).length := by
  obtain ⟨h1, h2⟩ := scDepth_scChoiceE sepF e n (tHs M B Hs) A W
  exact (scDepth_le_nTouch (tHs_pairwise hd) _ h1 h2 ex hB (conn_tHs hNB hconn)).trans
    (by classical exact List.length_filter_le _ _)

end BKMNW

end PlanarFlow
