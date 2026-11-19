module

public import PlanarFlow.BKMNW.ExistCert
public import PlanarFlow.BKMNW.ExistSegs

/-!
# The split of a large piece

* `exists_two_groups`: items of weight at most `A`, of total at most `W` with `2 W ≤ 3 A`, split
  into two nonempty groups of weight at most `A`.
* `scert_lift_list`: a certificate of a split of the core of a piece lifts to the core with
  the pendant edges and the darts inside the holes attached, their weight first put on anchor
  darts (`scert_prune`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit Relation

/-- **Two groups**: items of weight at most `A` each, of total at most `W` with `2 W ≤ 3 A`, at
least two of them, split into two nonempty groups of weight at most `A` each. -/
lemma exists_two_groups {ι : Type*} [DecidableEq ι] (J : Finset ι) (ω : ι → ℕ) {A W : ℕ}
    (hJ : 2 ≤ J.card) (hω : ∀ i ∈ J, ω i ≤ A) (hW : ∑ i ∈ J, ω i ≤ W) (hAW : 2 * W ≤ 3 * A) :
    ∃ S ⊆ J, S.Nonempty ∧ (J \ S).Nonempty ∧ ∑ i ∈ S, ω i ≤ A ∧ ∑ i ∈ J \ S, ω i ≤ A := by
  classical
  obtain ⟨S, hS, hmax⟩ := (J.powerset.filter fun S => ∑ i ∈ S, ω i ≤ A).exists_max_image
    (fun S => ∑ i ∈ S, ω i) ⟨∅, by simp⟩
  simp only [mem_filter, mem_powerset] at hS hmax
  obtain ⟨hSJ, hSA⟩ := hS
  have hsplit : ∑ i ∈ S, ω i + ∑ i ∈ J \ S, ω i = ∑ i ∈ J, ω i := by
    rw [add_comm, sum_sdiff hSJ]
  -- the rest weighs at most `A`
  have hrest : ∑ i ∈ J \ S, ω i ≤ A := by
    by_contra hlt
    push Not at hlt
    have h3 : 3 * ∑ i ∈ S, ω i < W := by omega
    obtain ⟨i, hi, hpos⟩ : ∃ i ∈ J \ S, 0 < ω i := by
      by_contra h
      push Not at h
      have := sum_eq_zero (s := J \ S) (f := ω) fun i hi => Nat.le_zero.1 (h i hi)
      omega
    have hiJ := (mem_sdiff.1 hi).1
    have hiS := (mem_sdiff.1 hi).2
    by_cases hfit : ∑ j ∈ S, ω j + ω i ≤ A
    · have := hmax (insert i S) ⟨insert_subset hiJ hSJ, by rw [sum_insert hiS]; omega⟩
      rw [sum_insert hiS] at this; omega
    · have := hmax {i} ⟨singleton_subset_iff.2 hiJ, by simpa using hω i hiJ⟩
      simp only [sum_singleton] at this
      omega
  -- make both groups nonempty
  by_cases hS0 : S.Nonempty
  · by_cases hS1 : (J \ S).Nonempty
    · exact ⟨S, hSJ, hS0, hS1, hSA, hrest⟩
    · have hSeq : S = J := by
        rw [not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset] at hS1
        exact Subset.antisymm hSJ hS1
      obtain ⟨i, hi⟩ := hS0
      refine ⟨{i}, singleton_subset_iff.2 (hSeq ▸ hi), singleton_nonempty _, ?_, ?_, ?_⟩
      · rw [← card_pos, card_sdiff_of_subset (singleton_subset_iff.2 (hSeq ▸ hi)), card_singleton]
        omega
      · simpa using hω i (hSeq ▸ hi)
      · have := sum_le_sum_of_subset (f := ω) (sdiff_subset (s := J) (t := {i}))
        rw [← hSeq] at this ⊢; omega
  · rw [not_nonempty_iff_eq_empty] at hS0
    subst hS0
    rw [sdiff_empty] at hrest
    obtain ⟨i, hi⟩ : J.Nonempty := card_pos.1 (by omega)
    refine ⟨{i}, singleton_subset_iff.2 hi, singleton_nonempty _, ?_, by simpa using hω i hi, ?_⟩
    · rw [← card_pos, card_sdiff_of_subset (singleton_subset_iff.2 hi), card_singleton]; omega
    · exact (sum_le_sum_of_subset sdiff_subset).trans hrest

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

/-- The union of the first components of a list of pairs. -/
def lunion {β : Type*} (Ls : List (Finset D × β)) : Finset D := Ls.foldr (fun e acc => e.1 ∪ acc) ∅

lemma mem_lunion {β : Type*} {Ls : List (Finset D × β)} {x : D} :
    x ∈ lunion Ls ↔ ∃ e ∈ Ls, x ∈ e.1 := by
  induction Ls with
  | nil => simp [lunion]
  | cons e Ls ih =>
    simp only [lunion, List.foldr_cons, mem_union, List.mem_cons] at ih ⊢
    rw [ih]
    constructor
    · rintro (h | ⟨e', he', h⟩)
      · exact ⟨e, Or.inl rfl, h⟩
      · exact ⟨e', Or.inr he', h⟩
    · rintro ⟨e', rfl | he', h⟩
      · exact Or.inl h
      · exact Or.inr ⟨e', he', h⟩

/-- The extra weights moved to the anchors of a list of attached sets. -/
def lmoved (ex : D → ℕ) (Ls : List (Finset D × Finset V × D)) (d : D) : ℕ :=
  (Ls.map fun e => if d = e.2.2 then ∑ x ∈ e.1, (1 + ex x) else 0).sum

/-- **Attaching darts hanging at a vertex**: a certificate for `B`, with the weights of a list of
sets of darts (pendant edges, darts inside a hole) put on their anchors in `B`, lifts to a
certificate for `B` with the sets attached. Each set `E` hangs at a set `g` of vertices related by
the holes (a vertex off the holes, or a hole) at which `B` has the anchor dart, and every dart of
`E` leaves `g` or a vertex of degree one off the holes. -/
theorem scert_lift_list {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {Q : Finset V}
    (hQ : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQH : Disjoint (hunion Hs) Q) {A L : ℕ} :
    ∀ (Ls : List (Finset D × Finset V × D)) (B : Finset D) (ex : D → ℕ),
      Stable (revPerm M) B →
      (∀ e ∈ Ls, Stable (revPerm M) e.1 ∧ Disjoint e.1 B ∧ HClosed Hs e.2.1 ∧
        (∀ u ∈ e.2.1, ∀ v ∈ e.2.1, HRel Hs u v) ∧ e.2.2 ∈ B ∧ M.tail e.2.2 ∈ e.2.1 ∧
        (∀ d ∈ e.1, M.tail d ∈ e.2.1 ∨ M.tail d ∈ Q) ∧ ∑ d ∈ e.1, (1 + ex d) ≤ A) →
      Ls.Pairwise (fun e e' => Disjoint e.1 e'.1) →
      ∀ {Nρ : Finset D}, SCert M B Nρ Hs (fun d => ex d + lmoved ex Ls d) A L →
      SCert M (B ∪ lunion Ls) Nρ Hs ex A L := by
  intro Ls
  induction Ls with
  | nil =>
    intro B ex _ _ _ Nρ h
    simpa [lunion, lmoved] using h
  | cons e Ls ih =>
    intro B ex hB hLs hpw Nρ hc
    obtain ⟨hE, hEB, hgc, hgr, haB, hag, hEt, hEw⟩ := hLs e List.mem_cons_self
    have hpw' := List.pairwise_cons.1 hpw
    set ex₁ : D → ℕ := fun d => ex d + if d = e.2.2 then ∑ x ∈ e.1, (1 + ex x) else 0
      with hex₁
    have hsame : ∀ e' ∈ Ls, ∑ x ∈ e'.1, (1 + ex₁ x) = ∑ x ∈ e'.1, (1 + ex x) := by
      intro e' he'
      refine sum_congr rfl fun x hx => ?_
      have : x ≠ e.2.2 := fun h => by
        subst h
        exact disjoint_left.1 (hLs e' (List.mem_cons_of_mem _ he')).2.1 hx haB
      simp [ex₁, this]
    have hmv : ∀ d, ex₁ d + lmoved ex₁ Ls d = ex d + lmoved ex (e :: Ls) d := by
      intro d
      have : lmoved ex₁ Ls d = lmoved ex Ls d := by
        unfold lmoved
        congr 1
        refine List.map_congr_left fun e' he' => ?_
        rw [hsame e' he']
      rw [this]
      simp only [lmoved, List.map_cons, List.sum_cons, ex₁]
      ring
    have hc₁ : SCert M B Nρ Hs (fun d => ex₁ d + lmoved ex₁ Ls d) A L := by
      have : (fun d => ex₁ d + lmoved ex₁ Ls d) = fun d => ex d + lmoved ex (e :: Ls) d :=
        funext hmv
      rw [this]; exact hc
    have hK := ih B ex₁ hB (fun e' he' => by
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hLs e' (List.mem_cons_of_mem _ he')
      exact ⟨a1, a2, a3, a4, a5, a6, a7, by rw [hsame e' he']; exact a8⟩) hpw'.2 hc₁
    set K := B ∪ lunion Ls with hKdef
    have hEK : Disjoint e.1 K := by
      refine disjoint_union_right.2 ⟨hEB, disjoint_left.2 fun x hx hx' => ?_⟩
      obtain ⟨e', he', hx''⟩ := mem_lunion.1 hx'
      exact disjoint_left.1 (hpw'.1 e' he') hx hx''
    have hKs : Stable (revPerm M) K := by
      intro d hd
      rcases mem_union.1 hd with h | h
      · exact mem_union_left _ (hB d h)
      · obtain ⟨e', he', hx⟩ := mem_lunion.1 h
        exact mem_union_right _ (mem_lunion.2 ⟨e', he',
          (hLs e' (List.mem_cons_of_mem _ he')).1 d hx⟩)
    have hNK : (K ∪ e.1) \ K = e.1 := by
      rw [union_sdiff_left]; exact sdiff_eq_self_of_disjoint hEK
    have hrel : ∀ a b, HRel Hs (M.tail a) (M.tail b) → M.tail b ∈ Q → a = b := fun a b h hb =>
      hQ _ hb a b (hRel_eq_of_not_mem (fun h' => disjoint_left.1 hQH h' hb) h) rfl
    have hres := scert_prune (N := K ∪ e.1) (K := K) (A := A) (L := L) hd hgc hgr
      subset_union_left hKs
      (fun a ha b hab => by
        rcases mem_union.1 hab.1 with hb | hb
        · exact hb
        · exfalso
          rcases hab.2 with h | ⟨h, hag'⟩
          · exact disjoint_left.1 hEK hb (h ▸ hKs a ha)
          · rcases hEt b hb with hbg | hbQ
            · exact hag' (hgc _ hbg _ (hRel_symm h))
            · exact disjoint_left.1 hEK hb (hrel a b h hbQ ▸ ha))
      (fun a ha b hab => by
        rw [hNK] at ha ⊢
        rcases hab.2 with h | ⟨h, hag'⟩
        · exact h ▸ hE a ha
        · rcases hEt a ha with hag'' | haQ
          · exact absurd hag'' hag'
          · have := hrel b a (hRel_symm h) haQ
            exact this ▸ ha)
      (mem_union_left _ haB) hag ex (by rw [hNK]; exact hEw)
      (by rw [hNK]; exact hK)
    have he : B ∪ lunion (e :: Ls) = K ∪ e.1 := by
      simp only [lunion, List.foldr_cons, hKdef]
      ext x; simp only [mem_union]; tauto
    rw [he]; exact hres

/-! ### The children -/

/-- **A set closed under the steps avoiding a hole is connected** after contracting the holes, in a
connected piece map: every dart reaches the hole inside the set, or no dart leaves the hole and the
steps never pivot at it. -/
lemma hConn_of_closed {B L : Finset D} {Hs : List (Finset V)} {Y : Finset V} (hYH : Y ∈ Hs)
    (hYc : HClosed Hs Y) (hL : L ⊆ B) (hconn : ∀ x ∈ B, ∀ y ∈ B, ReflTransGen (HStep M B Hs) x y)
    (hcl : ∀ a ∈ L, ∀ b, AStep M B Hs Y a b → b ∈ L) :
    ∀ x ∈ L, ∀ y ∈ L, ReflTransGen (HStep M L Hs) x y := by
  by_cases hY : ∃ y₀ ∈ B, M.tail y₀ ∈ Y
  · obtain ⟨y₀, hy₀, hy₀Y⟩ := hY
    exact conn_of_closed hYH hYc hL hcl fun x hx => reach_of_conn hconn hy₀ hy₀Y (hL hx)
  · push Not at hY
    intro x hx y hy
    have key : ∀ z, ReflTransGen (HStep M B Hs) x z → z ∈ L ∧ ReflTransGen (HStep M L Hs) x z := by
      intro z hz
      induction hz with
      | refl => exact ⟨hx, .refl⟩
      | tail h1 hst ih =>
        rename_i b c
        obtain ⟨hb, ih⟩ := ih
        have hc : c ∈ L := hcl b hb c ⟨hst.1, hst.2.imp id fun e => ⟨e, hY b (hL hb)⟩⟩
        exact ⟨hc, ih.tail ⟨hc, hst.2⟩⟩
    exact (key y (hconn x (hL hx) y (hL hy))).2

variable (M) in
/-- The darts of a piece with no end among the vertices `Q` (the pendant vertices). -/
noncomputable def core (Q : Finset V) (P : Finset D) : Finset D := by
  classical exact P.filter fun d => M.tail d ∉ Q ∧ M.head d ∉ Q

lemma mem_core {Q : Finset V} {P : Finset D} {d : D} :
    d ∈ core M Q P ↔ d ∈ P ∧ M.tail d ∉ Q ∧ M.head d ∉ Q := by
  classical simp [core]

lemma core_mono {Q : Finset V} {P P' : Finset D} (h : P ⊆ P') : core M Q P ⊆ core M Q P' :=
  fun d hd => by rw [mem_core] at hd ⊢; exact ⟨h hd.1, hd.2⟩

lemma revClosed_core {Q : Finset V} {P : Finset D} (hP : RevClosed M P) :
    RevClosed M (core M Q P) := fun d hd => by
  rw [mem_core] at hd ⊢
  exact ⟨hP d hd.1, by rw [CombMap.tail_rev]; exact hd.2.2, by rw [CombMap.head_rev]; exact hd.2.1⟩

variable (M) in
/-- **The invariant of the large pieces**: the holes avoid the pendant vertices `Q`, and the core
of the piece is a piece map (`PieceInv`), connected after contracting its holes, whose faces are
small or around a hole (`FOK`). -/
def CInv (Q : Finset V) (P : Finset D) (Hs : List (Finset V)) : Prop :=
  Disjoint (hunion Hs) Q ∧ ∃ σ : Perm D, PieceInv M (core M Q P) Hs σ ∧
    FOK M σ (pdarts M (core M Q P) Hs) Hs ∧ HConn M (core M Q P) Hs

lemma hClosed_newHole_ch {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {C : Finset V} :
    HClosed (childHoles Hs C) (newHole Hs C) := by
  intro v hv w h
  rcases hRel_childHoles.1 h with h | h
  · rcases h with rfl | ⟨H, hH, h1, h2⟩
    · exact hv
    · rw [mem_newHole] at hv ⊢
      rcases hv with hv | ⟨H', hH', hm, hv⟩
      · exact Or.inr ⟨H, hH, not_disjoint_iff.2 ⟨v, h1, hv⟩, h2⟩
      · by_cases e : H = H'
        · subst e; exact Or.inr ⟨H, hH, hm, h2⟩
        · exact absurd hv (disjoint_left.1 (disjoint_of_pairwise hd hH hH' e) h1)
  · exact h.2

/-- A relation of the children's holes at a vertex off the new hole is one of the parent's. -/
lemma hRel_of_childHoles {Hs : List (Finset V)} {C : Finset V} {u v : V}
    (hu : u ∉ newHole Hs C) (h : HRel (childHoles Hs C) u v) : HRel Hs u v := by
  rcases hRel_childHoles.1 h with h | h
  · exact h
  · exact absurd h.1 hu

/-- **The children of a split**: a separator `π` of the core of a piece (a simple path through the
holes along darts of the piece map of the core, off the pendant vertices), with its parts off the
holes, and a partition of the piece into two parts `l`, `r` closed under reversal and under the
steps avoiding the new hole (at darts not inside the holes of the children), give a split
(`SplitOK`) whose children meet `CInv`. -/
theorem split_of_closed {S T Q : Finset V} {κ η : ℕ} (hSTQ : S ∪ T ⊆ Q) {P : Finset D}
    {Hs : List (Finset V)} (hP : PcOK M S T P Hs) (hI : CInv M Q P Hs) {π : HSep M}
    (hρ : π.path.Simple Hs) (hρB : ∀ e ∈ π.path.darts, e ∈ pdarts M (core M Q P) Hs)
    (hρQ : Disjoint π.path.mverts Q) (hseg : π.SegOK Hs)
    (hsegs : ∀ σ ∈ π.segs, (∀ e ∈ σ.darts, e ∈ P) ∧ ∃ x ∈ P, M.tail x = σ.p σ.k)
    (hshort : π.Short κ η P.card) {l r : Finset D} (hlr : l ∪ r = P) (hdisj : Disjoint l r)
    (hl0 : 0 < l.card) (hr0 : 0 < r.card) (hlrev : RevClosed M l) (hrrev : RevClosed M r)
    (hlcl : ∀ a ∈ l, ∀ b ∈ P, ¬ Inner M (childHoles Hs π.path.mverts) a →
      ¬ Inner M (childHoles Hs π.path.mverts) b → (b = M.rev a ∨
        (HRel Hs (M.tail a) (M.tail b) ∧ M.tail a ∉ newHole Hs π.path.mverts)) → b ∈ l)
    (hrcl : ∀ a ∈ r, ∀ b ∈ P, ¬ Inner M (childHoles Hs π.path.mverts) a →
      ¬ Inner M (childHoles Hs π.path.mverts) b → (b = M.rev a ∨
        (HRel Hs (M.tail a) (M.tail b) ∧ M.tail a ∉ newHole Hs π.path.mverts)) → b ∈ r) :
    SplitOK M S T κ η P Hs l r π ∧ CInv M Q l (childHoles Hs π.path.mverts) ∧
      CInv M Q r (childHoles Hs π.path.mverts) := by
  obtain ⟨hHQ, σ, hPI, hF, hcc⟩ := hI
  set ch := childHoles Hs π.path.mverts with hch
  set h'' := newHole Hs π.path.mverts with hh''
  have hd := hP.disj
  have hdch := pairwise_childHoles (C := π.path.mverts) hd
  have hh''ch : h'' ∈ ch := List.mem_append_right _ (List.mem_singleton_self _)
  have hh''c : HClosed ch h'' := hClosed_newHole_ch hd
  have hlP : l ⊆ P := hlr ▸ subset_union_left
  have hrP : r ⊆ P := hlr ▸ subset_union_right
  have hρP : ∀ e ∈ π.path.darts, e ∈ pdarts M P Hs := fun e he => by
    have := hρB e he
    rw [mem_pdarts] at this ⊢
    exact ⟨(mem_core.1 this.1).1, this.2⟩
  have hρQ' : Disjoint π.path.mverts (S ∪ T) := disjoint_of_subset_right hSTQ hρQ
  have hh''sub : ∀ v ∈ h'', v ∈ hunion Hs ∪ π.path.mverts := fun v hv => by
    rcases mem_newHole.1 hv with h | ⟨H, hH, -, h⟩
    · exact mem_union_right _ h
    · exact mem_union_left _ (subset_hunion hH h)
  -- a dart leaving a vertex off the holes of the children is not inside one
  have hnin : ∀ d : D, M.tail d ∉ hunion ch → ¬ Inner M ch d := fun d hd h => by
    obtain ⟨H, hH, h1, -⟩ := h; exact hd (subset_hunion hH h1)
  -- the pieces of the children: connected after contracting their holes
  have hconnP : HConn M P ch := hP.conn.coarse (coarse_childHoles _ _) hdch
  have hconnC : HConn M (core M Q P) ch := hcc.coarse (coarse_childHoles _ _) hdch
  have hstep : ∀ {X B : Finset D}, X ⊆ P → (∀ a ∈ X, ∀ b ∈ P, ¬ Inner M ch a → ¬ Inner M ch b →
      (b = M.rev a ∨ (HRel Hs (M.tail a) (M.tail b) ∧ M.tail a ∉ h'')) → b ∈ X) →
      B ⊆ P → ∀ a ∈ pdarts M X ch, ∀ b, AStep M (pdarts M B ch) ch h'' a b →
        b ∈ pdarts M X ch := by
    intro X B hX hXcl hB a ha b hab
    have hbB := hab.1
    rw [mem_pdarts] at ha hbB ⊢
    refine ⟨hXcl a ha.1 b (hB hbB.1) ha.2 hbB.2 ?_, hbB.2⟩
    rcases hab.2 with e | ⟨e, h⟩
    · exact Or.inl e
    · exact Or.inr ⟨hRel_of_childHoles h e, h⟩
  have hconn_child : ∀ {X : Finset D}, X ⊆ P → (∀ a ∈ X, ∀ b ∈ P, ¬ Inner M ch a →
      ¬ Inner M ch b → (b = M.rev a ∨ (HRel Hs (M.tail a) (M.tail b) ∧ M.tail a ∉ h'')) →
      b ∈ X) → HConn M X ch := by
    intro X hX hXcl
    exact hConn_of_closed hh''ch hh''c (fun d hd => by
      rw [mem_pdarts] at hd ⊢; exact ⟨hX hd.1, hd.2⟩) hconnP (hstep hX hXcl le_rfl)
  have hconn_core : ∀ {X : Finset D}, X ⊆ P → (∀ a ∈ X, ∀ b ∈ P, ¬ Inner M ch a →
      ¬ Inner M ch b → (b = M.rev a ∨ (HRel Hs (M.tail a) (M.tail b) ∧ M.tail a ∉ h'')) →
      b ∈ X) → HConn M (core M Q X) ch := by
    intro X hX hXcl
    have hXc : core M Q X ⊆ core M Q P := core_mono hX
    refine hConn_of_closed hh''ch hh''c (fun d hd => by
      rw [mem_pdarts] at hd ⊢; exact ⟨hXc hd.1, hd.2⟩) hconnC ?_
    intro a ha b hab
    have hbB := hab.1
    rw [mem_pdarts] at ha hbB ⊢
    have hbc := mem_core.1 hbB.1
    refine ⟨mem_core.2 ⟨hXcl a (mem_core.1 ha.1).1 b hbc.1 ha.2 hbB.2 ?_, hbc.2⟩, hbB.2⟩
    rcases hab.2 with e | ⟨e, h⟩
    · exact Or.inl e
    · exact Or.inr ⟨hRel_of_childHoles h e, h⟩
  -- the invariant of a child
  have hinv : ∀ {X : Finset D}, X ⊆ P → RevClosed M X → (∀ a ∈ X, ∀ b ∈ P,
      ¬ Inner M ch a → ¬ Inner M ch b →
      (b = M.rev a ∨ (HRel Hs (M.tail a) (M.tail b) ∧ M.tail a ∉ h'')) → b ∈ X) →
      CInv M Q X ch := by
    intro X hX hXr hXcl
    have hXc : core M Q X ⊆ core M Q P := core_mono hX
    have hXcr : RevClosed M (core M Q X) := revClosed_core hXr
    refine ⟨by rw [hunion_childHoles]; exact disjoint_union_left.2 ⟨hHQ, hρQ⟩, _,
      hPI.child hd hρ hρB hXc hXcr, ?_, hconn_core hX hXcl⟩
    -- the faces of the child piece map
    classical
    set Lv : Finset V := univ.filter fun v => v ∉ h'' ∧
      ∃ d ∈ X, d ∈ pdarts M (core M Q P) Hs ∧ HRel Hs (M.tail d) v with hLv
    have hmemLv : ∀ v, v ∈ Lv ↔ v ∉ h'' ∧
        ∃ d ∈ X, d ∈ pdarts M (core M Q P) Hs ∧ HRel Hs (M.tail d) v := fun v => by
      simp [Lv]
    have hBnin : ∀ d ∈ pdarts M (core M Q P) Hs, (M.tail d ∉ h'' ∨ M.head d ∉ h'') →
        ¬ Inner M ch d := by
      intro d hd hne h
      obtain ⟨H, hH, h1, h2⟩ := h
      rcases List.mem_append.1 hH with hH | hH
      · exact (mem_pdarts.1 hd).2 ⟨H, (List.mem_filter.1 hH).1, h1, h2⟩
      · rw [List.mem_singleton.1 hH] at h1 h2; tauto
    -- a dart of the core with an end in `Lv` lies in `X`
    have hinX : ∀ d ∈ pdarts M (core M Q P) Hs, M.tail d ∈ Lv → d ∈ X := by
      intro d hdB0 hdL
      obtain ⟨hdh, d', hd'X, hd'B, hr⟩ := (hmemLv _).1 hdL
      have hd'h : M.tail d' ∉ h'' := fun h => hdh (hClosed_newHole hd hρ _ h _ hr)
      exact hXcl d' hd'X d (mem_core.1 (mem_pdarts.1 hdB0).1).1 (hBnin d' hd'B (Or.inl hd'h))
        (hBnin d hdB0 (Or.inl hdh)) (Or.inr ⟨hr, hd'h⟩)
    have hBrev : ∀ d ∈ pdarts M (core M Q P) Hs, M.rev d ∈ pdarts M (core M Q P) Hs :=
      fun d hd => stable_pdarts (revClosed_core hP.rev) Hs d hd
    refine FOK.child hPI hd hρ hρB hF hXcr (fun d hd => mem_sdiff.2
      ⟨pdarts_childHoles_subset hXc hd, fun hdρ => ?_⟩) (Lv := Lv) ?_ ?_ ?_
    · rw [List.mem_toFinset] at hdρ
      obtain ⟨h1, h2⟩ := π.path.ends_mem hdρ
      exact (mem_pdarts.1 hd).2 ⟨h'', hh''ch, subset_newHole h1, subset_newHole h2⟩
    · intro a ha b hab
      obtain ⟨hah, d, hdX, hdB, hr⟩ := (hmemLv a).1 ha
      have hbh : b ∉ h'' := fun h => hah (hh''c _ h _ (hRel_symm' hab))
      exact (hmemLv b).2 ⟨hbh, d, hdX, hdB, hRel_trans' hd hr (hRel_of_childHoles hah hab)⟩
    · intro d hd ht hh
      constructor
      · intro hL
        have hdX := hinX d hd hL
        exact (hmemLv _).2 ⟨hh, M.rev d, hXr d hdX, hBrev d hd, by
          rw [CombMap.tail_rev]; exact Or.inl rfl⟩
      · intro hL
        have hrX := hinX (M.rev d) (hBrev d hd) (by rw [CombMap.tail_rev]; exact hL)
        have hdX : d ∈ X := by have := hXr _ hrX; rwa [M.rev_rev] at this
        exact (hmemLv _).2 ⟨ht, d, hdX, hd, Or.inl rfl⟩
    · intro d hd
      have hdB := (mem_sdiff.1 hd).1
      rw [mem_pdarts, mem_core]
      constructor
      · rintro ⟨⟨hdX, -⟩, hni⟩
        by_cases ht : M.tail d ∈ h''
        · have hh : M.head d ∉ h'' := fun h => hni ⟨h'', hh''ch, ht, h⟩
          refine Or.inr ((hmemLv _).2 ⟨hh, M.rev d, hXr d hdX, hBrev d hdB, ?_⟩)
          rw [CombMap.tail_rev]; exact Or.inl rfl
        · exact Or.inl ((hmemLv _).2 ⟨ht, d, hdX, hdB, Or.inl rfl⟩)
      · intro hL
        have hdX : d ∈ X := by
          rcases hL with hL | hL
          · exact hinX d hdB hL
          · have hrX := hinX (M.rev d) (hBrev d hdB) (by rw [CombMap.tail_rev]; exact hL)
            have := hXr _ hrX; rwa [M.rev_rev] at this
        have hdc := mem_core.1 (mem_pdarts.1 hdB).1
        refine ⟨⟨hdX, hdc.2⟩, hBnin d hdB ?_⟩
        rcases hL with hL | hL
        · exact Or.inl ((hmemLv _).1 hL).1
        · exact Or.inr ((hmemLv _).1 hL).1
  refine ⟨⟨hlr, hdisj, hl0, hr0, ?_, hρQ', hseg, hρ, hρP, fun σ' hσ' => hsegs σ' hσ', hshort,
    hlrev, hrrev, hconn_child hlP hlcl, hconn_child hrP hrcl⟩, hinv hlP hlrev hlcl,
    hinv hrP hrrev hrcl⟩
  -- the vertices shared by the children
  intro v hv
  obtain ⟨⟨a, ha, rfl⟩, ⟨b, hb, e⟩⟩ := mem_bd.1 hv
  by_contra hno
  have hvH : M.tail a ∉ hunion Hs ∪ π.path.mverts := fun h => hno (mem_union_right _ h)
  have hvh : M.tail a ∉ h'' := fun h => hvH (hh''sub _ h)
  have hvch : M.tail a ∉ hunion ch := by rw [hunion_childHoles]; exact hvH
  have hbl := hlcl a ha b (hrP hb) (hnin a hvch) (hnin b (e ▸ hvch))
    (Or.inr ⟨by rw [e]; exact Or.inl rfl, hvh⟩)
  exact disjoint_left.1 hdisj hbl hb

end BKMNW

end PlanarFlow
