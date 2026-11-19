module

public import PlanarFlow.BKMNW.ExistCertD

/-!
# The certificate of a piece map as a function of its inputs

`exists_scert` (balanced splits of piece maps, by recursion on the number of darts: pruning at a
cut-vertex hole with a heavy component, a cut at a hole, Miller's theorem on a piece map without
cut-vertex holes) with every choice made by given functions (`ScChoice`): the separator of
Miller's theorem, a cut-vertex hole, a dart of a heavy component, a dart leaving a hole.

* `cutCert`, `pruneI`: the explicit certificates of `scert_cut` and `scert_prune`
  (`scert_cut'`, `scert_prune'`).
* **`scertD`**: the certificate as a (well-founded) recursive function of the piece map, the
  rotation and the extra weights, given the choice functions.
* `ScChoice.OK`: the specification of the choice functions (on piece maps only).
* **`scertD_spec`**: under the hypotheses of `exists_scert`, `scertD` returns a certificate
  (`SCertOf`). `exists_scChoice_ok`: choice functions meeting the specification exist.
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
/-- The certificate of a cut at the hole `g` through the tail of `x₀`: the one-vertex path and
the components off the hole. -/
noncomputable def cutCert (Hs : List (Finset V)) (N : Finset D) (g : Finset V) (x₀ : D) :
    HPath M × Finset (Finset D) :=
  ((SPath.point (M' := M) x₀ (M.tail x₀)).toH, N.image (comp M N Hs g))

/-- The items of a pruned certificate: the deleted darts `N \ K` form an item when the anchor
`a₀` lies on the new hole, and join the item of `a₀` otherwise. -/
def pruneI (Hs : List (Finset V)) (N K : Finset D) (a₀ : D) (ρ : HPath M)
    (I : Finset (Finset D)) : Finset (Finset D) :=
  if M.tail a₀ ∈ newHole Hs ρ.mverts then insert (N \ K) I
  else insert ((I.filter (a₀ ∈ ·)).biUnion id ∪ (N \ K)) (I.filter (a₀ ∉ ·))

lemma biUnion_filter_mem {I : Finset (Finset D)} (hdisj : ∀ X ∈ I, ∀ Y ∈ I, X ≠ Y → Disjoint X Y)
    {X₀ : Finset D} (hX₀ : X₀ ∈ I) {a : D} (ha : a ∈ X₀) : (I.filter (a ∈ ·)).biUnion id = X₀ := by
  have : I.filter (a ∈ ·) = {X₀} := by
    ext X
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hX, haX⟩
      by_contra hne
      exact disjoint_left.1 (hdisj X hX X₀ hX₀ hne) haX ha
    · rintro rfl; exact ⟨hX₀, ha⟩
  rw [this, singleton_biUnion]; rfl

lemma filter_not_mem_eq_erase {I : Finset (Finset D)}
    (hdisj : ∀ X ∈ I, ∀ Y ∈ I, X ≠ Y → Disjoint X Y)
    {X₀ : Finset D} (hX₀ : X₀ ∈ I) {a : D} (ha : a ∈ X₀) : I.filter (a ∉ ·) = I.erase X₀ := by
  ext X
  simp only [mem_filter, mem_erase]
  constructor
  · rintro ⟨hX, haX⟩; exact ⟨fun h => haX (h ▸ ha), hX⟩
  · rintro ⟨hne, hX⟩
    exact ⟨hX, fun haX => disjoint_left.1 (hdisj X hX X₀ hX₀ hne) haX ha⟩

/-- **`scert_cut` with the witnesses named**: the path of the one vertex `tail x₀` of the hole and
the components off the hole. -/
theorem scert_cut' {N : Finset D} {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint)
    {g : Finset V} (hg : g ∈ Hs) {x₀ : D} (hx₀ : x₀ ∈ N)
    (hx₀g : M.tail x₀ ∈ g) (ex : D → ℕ) {A L : ℕ}
    (hlight : ∀ x ∈ N, wtY M ex g (comp M N Hs g x) ≤ A) (hL : 1 ≤ L) :
    SCertOf M N N Hs ex A L (cutCert M Hs N g x₀).1 (cutCert M Hs N g x₀).2 := by
  show SCertOf M N N Hs ex A L (SPath.point (M' := M) x₀ (M.tail x₀)).toH (N.image (comp M N Hs g))
  classical
  have hgc := hClosed_of_mem hd hg
  set ρ := (SPath.point (M' := M) x₀ (M.tail x₀)).toH with hρ
  have hm : ρ.mverts = {M.tail x₀} := HPath.toH_point_mverts x₀ _
  have hh : newHole Hs ρ.mverts = g := by rw [hm]; exact newHole_singleton hd hg hx₀g
  refine ⟨⟨fun j hj => absurd hj (Nat.not_lt_zero _),
    fun i hi j hj _ => by simp [ρ, SPath.toH, SPath.point] at hi hj; omega⟩, fun e he => ?_,
    by simp [ρ, SPath.toH, SPath.point]; omega, ⟨x₀, hx₀, rfl⟩, ?_, ?_, ?_, ?_⟩
  · simp [ρ, SPath.toH_darts, SPath.point_darts'] at he
  · intro X hX Y hY hXY
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hX
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hY
    exact comp_disjoint hgc hx hy hXY
  · intro X hX
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hX
    refine ⟨fun y hy => (mem_comp.1 hy).1, fun a ha b hab => ?_⟩
    rw [hh] at hab
    exact comp_closed ha hab
  · intro d hd _
    exact ⟨comp M N Hs g d, mem_image_of_mem _ hd, self_mem_comp hd⟩
  · intro X hX
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hX
    rw [hh]; exact hlight x hx


/-- **`scert_prune` with the witnesses named**: the same path, and the items `pruneI`. -/
theorem scert_prune' {N K : Finset D} {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint)
    {g : Finset V} (hgc : HClosed Hs g) (hgr : ∀ u ∈ g, ∀ v ∈ g, HRel Hs u v) (hKN : K ⊆ N)
    (hK : Stable (revPerm M) K) (hcl : ∀ a ∈ K, ∀ b, AStep M N Hs g a b → b ∈ K)
    (hRcl : ∀ a ∈ N \ K, ∀ b, AStep M N Hs g a b → b ∈ N \ K)
    {a₀ : D} (ha₀ : a₀ ∈ K) (ha₀g : M.tail a₀ ∈ g) (ex : D → ℕ) {A L : ℕ}
    (hlight : ∑ d ∈ N \ K, (1 + ex d) ≤ A)
    {Nρ : Finset D} {ρ : HPath M} {I : Finset (Finset D)}
    (hc : SCertOf M K Nρ Hs (fun d => ex d + if d = a₀ then ∑ d ∈ N \ K, (1 + ex d) else 0) A L
      ρ I) :
    SCertOf M N Nρ Hs ex A L ρ (pruneI Hs N K a₀ ρ I) := by
  classical
  obtain ⟨hs, hdar, hlen, htch, hdisj, hcls, hcov, hwt⟩ := hc
  unfold pruneI
  set h'' := newHole Hs ρ.mverts with hh''
  set R := N \ K with hR
  set T := ∑ d ∈ R, (1 + ex d) with hT
  set ex' : D → ℕ := fun d => ex d + if d = a₀ then T else 0 with hex'
  have hhc := hClosed_newHole hd hs
  have hexle : ∀ d, ex d ≤ ex' d := fun d => by simp only [ex']; omega
  -- a step from `K` to the deleted darts pivots at `g`
  have hF1 : ∀ a ∈ K, ∀ b ∈ R, AStep M N Hs h'' a b → M.tail a ∈ g ∧ M.tail a ∉ h'' := by
    intro a ha b hb hab
    rcases hab.2 with e | ⟨e, hah⟩
    · exact absurd (e ▸ hK a ha) (mem_sdiff.1 hb).2
    · refine ⟨?_, hah⟩
      by_contra hag
      exact (mem_sdiff.1 hb).2 (hcl a ha b ⟨hab.1, Or.inr ⟨e, hag⟩⟩)
  have hKstep : ∀ a b, b ∈ K → AStep M N Hs h'' a b → AStep M K Hs h'' a b :=
    fun a b hb hab => ⟨hb, hab.2⟩
  have hRK : Disjoint R K := disjoint_sdiff_self_left
  by_cases hgh : M.tail a₀ ∈ h''
  · -- the hole `g` is on the separator: the deleted darts form an item
    have hgsub : ∀ v ∈ g, v ∈ h'' := fun v hv => hhc _ hgh _ (hgr _ ha₀g v hv)
    simp only [hgh, ↓reduceIte]
    refine ⟨hs, hdar, hlen, htch, ?_, ?_, ?_, ?_⟩
    · intro X hX Y hY hXY
      rcases mem_insert.1 hX with rfl | hX <;> rcases mem_insert.1 hY with rfl | hY
      · exact absurd rfl hXY
      · exact disjoint_of_subset_right (hcls Y hY).1 hRK
      · exact (disjoint_of_subset_right (hcls X hX).1 hRK).symm
      · exact hdisj X hX Y hY hXY
    · intro X hX
      rcases mem_insert.1 hX with rfl | hX
      · refine ⟨sdiff_subset, fun a ha b hab => ?_⟩
        rcases hab.2 with e | ⟨e, hah⟩
        · exact hRcl a ha b ⟨hab.1, Or.inl e⟩
        · exact hRcl a ha b ⟨hab.1, Or.inr ⟨e, fun h => hah (hgsub _ h)⟩⟩
      · refine ⟨(hcls X hX).1.trans hKN, fun a ha b hab => ?_⟩
        have haK := (hcls X hX).1 ha
        by_cases hbK : b ∈ K
        · exact (hcls X hX).2 a ha b (hKstep a b hbK hab)
        · have := hF1 a haK b (mem_sdiff.2 ⟨hab.1, hbK⟩) hab
          exact absurd (hgsub _ this.1) this.2
    · intro d hdN hnot
      by_cases hdK : d ∈ K
      · obtain ⟨X, hX, hdX⟩ := hcov d hdK hnot
        exact ⟨X, mem_insert_of_mem hX, hdX⟩
      · exact ⟨R, mem_insert_self _ _, mem_sdiff.2 ⟨hdN, hdK⟩⟩
    · intro X hX
      rcases mem_insert.1 hX with rfl | hX
      · exact (wtY_le ex h'' _).trans hlight
      · exact (wtY_mono hexle h'' X).trans (hwt X hX)
  · -- the deleted darts join the item of `g`
    have hgoff : ∀ v ∈ g, v ∉ h'' := fun v hv h =>
      hgh (hhc _ h _ (hgr v hv _ ha₀g))
    obtain ⟨X₀, hX₀, ha₀X⟩ := hcov a₀ ha₀ fun h => hgh h.1
    have hF3 : ∀ a ∈ K, M.tail a ∈ g → a ∈ X₀ := fun a ha hag =>
      (hcls X₀ hX₀).2 a₀ ha₀X a ⟨ha, Or.inr ⟨hgr _ ha₀g _ hag, hgh⟩⟩
    have hXX : ∀ X ∈ I, X ≠ X₀ → ∀ a ∈ X, M.tail a ∉ g := fun X hX hne a ha hag =>
      disjoint_left.1 (hdisj X hX X₀ hX₀ hne) ha (hF3 a ((hcls X hX).1 ha) hag)
    simp only [hgh, ↓reduceIte]
    rw [biUnion_filter_mem hdisj hX₀ ha₀X, filter_not_mem_eq_erase hdisj hX₀ ha₀X]
    refine ⟨hs, hdar, hlen, htch, ?_, ?_, ?_, ?_⟩
    · intro X hX Y hY hXY
      have hside : ∀ Z ∈ I.erase X₀, Disjoint (X₀ ∪ R) Z := fun Z hZ => by
        obtain ⟨hZ0, hZ⟩ := mem_erase.1 hZ
        exact disjoint_union_left.2 ⟨(hdisj Z hZ X₀ hX₀ hZ0).symm,
          disjoint_of_subset_right (hcls Z hZ).1 hRK⟩
      rcases mem_insert.1 hX with rfl | hX <;> rcases mem_insert.1 hY with rfl | hY
      · exact absurd rfl hXY
      · exact hside Y hY
      · exact (hside X hX).symm
      · exact hdisj X (mem_erase.1 hX).2 Y (mem_erase.1 hY).2 hXY
    · intro X hX
      rcases mem_insert.1 hX with rfl | hX
      · refine ⟨union_subset ((hcls X₀ hX₀).1.trans hKN) sdiff_subset, fun a ha b hab => ?_⟩
        by_cases hbK : b ∈ K
        · rcases mem_union.1 ha with ha | ha
          · exact mem_union_left _ ((hcls X₀ hX₀).2 a ha b (hKstep a b hbK hab))
          · -- from the deleted darts into `K`: the pivot is in `g`
            rcases hab.2 with e | ⟨e, hah⟩
            · exact absurd hbK (mem_sdiff.1 (hRcl a ha b ⟨hab.1, Or.inl e⟩)).2
            · by_cases hag : M.tail a ∈ g
              · exact mem_union_left _ (hF3 b hbK (hgc _ hag _ e))
              · exact absurd hbK (mem_sdiff.1 (hRcl a ha b ⟨hab.1, Or.inr ⟨e, hag⟩⟩)).2
        · exact mem_union_right _ (mem_sdiff.2 ⟨hab.1, hbK⟩)
      · obtain ⟨hX0, hX⟩ := mem_erase.1 hX
        refine ⟨(hcls X hX).1.trans hKN, fun a ha b hab => ?_⟩
        by_cases hbK : b ∈ K
        · exact (hcls X hX).2 a ha b (hKstep a b hbK hab)
        · exact absurd (hF1 a ((hcls X hX).1 ha) b (mem_sdiff.2 ⟨hab.1, hbK⟩) hab).1
            (hXX X hX hX0 a ha)
    · intro d hdN hnot
      by_cases hdK : d ∈ K
      · obtain ⟨X, hX, hdX⟩ := hcov d hdK hnot
        by_cases e : X = X₀
        · exact ⟨X₀ ∪ R, mem_insert_self _ _, mem_union_left _ (e ▸ hdX)⟩
        · exact ⟨X, mem_insert_of_mem (mem_erase.2 ⟨e, hX⟩), hdX⟩
      · exact ⟨X₀ ∪ R, mem_insert_self _ _, mem_union_right _ (mem_sdiff.2 ⟨hdN, hdK⟩)⟩
    · intro X hX
      rcases mem_insert.1 hX with rfl | hX
      · have hdis : Disjoint X₀ R := (disjoint_of_subset_left (hcls X₀ hX₀).1 hRK.symm)
        rw [wtY, sum_union hdis, ← wtY, ← wtY]
        have h1 : wtY M ex' h'' X₀ = wtY M ex h'' X₀ + T := by
          simp only [wtY, ex']
          rw [show (∑ d ∈ X₀, (1 + if M.tail d ∈ h'' then 0 else ex d + if d = a₀ then T else 0))
              = ∑ d ∈ X₀, ((1 + if M.tail d ∈ h'' then 0 else ex d) +
                if d = a₀ then T else 0) from sum_congr rfl fun d hd => by
                  split_ifs with h1 h2 <;> simp_all <;> omega]
          rw [sum_add_distrib, sum_ite_eq' X₀ a₀]; simp [ha₀X]
        have h2 := wtY_le (M := M) ex h'' R
        have h3 : wtY M ex' h'' X₀ ≤ A := hwt X₀ hX₀
        show wtY M ex h'' X₀ + wtY M ex h'' R ≤ A
        omega
      · exact (wtY_mono hexle h'' X).trans (hwt X (mem_erase.1 hX).2)


lemma SCertOf.mono {N Nρ : Finset D} {Hs : List (Finset V)} {ex : D → ℕ} {A L L' : ℕ}
    {ρ : HPath M} {I : Finset (Finset D)} (h : SCertOf M N Nρ Hs ex A L ρ I) (hL : L ≤ L') :
    SCertOf M N Nρ Hs ex A L' ρ I := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, h3.trans hL, h4⟩

lemma SCertOf.mono_ρ {N Nρ Nρ' : Finset D} {Hs : List (Finset V)} {ex : D → ℕ} {A L : ℕ}
    {ρ : HPath M} {I : Finset (Finset D)} (h : SCertOf M N Nρ Hs ex A L ρ I) (hN : Nρ ⊆ Nρ') :
    SCertOf M N Nρ' Hs ex A L ρ I := by
  obtain ⟨h1, h2, h3, ⟨x, hx, e⟩, h4⟩ := h
  exact ⟨h1, fun e he => hN (h2 e he), h3, ⟨x, hN hx, e⟩, h4⟩

variable (M) in
/-- **The choice functions of the certificate recursion**: a separator of the stellar subdivision
of a piece map (for the extra weights `ex`), a cut-vertex hole of a piece, a dart with a heavy
component off a hole, a dart of a set leaving a hole. -/
structure ScChoice where
  /-- Miller's separator of the stellar subdivision of the piece map. -/
  sep : ∀ (N : Finset D) (τ : Perm D) (hσ : Stable τ N) (hB : Stable (revPerm M) N)
    (ex : D → ℕ), Option ((psep M hσ hB).stellar.SCycle × Finset (psep M hσ hB).stellar.Face)
  /-- A hole that is a cut vertex. -/
  hole : Finset D → Option (Finset V)
  /-- A dart whose component off the hole is heavy. -/
  heavy : Finset D → Finset V → (D → ℕ) → Option D
  /-- A dart of the set leaving the hole. -/
  anchor : Finset D → Finset V → Option D

open Classical in
/-- **The certificate of a piece map, as a function** of the darts `N`, the rotation `τ` and the
extra weights `ex`, given the choice functions: Miller's separator (`scert_core'`) if no hole is
a cut vertex; otherwise at the chosen cut-vertex hole `g`, the recursion on the chosen heavy
component `K` with the rest pruned (`scert_prune'`), or the cut at `g` (`scert_cut'`) if no
component is heavy. -/
noncomputable def scertD (ch : ScChoice M) (Hs : List (Finset V)) (N : Finset D) (τ : Perm D)
    (ex : D → ℕ) : Option (HPath M × Finset (Finset D)) :=
  if NoCut M N Hs then
    (if h : Stable τ N ∧ Stable (revPerm M) N then
      (ch.sep N τ h.1 h.2 ex).map fun r => (corePath h.1 h.2 r.1,
        {sideItem h.1 h.2 (coreI h.1 h.2 r.1 r.2), sideItem h.1 h.2 (coreO h.1 h.2 r.1 r.2)})
    else none)
  else
    match ch.hole N with
    | none => none
    | some g =>
      match ch.heavy N g ex with
      | some z =>
        match ch.anchor (comp M N Hs g z) g with
        | none => none
        | some a₀ =>
          if hK : (comp M N Hs g z).card < N.card then
            (scertD ch Hs (comp M N Hs g z) (ret τ (comp M N Hs g z))
              (fun d => ex d + if d = a₀ then ∑ d ∈ N \ comp M N Hs g z, (1 + ex d) else 0)).map
              fun r => (r.1, pruneI Hs N (comp M N Hs g z) a₀ r.1 r.2)
          else none
      | none =>
        match ch.anchor N g with
        | none => none
        | some a₁ => some (cutCert M Hs N g a₁)
termination_by N.card

open Classical PlanarSeparator.Map in
/-- **The specification of the choice functions** (for the holes `Hs` and the weight bounds `A`,
`W`), only on the inputs where they are used: a separator meeting the natural weight bounds of
`exists_core_cycle'` on nonempty piece maps without cut-vertex holes; a cut-vertex hole when there
is one; a dart of a heavy component (weight above `W - A`) exactly when there is one; a dart of
the set leaving the hole when there is one. -/
structure ScChoice.OK (ch : ScChoice M) (Hs : List (Finset V)) (A W : ℕ) : Prop where
  sep : ∀ (N : Finset D) (τ : Perm D) (hN : PMap M N Hs τ) (ex : D → ℕ), N.Nonempty →
    NoCut M N Hs → ∃ C Z, ch.sep N τ hN.stable hN.rev ex = some (C, Z) ∧
      C.k ≤ 6 * Nat.sqrt (Fintype.card (SVert τ N) +
        Fintype.card (psep M hN.stable hN.rev).Face) + 4 ∧
      IsCycleSep C Z (sideIn C Z) (sideOut C Z) ∧
      3 * ∑ y ∈ sideIn C Z, coreWt hN.stable hN.rev (fun _ => 1) (coreExW τ N ex) y ≤
        2 * (∑ _x : SDart N, 1 + ∑ q, coreExW τ N ex q) + 2 ∧
      3 * ∑ y ∈ sideOut C Z, coreWt hN.stable hN.rev (fun _ => 1) (coreExW τ N ex) y ≤
        2 * (∑ _x : SDart N, 1 + ∑ q, coreExW τ N ex q) + 2
  hole : ∀ N : Finset D, ¬ NoCut M N Hs → ∃ g, ch.hole N = some g ∧ g ∈ Hs ∧
    ∃ x ∈ N, ∃ y ∈ N, M.tail x ∉ g ∧ M.tail y ∉ g ∧ ¬ ReflTransGen (AStep M N Hs g) x y
  heavy_some : ∀ (N : Finset D) (g : Finset V) (ex : D → ℕ) (z : D), ch.heavy N g ex = some z →
    z ∈ N ∧ W < A + ∑ d ∈ comp M N Hs g z, (1 + ex d)
  heavy_none : ∀ (N : Finset D) (g : Finset V) (ex : D → ℕ), ch.heavy N g ex = none →
    ∀ z ∈ N, A + ∑ d ∈ comp M N Hs g z, (1 + ex d) ≤ W
  anchor : ∀ (S : Finset D) (g : Finset V), (∃ a ∈ S, M.tail a ∈ g) →
    ∃ a, ch.anchor S g = some a ∧ a ∈ S ∧ M.tail a ∈ g

/-- **The certificate recursion is correct** (`exists_scert` for the explicit function `scertD`):
under the hypotheses of `exists_scert` and choice functions meeting `ScChoice.OK`, `scertD`
returns a path and items meeting `SCertOf`. -/
theorem scertD_spec {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint)
    (hloopM : ∀ d, M.head d ≠ M.tail d) {A W : ℕ} (hAW : W ≤ 2 * A) (ch : ScChoice M)
    (hch : ch.OK Hs A W) :
    ∀ (n : ℕ) (N : Finset D) (τ : Perm D) (ex : D → ℕ), N.card = n → PMap M N Hs τ →
      N.Nonempty → ∑ d ∈ N, (1 + ex d) ≤ W → 2 * W + 2 + 9 * (6 * Nat.sqrt (2 * n) + 4) ≤ 3 * A →
      ∃ ρ I, scertD ch Hs N τ ex = some (ρ, I) ∧
        SCertOf M N N Hs ex A (6 * Nat.sqrt (2 * n) + 4) ρ I := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N τ ex hn hN hne hW hA
  obtain ⟨x₀, hx₀⟩ := hne
  rw [scertD]
  by_cases hnc : NoCut M N Hs
  · subst hn
    obtain ⟨C, Z, hCZ, hk, hsep, hin, hout⟩ := hch.sep N τ hN ex ⟨x₀, hx₀⟩ hnc
    have hst : Stable τ N ∧ Stable (revPerm M) N := ⟨hN.stable, hN.rev⟩
    rw [dite_eq_left_of_eq_true (eq_true hst)]
    simp only [hnc, ↓reduceIte, hCZ, Option.map_some]
    exact ⟨_, _, rfl, scert_core' hd hloopM hN hx₀ hnc ex (by omega) C Z hk hsep hin hout⟩
  obtain ⟨g, hgch, hg, x, hx, y, hy, hxg, hyg, hxy⟩ := hch.hole N hnc
  simp only [hnc, ↓reduceIte, hgch]
  have hgc := hClosed_of_mem hd hg
  have hxyc : y ∉ comp M N Hs g x := fun h => hxy (mem_comp.1 h).2
  obtain ⟨a₁, ha₁, ha₁g⟩ := exists_exit (S := comp M N Hs g x)
    (fun a ha b hab => comp_closed ha hab) (self_mem_comp hx) hxyc (hN.conn x hx y hy)
  have ha₁N := (mem_comp.1 ha₁).1
  rcases hzz : ch.heavy N g ex with _ | z
  · have hheavy := hch.heavy_none N g ex hzz
    obtain ⟨a, hach, ha, hag⟩ := hch.anchor N g ⟨a₁, ha₁N, ha₁g⟩
    simp only [hach]
    exact ⟨_, _, rfl, scert_cut' hd hg ha hag ex (fun z hz => (wtY_le ex g _).trans (by
      have := hheavy z hz; omega)) (by omega)⟩
  obtain ⟨hz, hzh⟩ := hch.heavy_some N g ex z hzz
  simp only
  set K := comp M N Hs g z with hK
  have hKN : K ⊆ N := fun d hd => (mem_comp.1 hd).1
  have hKlt : K.card < N.card := by
    refine card_lt_card ⟨hKN, fun hNK => ?_⟩
    have hxK := hNK hx
    have hyK := hNK hy
    rw [hK] at hxK hyK
    have := comp_eq_of_mem hgc hz hxK
    rw [← this] at hyK
    exact hxyc hyK
  obtain ⟨w, hwN, hwK⟩ : ∃ w ∈ N, w ∉ K := by
    by_contra h; push Not at h; exact absurd (card_le_card h) (by omega)
  obtain ⟨a₀', ha₀', ha₀g'⟩ := exists_exit (S := K) (fun a ha b hab => comp_closed ha hab)
    (self_mem_comp hz) hwK (hN.conn z hz w hwN)
  obtain ⟨a₀, ha₀ch, ha₀, ha₀g⟩ := hch.anchor K g ⟨a₀', ha₀', ha₀g'⟩
  simp only [ha₀ch, hKlt, ↓reduceDIte]
  have hKr : Stable (revPerm M) K := fun d hd => comp_rev hN.rev hd
  have hKp : PMap M K Hs (ret τ K) := PMap.del hd hN hg hKN hKr
    (fun a ha b hab => comp_closed ha hab) (comp_conn hgc hz)
  set T := ∑ d ∈ N \ K, (1 + ex d) with hT
  have hsplit : ∑ d ∈ N, (1 + ex d) = ∑ d ∈ K, (1 + ex d) + T := by
    rw [hT, ← sum_union disjoint_sdiff, union_sdiff_of_subset hKN]
  have hlight : T ≤ A := by omega
  have hsumK : ∑ d ∈ K, (1 + (ex d + if d = a₀ then T else 0)) ≤ W := by
    have : ∑ d ∈ K, (1 + (ex d + if d = a₀ then T else 0)) =
        ∑ d ∈ K, (1 + ex d) + T := by
      rw [show (∑ d ∈ K, (1 + (ex d + if d = a₀ then T else 0))) =
        ∑ d ∈ K, ((1 + ex d) + if d = a₀ then T else 0) from
          sum_congr rfl fun d _ => by ring, sum_add_distrib, sum_ite_eq' K a₀]
      simp [ha₀]
    omega
  have hsq : Nat.sqrt (2 * K.card) ≤ Nat.sqrt (2 * n) := Nat.sqrt_le_sqrt (by omega)
  obtain ⟨ρ, I, hρI, hc⟩ := ih K.card (by omega) K (ret τ K)
    (fun d => ex d + if d = a₀ then T else 0) rfl hKp ⟨z, self_mem_comp hz⟩ hsumK (by omega)
  rw [hρI, Option.map_some]
  have hRcl : ∀ a ∈ N \ K, ∀ b, AStep M N Hs g a b → b ∈ N \ K := by
    intro a ha b hab
    refine mem_sdiff.2 ⟨hab.1, fun hbK => (mem_sdiff.1 ha).2 ?_⟩
    exact comp_closed hbK (hab.symm hgc (mem_sdiff.1 ha).1)
  exact ⟨ρ, _, rfl, ((scert_prune' hd hgc (fun u hu v hv => Or.inr ⟨g, hg, hu, hv⟩) hKN hKr
    (fun a ha b hab => comp_closed ha hab) hRcl ha₀ ha₀g ex hlight hc).mono (by omega)).mono_ρ
    hKN⟩

open Classical PlanarSeparator.Map in
/-- **The specification `ScChoice.OK` can be met** (by choices; on a map without loops). -/
theorem exists_scChoice_ok {Hs : List (Finset V)} (hloopM : ∀ d, M.head d ≠ M.tail d)
    (A W : ℕ) : ∃ ch : ScChoice M, ch.OK Hs A W := by
  let good : ∀ (N : Finset D) (τ : Perm D) (hσ : Stable τ N) (hB : Stable (revPerm M) N)
      (ex : D → ℕ), (psep M hσ hB).stellar.SCycle × Finset (psep M hσ hB).stellar.Face → Prop :=
    fun N τ hσ hB ex r =>
      r.1.k ≤ 6 * Nat.sqrt (Fintype.card (SVert τ N) + Fintype.card (psep M hσ hB).Face) + 4 ∧
      IsCycleSep r.1 r.2 (sideIn r.1 r.2) (sideOut r.1 r.2) ∧
      3 * ∑ y ∈ sideIn r.1 r.2, coreWt hσ hB (fun _ => 1) (coreExW τ N ex) y ≤
        2 * (∑ _x : SDart N, 1 + ∑ q, coreExW τ N ex q) + 2 ∧
      3 * ∑ y ∈ sideOut r.1 r.2, coreWt hσ hB (fun _ => 1) (coreExW τ N ex) y ≤
        2 * (∑ _x : SDart N, 1 + ∑ q, coreExW τ N ex q) + 2
  refine ⟨⟨fun N τ hσ hB ex => if h : ∃ r, good N τ hσ hB ex r then some h.choose else none,
    fun N => if h : ∃ g ∈ Hs, ∃ x ∈ N, ∃ y ∈ N, M.tail x ∉ g ∧ M.tail y ∉ g ∧
        ¬ ReflTransGen (AStep M N Hs g) x y then some h.choose else none,
    fun N g ex => if h : ∃ z ∈ N, W < A + ∑ d ∈ comp M N Hs g z, (1 + ex d) then
        some h.choose else none,
    fun S g => if h : ∃ a ∈ S, M.tail a ∈ g then some h.choose else none⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro N τ hN ex hne hnc
    obtain ⟨x₀, hx₀⟩ := hne
    have hl : ∀ d, (psep M hN.stable hN.rev).vert ((psep M hN.stable hN.rev).α d) ≠
        (psep M hN.stable hN.rev).vert d := by
      intro d h
      have h' := (hN.vert _ ((psep M hN.stable hN.rev).α d).2 _ d.2).1 ((psep_vert_eq _ _).1 h)
      rw [psep_α, CombMap.tail_rev] at h'
      rcases h' with e | ⟨H, hH, h1, h2⟩
      · exact hloopM d.1 e
      · exact hN.inner d.1 d.2 ⟨H, hH, h2, h1⟩
    obtain ⟨C, Z, h1, h2, h3, h4⟩ := exists_coreSep hN.stable hN.rev hx₀ hN.conn' hN.gap hl
      (fun _ => 1) (coreExW τ N ex)
    have hex : ∃ r, good N τ hN.stable hN.rev ex r := ⟨(C, Z), h1, h2, h3, h4⟩
    refine ⟨hex.choose.1, hex.choose.2, ?_, hex.choose_spec⟩
    simp only [hex, ↓reduceDIte]
  · intro N hnc
    have h : ∃ g ∈ Hs, ∃ x ∈ N, ∃ y ∈ N, M.tail x ∉ g ∧ M.tail y ∉ g ∧
        ¬ ReflTransGen (AStep M N Hs g) x y := by
      simp only [NoCut, not_forall] at hnc
      obtain ⟨g, hg, x, hx, y, hy, hxg, hyg, hxy⟩ := hnc
      exact ⟨g, hg, x, hx, y, hy, hxg, hyg, hxy⟩
    exact ⟨h.choose, by simp only [h, ↓reduceDIte], h.choose_spec⟩
  · intro N g ex z hz
    dsimp only at hz
    split_ifs at hz with h
    · cases hz; exact h.choose_spec
  · intro N g ex hz z hzN
    dsimp only at hz
    split_ifs at hz with h
    push Not at h
    exact (h z hzN)
  · intro S g h
    exact ⟨h.choose, by simp only [h, ↓reduceDIte], h.choose_spec⟩

end BKMNW

end PlanarFlow
