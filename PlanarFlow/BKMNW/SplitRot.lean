module

public import PlanarFlow.BKMNW.SplitD

/-!
# The rotation of the core piece map carried down the recursion

The chain of `PlanarFlow.BKMNW.SplitD` takes the rotation `σf P Hs` of the piece map of the core
of each piece as a parameter (specification: `PMap` whenever `CInv`). That rotation is **not** a
function of `(P, Hs)` in general: the child rotation of the proofs (`PieceInv.child`) contracts the
darts of the separator path and deletes the other darts inside the new hole; when the new hole
spans a cycle of the map (a chord between two vertices of the path), contracting a different
spanning tree of it gives a different cyclic order at the contracted vertex, with the same dart
set and holes. So the rotation is carried as a state: the invariant `CInvS M Q P Hs σ` is the body
of `CInv` with the rotation named, and the rotation of a child is the explicit
`chRot M Q P Hs σ π X = childRot M σ (pdarts M (core M Q P) Hs) π.path.darts
(pdarts M (core M Q X) (childHoles Hs π.path.mverts))` (contract the path, keep the child's darts).

* `CInvS`, `CInvS.cinv`, `CInvS.pmap`, `chRot`;
* **`split_of_closed_S`**: `split_of_closed` with the children's invariant for `chRot`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit Relation

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

variable (M) in
/-- **The invariant of the large pieces with the rotation named**: the body of `CInv` for the
rotation `σ` of the piece map of the core. -/
def CInvS (Q : Finset V) (P : Finset D) (Hs : List (Finset V)) (σ : Perm D) : Prop :=
  Disjoint (hunion Hs) Q ∧ PieceInv M (core M Q P) Hs σ ∧
    FOK M σ (pdarts M (core M Q P) Hs) Hs ∧ HConn M (core M Q P) Hs

lemma CInvS.cinv {Q : Finset V} {P : Finset D} {Hs : List (Finset V)} {σ : Perm D}
    (h : CInvS M Q P Hs σ) : CInv M Q P Hs :=
  ⟨h.1, σ, h.2.1, h.2.2.1, h.2.2.2⟩

/-- The named rotation is a rotation of the piece map of the core. -/
lemma CInvS.pmap {Q : Finset V} {P : Finset D} {Hs : List (Finset V)} {σ : Perm D}
    (h : CInvS M Q P Hs σ) : PMap M (pdarts M (core M Q P) Hs) Hs σ := by
  obtain ⟨-, hPI, hF, hc⟩ := h
  exact ⟨stable_pdarts hPI.rev Hs, hPI.stable, hPI.gap, hPI.vert, hc,
    fun x hx => (mem_pdarts.1 hx).2, hF⟩

lemma cinv_iff_exists_cinvS {Q : Finset V} {P : Finset D} {Hs : List (Finset V)} :
    CInv M Q P Hs ↔ ∃ σ, CInvS M Q P Hs σ :=
  ⟨fun ⟨h1, σ, h2, h3, h4⟩ => ⟨σ, h1, h2, h3, h4⟩, fun ⟨_, h⟩ => h.cinv⟩

variable (M) in
/-- **The rotation of a child**: contract the darts of the separator path in the piece map of
the core of the parent (rotation `σ`), then keep the darts of the piece map of the core of the
child `X`. -/
noncomputable def chRot (Q : Finset V) (P : Finset D) (Hs : List (Finset V)) (σ : Perm D)
    (π : HSep M) (X : Finset D) : Perm D :=
  childRot M σ (pdarts M (core M Q P) Hs) π.path.darts
    (pdarts M (core M Q X) (childHoles Hs π.path.mverts))

/-- **`split_of_closed` with the rotations named**: the children meet `CInvS` for the rotations
`chRot`. -/
theorem split_of_closed_S {S T Q : Finset V} {κ η : ℕ} (hSTQ : S ∪ T ⊆ Q) {P : Finset D}
    {Hs : List (Finset V)} (hP : PcOK M S T P Hs) {σ : Perm D} (hI : CInvS M Q P Hs σ)
    {π : HSep M}
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
    SplitOK M S T κ η P Hs l r π ∧
      CInvS M Q l (childHoles Hs π.path.mverts) (chRot M Q P Hs σ π l) ∧
      CInvS M Q r (childHoles Hs π.path.mverts) (chRot M Q P Hs σ π r) := by
  obtain ⟨hHQ, hPI, hF, hcc⟩ := hI
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
      CInvS M Q X ch (chRot M Q P Hs σ π X) := by
    intro X hX hXr hXcl
    have hXc : core M Q X ⊆ core M Q P := core_mono hX
    have hXcr : RevClosed M (core M Q X) := revClosed_core hXr
    refine ⟨by rw [hunion_childHoles]; exact disjoint_union_left.2 ⟨hHQ, hρQ⟩,
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

open Classical in
/-- **`exists_split_of_pcert'` with the rotations named**: from `PCertOf … Nf ρ I` and a nodup list
`lc` of the classes `P.image (clsF M P Nf Hs K ρ)`, the split `splitOf M P Hs K A Nf ρ lc`
meets the conclusion of `exists_split_of_pcert`, the children meeting `CInvS` for the rotations
`chRot`. -/
theorem exists_split_of_pcert_S {S T Q : Finset V} {κ : ℕ} (hSTQ : S ∪ T ⊆ Q) {P : Finset D}
    {Hs : List (Finset V)} (hP : PcOK M S T P Hs) {σ : Perm D} (hI : CInvS M Q P Hs σ) {K A L : ℕ}
    {Nf : Finset D} {ρ : HPath M} {I : Finset (Finset D)}
    (hc : PCertOf (M := M) Q P Hs K A L Nf ρ I) {lc : List (Finset D)}
    (hlc : lc.Nodup ∧ lc.toFinset = P.image (clsF M P Nf Hs K ρ)) (hA2 : 2 ≤ A)
    (hKA : K ≠ 0 → P.card + K ≤ A)
    (hW : 2 * (P.card + K * nTouch M P Hs) ≤ 3 * A) (hnT : nTouch M P Hs ≤ 6)
    (hbig : K = 0 → A < P.card) (hhole : K ≠ 0 → nTouch M P Hs = 6 ∧ A < 5 * K)
    (hshort : ∀ k, k + 1 ≤ L → k ^ 2 ≤ κ ^ 2 * P.card ∧ 2 * k ≤ P.card) :
    SplitOK M S T κ 6 P Hs (splitOf M P Hs K A Nf ρ lc).1 (splitOf M P Hs K A Nf ρ lc).2.1
        (splitOf M P Hs K A Nf ρ lc).2.2 ∧
      CInvS M Q (splitOf M P Hs K A Nf ρ lc).1 (childHoles Hs ρ.mverts)
        (chRot M Q P Hs σ (splitOf M P Hs K A Nf ρ lc).2.2 (splitOf M P Hs K A Nf ρ lc).1) ∧
      CInvS M Q (splitOf M P Hs K A Nf ρ lc).2.1 (childHoles Hs ρ.mverts)
        (chRot M Q P Hs σ (splitOf M P Hs K A Nf ρ lc).2.2 (splitOf M P Hs K A Nf ρ lc).2.1) ∧
      hw M K Hs ρ.mverts (splitOf M P Hs K A Nf ρ lc).1 ≤ A ∧
      hw M K Hs ρ.mverts (splitOf M P Hs K A Nf ρ lc).2.1 ≤ A := by
  simp only [splitOf]
  obtain ⟨hNf, hout, hρ, hρB, hρL, hlast, hρQ, -, hIc, hIcov, hIw⟩ := hc
  have hd := hP.disj
  obtain ⟨hcls, hrevX, hwt, htdisj, hclo, hcJ⟩ :=
    exists_cls' hP hNf hout hρ hIc hIcov hIw hA2 hKA
  set c := clsF M P Nf Hs K ρ with hcdef
  set C := ρ.mverts with hC
  set Y := newHole Hs C with hY
  set Z := P.image c with hZ
  have hρP : ∀ e ∈ ρ.darts, e ∈ P := fun e he => (mem_core.1 (mem_pdarts.1 (hρB e he)).1).1
  have hXP : ∀ X ∈ Z, X ⊆ P := fun X hX => by
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hX; exact hcls.sub d hd
  -- the total weight
  have hsum : ∑ X ∈ Z, hw M K Hs C X ≤ P.card + K * nTouch M P Hs := by
    simp only [hw_eq, sum_add_distrib, ← mul_sum]
    rw [← hcls.card_biUnion subset_rfl, hcls.biUnion_eq]
    refine Nat.add_le_add_left ?_ _
    rcases eq_or_ne K 0 with hK | hK
    · simp [hK]
    refine Nat.mul_le_mul_left _ ?_
    rw [← Finset.card_biUnion fun X hX X' hX' hne =>
      htdisj hK X (mem_coe.1 hX) X' (mem_coe.1 hX') hne, ← tH_biUnion, hcls.biUnion_eq]
    exact card_tH_le_nTouch P
  -- at least two classes
  have hlow : A < hw M K Hs C P → 2 ≤ Z.card := by
    intro h
    by_contra h'
    have h1 : Z.card ≤ 1 := by omega
    have h2 := hw_biUnion_le (M := M) (Hs := Hs) (C := C) K Z
    rw [hcls.biUnion_eq] at h2
    have h3 : ∑ X ∈ Z, hw M K Hs C X ≤ Z.card * A := by
      simpa using sum_le_card_nsmul Z _ A hwt
    nlinarith
  have h2 : 2 ≤ Z.card := by
    rcases eq_or_ne K 0 with hK | hK
    · apply hlow; rw [hw_eq, hK, zero_mul, add_zero]; exact hbig hK
    obtain ⟨h6, h5K⟩ := hhole hK
    by_cases ht : 5 ≤ (tH M Hs C P).card
    · apply hlow
      rw [hw_eq]
      have := Nat.mul_le_mul_left K ht
      linarith
    push Not at ht
    -- the holes touched by the piece
    set Fall := (Hs.filter fun H => ∃ v ∈ H, Touch M P v).toFinset with hFall
    have hF6 : Fall.card = 6 := by rw [← nTouch_eq_card hd]; exact h6
    have hHs : ∀ H ∈ Fall, H ∈ Hs ∧ ∃ v ∈ H, Touch M P v := fun H hH => by
      simpa [hFall] using hH
    have hdisj : ∀ {H H'}, H ∈ Fall → H' ∈ Fall → H ≠ H' → Disjoint H H' := fun h h' hne =>
      disjoint_of_pairwise hd (hHs _ h).1 (hHs _ h').1 hne
    -- two of them are met by the separator
    have hmet : 1 < (Fall.filter fun H => ¬ Disjoint H C).card := by
      have := card_filter_add_card_filter_not (s := Fall) (fun H => Disjoint H C)
      have hsub : (Fall.filter fun H => Disjoint H C).card ≤ (tH M Hs C P).card := by
        refine card_le_card fun H hH => ?_
        obtain ⟨hH1, hH2⟩ := mem_filter.1 hH
        obtain ⟨hHs', v, hv, x, hx, rfl⟩ := hHs H hH1
        exact mem_tH.2 ⟨hHs', hH2, x, hx, hv⟩
      omega
    obtain ⟨H₁, hH₁, H₂, hH₂, hne⟩ := one_lt_card.1 hmet
    rw [mem_filter] at hH₁ hH₂
    -- so the separator has a dart
    have hk : 0 < ρ.k := by
      by_contra hk0
      have hm : ∀ v ∈ C, v = ρ.p 0 := by
        intro v hv
        rcases ρ.mem_mverts.1 hv with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
        · rw [show j = 0 by omega]
        · omega
      obtain ⟨v₁, hv₁, hv₁C⟩ := not_disjoint_iff.1 hH₁.2
      obtain ⟨v₂, hv₂, hv₂C⟩ := not_disjoint_iff.1 hH₂.2
      rw [hm v₁ hv₁C] at hv₁
      rw [hm v₂ hv₂C] at hv₂
      exact disjoint_left.1 (hdisj hH₁.1 hH₂.1 hne) hv₁ hv₂
    have he₀ : ρ.d 0 ∈ ρ.darts := ρ.mem_darts.2 ⟨0, hk, Or.inl rfl⟩
    have he₀P := hρP _ he₀
    obtain ⟨ht₀, hh₀⟩ := ρ.ends_mem he₀
    have hce₀ : c (ρ.d 0) = {ρ.d 0, M.rev (ρ.d 0)} :=
      hcJ _ he₀P (subset_newHole ht₀) (subset_newHole hh₀)
    -- a touched hole avoids the ends of that dart
    obtain ⟨a, ha, b, hb, c', hc', hab, hac, hbc⟩ := two_lt_card.1 (by omega : 2 < Fall.card)
    have hfree : ∃ H ∈ Fall, M.tail (ρ.d 0) ∉ H ∧ M.head (ρ.d 0) ∉ H := by
      by_contra hcon
      have hc : ∀ H ∈ Fall, M.tail (ρ.d 0) ∉ H → M.head (ρ.d 0) ∈ H := fun H hH h => by
        by_contra h'; exact hcon ⟨H, hH, h, h'⟩
      have d1 : ∀ v, v ∈ a → v ∉ b := fun v hv => disjoint_left.1 (hdisj ha hb hab) hv
      have d2 : ∀ v, v ∈ a → v ∉ c' := fun v hv => disjoint_left.1 (hdisj ha hc' hac) hv
      have d3 : ∀ v, v ∈ b → v ∉ c' := fun v hv => disjoint_left.1 (hdisj hb hc' hbc) hv
      by_cases hxa : M.tail (ρ.d 0) ∈ a
      · exact d3 _ (hc b hb (d1 _ hxa)) (hc c' hc' (d2 _ hxa))
      have hya := hc a ha hxa
      by_cases hxb : M.tail (ρ.d 0) ∈ b
      · exact d2 _ hya (hc c' hc' (d3 _ hxb))
      · exact d1 _ hya (hc b hb hxb)
    obtain ⟨H, hH, hxH, hyH⟩ := hfree
    obtain ⟨-, v, hv, f, hf, rfl⟩ := hHs H hH
    have hfne : f ∉ ({ρ.d 0, M.rev (ρ.d 0)} : Finset D) := by
      intro h
      rcases mem_insert.1 h with h | h
      · rw [h] at hv; exact hxH hv
      · rw [mem_singleton.1 h, CombMap.tail_rev] at hv; exact hyH hv
    refine one_lt_card.2 ⟨c (ρ.d 0), mem_image_of_mem c he₀P, c f, mem_image_of_mem c hf,
      fun h => ?_⟩
    have := hcls.self f hf
    rw [← h, hce₀] at this
    exact hfne this
  -- the grouping
  have hlZ : lc.toFinset = Z := hlc.2
  have hlen : 2 ≤ lc.length := by
    rw [← List.toFinset_card_of_nodup hlc.1, hlZ]; exact h2
  obtain ⟨hGZ, hGne, hGcne, hGA, hGcA⟩ := twoGroups_spec (hw M K Hs C) hlc.1 hlen
    (fun X hX => hwt X (hlZ ▸ List.mem_toFinset.2 hX))
    (by rw [← sum_toFinset_nodup hlc.1, hlZ]; exact hsum) hW
  rw [hlZ] at hGZ hGcne hGcA
  set G := (twoGroupsL (hw M K Hs C) A lc).toFinset with hGdef
  have hGc : Z \ G ⊆ Z := sdiff_subset
  have hrevG : ∀ G' ⊆ Z, RevClosed M (G'.biUnion id) := fun G' hG' e he => by
    obtain ⟨X, hX, he⟩ := mem_biUnion.1 he
    exact mem_biUnion.2 ⟨X, hX, hrevX X (hG' hX) e he⟩
  have hclG : ∀ G' ⊆ Z, ∀ a ∈ G'.biUnion id, ∀ b ∈ P, ¬ Inner M (childHoles Hs C) a →
      ¬ Inner M (childHoles Hs C) b →
      (b = M.rev a ∨ (HRel Hs (M.tail a) (M.tail b) ∧ M.tail a ∉ Y)) → b ∈ G'.biUnion id := by
    intro G' hG' a ha b hb h1 h2 hst
    obtain ⟨X, hX, haX⟩ := mem_biUnion.1 ha
    refine mem_biUnion.2 ⟨X, hX, ?_⟩
    rw [← hcls.eq_of_mem (hG' hX) haX]
    exact hclo a (hXP X (hG' hX) haX) b hb h1 h2 hst
  have hposG : ∀ G' ⊆ Z, G'.Nonempty → 0 < (G'.biUnion id).card := fun G' hG' ⟨X, hX⟩ => by
    obtain ⟨e, he⟩ := hcls.nonempty (hG' hX)
    exact card_pos.2 ⟨e, mem_biUnion.2 ⟨X, hX, he⟩⟩
  have hlr : G.biUnion id ∪ (Z \ G).biUnion id = P := by
    rw [← union_biUnion, union_sdiff_of_subset hGZ, hcls.biUnion_eq]
  have hlrd : Disjoint (G.biUnion id) ((Z \ G).biUnion id) := by
    refine disjoint_left.2 fun e h1 h2 => ?_
    obtain ⟨X, hX, he⟩ := mem_biUnion.1 h1
    obtain ⟨X', hX', he'⟩ := mem_biUnion.1 h2
    have hne : X ≠ X' := fun h => (mem_sdiff.1 hX').2 (h ▸ hX)
    exact disjoint_left.1 (hcls.disj (hGZ hX) (hGc hX') hne) he he'
  -- the parts of the separator
  obtain ⟨hsok, hslen, hsσ⟩ := exists_segs' ρ hρ hρP hlast
  set segs := ρ.runsF hρ 0 with hsegs
  have hshort' : HSep.Short κ 6 P.card ⟨ρ, segs⟩ := by
    refine ⟨show segs.length ≤ 6 + 1 by omega, fun σ hσ => hshort σ.k ?_⟩
    have := (hsσ σ hσ).1
    omega
  obtain ⟨hsplit, hIl, hIr⟩ := split_of_closed_S (π := ⟨ρ, segs⟩) hSTQ hP hI hρ hρB hρQ hsok
    (fun σ hσ => (hsσ σ hσ).2) hshort' hlr hlrd (hposG G hGZ hGne) (hposG _ hGc hGcne)
    (hrevG G hGZ) (hrevG _ hGc) (hclG G hGZ) (hclG _ hGc)
  rw [show segsF ρ Hs = segs by simp only [segsF, hρ, ↓reduceDIte, hsegs]]
  exact ⟨hsplit, hIl, hIr, (hw_biUnion_le K G).trans hGA,
    (hw_biUnion_le K _).trans hGcA⟩


variable (M) in
/-- **The split by size with the rotation as an argument** (`spSD` with `σf` constant). -/
noncomputable def spSR (pc : PcChoice D V) (sc : List (Finset V) → ℕ → ℕ → ScChoice M)
    (Q : Finset V) (P : Finset D) (Hs : List (Finset V)) (σ : Perm D) : SplitAns M :=
  splitD M pc (sc Hs (aS P) (P.card + 0 * nTouch M P Hs)) Q P Hs 0 (aS P) σ

variable (M) in
/-- **The split by holes with the rotation as an argument** (`spHD` with `σf` constant). -/
noncomputable def spHR (pc : PcChoice D V) (sc : List (Finset V) → ℕ → ℕ → ScChoice M)
    (Q : Finset V) (P : Finset D) (Hs : List (Finset V)) (σ : Perm D) : SplitAns M :=
  splitD M pc (sc Hs (aH P) (P.card + kH P * nTouch M P Hs)) Q P Hs (kH P) (aH P) σ

lemma spSR_eq (pc : PcChoice D V) (sc : List (Finset V) → ℕ → ℕ → ScChoice M) (Q : Finset V)
    (P : Finset D) (Hs : List (Finset V)) (σ : Perm D) :
    spSR M pc sc Q P Hs σ = spSD M pc sc (fun _ _ => σ) Q P Hs := rfl

lemma spHR_eq (pc : PcChoice D V) (sc : List (Finset V) → ℕ → ℕ → ScChoice M) (Q : Finset V)
    (P : Finset D) (Hs : List (Finset V)) (σ : Perm D) :
    spHR M pc sc Q P Hs σ = spHD M pc sc (fun _ _ => σ) Q P Hs := rfl

/-- **`split_size` for `spSR`**, the children meeting `CInvS` for the rotations `chRot`. -/
theorem split_size_S {S T Q : Finset V} (hSTQ : S ∪ T ⊆ Q) (hloopM : ∀ d, M.head d ≠ M.tail d)
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) {P : Finset D} {Hs : List (Finset V)}
    (hP : PcOK M S T P Hs) {σ : Perm D} (hI : CInvS M Q P Hs σ) (hs : 100000 < P.card)
    (ht : nTouch M P Hs ≤ 5) (pc : PcChoice D V) (hpc : pc.OK M Q P Hs)
    (sc : List (Finset V) → ℕ → ℕ → ScChoice M) (hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W) :
    ∃ l r π, spSR M pc sc Q P Hs σ = some (l, r, π) ∧ SplitOK M S T 9 6 P Hs l r π ∧
      CInvS M Q l (childHoles Hs π.path.mverts) (chRot M Q P Hs σ π l) ∧
      CInvS M Q r (childHoles Hs π.path.mverts) (chRot M Q P Hs σ π r) ∧
      4 * l.card ≤ 3 * P.card ∧ 4 * r.card ≤ 3 * P.card := by
  have hb := sqrt_bound hs
  have hL : lS P = 6 * Nat.sqrt (2 * P.card) + 4 := rfl
  have hA : aS P = (2 * P.card + 2 + 9 * lS P) / 3 + 1 := rfl
  have hP0 : P.Nonempty := card_pos.1 (by omega)
  obtain ⟨c, hcD, hc⟩ := pcert' hloopM hQdeg hQ5 hP hI.cinv hP0 0 (A := aS P)
    (by simp only [zero_mul]; omega) (by omega) hI.pmap pc hpc _ (hsc Hs _ _)
  obtain ⟨h1, h2, h3, h4, h5⟩ := exists_split_of_pcert_S (κ := 9) hSTQ hP hI hc (hpc.ord _)
    (by omega) (fun h => absurd rfl h) (by simp only [zero_mul]; omega) (by omega)
    (fun _ => by omega) (fun h => absurd rfl h) (fun k hk => short_bound hs hk)
  rw [hw_eq, zero_mul, add_zero] at h4 h5
  refine ⟨_, _, _, ?_, h1, h2, h3, by omega, by omega⟩
  simp only [spSR, splitD, hcD, Option.map_some]

/-- **`split_hole` for `spHR`**, the children meeting `CInvS` for the rotations `chRot`. -/
theorem split_hole_S {S T Q : Finset V} (hSTQ : S ∪ T ⊆ Q) (hloopM : ∀ d, M.head d ≠ M.tail d)
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) {P : Finset D} {Hs : List (Finset V)}
    (hP : PcOK M S T P Hs) {σ : Perm D} (hI : CInvS M Q P Hs σ) (hs : 100000 < P.card)
    (ht : nTouch M P Hs = 6) (pc : PcChoice D V) (hpc : pc.OK M Q P Hs)
    (sc : List (Finset V) → ℕ → ℕ → ScChoice M) (hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W) :
    ∃ l r π, spHR M pc sc Q P Hs σ = some (l, r, π) ∧ SplitOK M S T 9 6 P Hs l r π ∧
      CInvS M Q l (childHoles Hs π.path.mverts) (chRot M Q P Hs σ π l) ∧
      CInvS M Q r (childHoles Hs π.path.mverts) (chRot M Q P Hs σ π r) ∧
      nTouch M l (childHoles Hs π.path.mverts) ≤ 5 ∧
      nTouch M r (childHoles Hs π.path.mverts) ≤ 5 := by
  have hb := sqrt_bound hs
  have hL : lS P = 6 * Nat.sqrt (2 * P.card) + 4 := rfl
  have hK : kH P = P.card + 3 * lS P + 2 := rfl
  have hA : aH P = (2 * (P.card + 6 * kH P) + 2 + 9 * lS P) / 3 + 1 := rfl
  have hP0 : P.Nonempty := card_pos.1 (by omega)
  obtain ⟨c, hcD, hc⟩ := pcert' hloopM hQdeg hQ5 hP hI.cinv hP0 (kH P) (A := aH P)
    (by rw [ht]; omega) (by omega) hI.pmap pc hpc _ (hsc Hs _ _)
  have hK0 : kH P ≠ 0 := by omega
  obtain ⟨h1, h2, h3, h4, h5⟩ := exists_split_of_pcert_S (κ := 9) hSTQ hP hI hc (hpc.ord _)
    (by omega) (fun _ => by omega) (by rw [ht]; omega) (by omega) (fun h => absurd h hK0)
    (fun _ => ⟨ht, by omega⟩) (fun k hk => short_bound hs hk)
  have hfew : ∀ X : Finset D, hw M (kH P) Hs c.2.1.mverts X ≤ aH P →
      nTouch M X (childHoles Hs c.2.1.mverts) ≤ 5 := by
    intro X hX
    refine (nTouch_ch_le hP.disj X).trans ?_
    rw [hw_eq] at hX
    by_contra h
    have h' : 5 ≤ (tH M Hs c.2.1.mverts X).card := by omega
    have := Nat.mul_le_mul_left (kH P) h'
    have : aH P < 5 * kH P := by omega
    linarith
  refine ⟨_, _, _, ?_, h1, h2, h3, hfew _ h4, hfew _ h5⟩
  simp only [spHR, splitD, hcD, Option.map_some]

end BKMNW

end PlanarFlow
