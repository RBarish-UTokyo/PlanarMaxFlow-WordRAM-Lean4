module

public import PlanarFlow.BKMNW.ExistScertD
public import PlanarFlow.BKMNW.ExistGroupD

/-!
# The certificate of a whole piece, and its split, as functions

* `liftI`, **`scert_lift_list'`**: `scert_lift_list` with the items named.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit Relation CombMap PlanarSeparator

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

/-- The items of a certificate lifted through a list of attached sets (`pruneI` at each set,
the last set of the list first). -/
def liftI (Hs : List (Finset V)) (B : Finset D) (ρ : HPath M) (I : Finset (Finset D)) :
    List (Finset D × Finset V × D) → Finset (Finset D)
  | [] => I
  | e :: Ls => pruneI Hs (B ∪ lunion Ls ∪ e.1) (B ∪ lunion Ls) e.2.2 ρ (liftI Hs B ρ I Ls)

/-- **`scert_lift_list` with the witnesses named**: the same path, the items `liftI`. -/
theorem scert_lift_list' {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {Q : Finset V}
    (hQ : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQH : Disjoint (hunion Hs) Q) {A L : ℕ} :
    ∀ (Ls : List (Finset D × Finset V × D)) (B : Finset D) (ex : D → ℕ),
      Stable (revPerm M) B →
      (∀ e ∈ Ls, Stable (revPerm M) e.1 ∧ Disjoint e.1 B ∧ HClosed Hs e.2.1 ∧
        (∀ u ∈ e.2.1, ∀ v ∈ e.2.1, HRel Hs u v) ∧ e.2.2 ∈ B ∧ M.tail e.2.2 ∈ e.2.1 ∧
        (∀ d ∈ e.1, M.tail d ∈ e.2.1 ∨ M.tail d ∈ Q) ∧ ∑ d ∈ e.1, (1 + ex d) ≤ A) →
      Ls.Pairwise (fun e e' => Disjoint e.1 e'.1) →
      ∀ {Nρ : Finset D} {ρ : HPath M} {I : Finset (Finset D)},
      SCertOf M B Nρ Hs (fun d => ex d + lmoved ex Ls d) A L ρ I →
      SCertOf M (B ∪ lunion Ls) Nρ Hs ex A L ρ (liftI Hs B ρ I Ls) := by
  intro Ls
  induction Ls with
  | nil =>
    intro B ex _ _ _ Nρ ρ I h
    simpa [lunion, lmoved, liftI] using h
  | cons e Ls ih =>
    intro B ex hB hLs hpw Nρ ρ I hc
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
    have hc₁ : SCertOf M B Nρ Hs (fun d => ex₁ d + lmoved ex₁ Ls d) A L ρ I := by
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
    have hres := scert_prune' (N := K ∪ e.1) (K := K) (A := A) (L := L) hd hgc hgr
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

variable (D V) in
/-- **The choice functions of the certificate of a whole piece**: a dart of a pair, a dart of the
core related to the anchor vertex of a dart, a dart of the core at a hole, and an ordering of a
finite set of sets of darts. -/
structure PcChoice where
  /-- A dart of the pair `{d, rev d}`. -/
  rep : Finset D → D
  /-- A dart of the piece map of the core related to the anchor vertex of a dart. -/
  ancD : Finset D → List (Finset V) → D → D
  /-- A dart of the piece map of the core leaving the hole. -/
  anch : Finset D → List (Finset V) → Finset V → D
  /-- A list of the elements of a finite set of sets. -/
  ord : Finset (Finset D) → List (Finset D)
  /-- An element of a nonempty set of darts. -/
  pick : Finset D → D

variable (M) in
/-- The anchor vertex of a dart: its end off `Q`. -/
def avQ (Q : Finset V) (d : D) : V := if M.tail d ∈ Q then M.head d else M.tail d

variable (M) in
/-- The specification of `PcChoice` on the piece `P` with holes `Hs`. -/
structure PcChoice.OK (pc : PcChoice D V) (Q : Finset V) (P : Finset D) (Hs : List (Finset V)) :
    Prop where
  rep : ∀ d, pc.rep {d, M.rev d} = d ∨ pc.rep {d, M.rev d} = M.rev d
  anc : ∀ d, (∃ b ∈ pdarts M (core M Q P) Hs, HRel Hs (M.tail b) (avQ M Q d)) →
    pc.ancD P Hs d ∈ pdarts M (core M Q P) Hs ∧ HRel Hs (M.tail (pc.ancD P Hs d)) (avQ M Q d)
  anch : ∀ H, (∃ b ∈ pdarts M (core M Q P) Hs, M.tail b ∈ H) →
    pc.anch P Hs H ∈ pdarts M (core M Q P) Hs ∧ M.tail (pc.anch P Hs H) ∈ H
  ord : ∀ X, (pc.ord X).Nodup ∧ (pc.ord X).toFinset = X
  pick : ∀ X : Finset D, X.Nonempty → pc.pick X ∈ X

variable (M) in
open Classical in
/-- The darts of the piece attached to the certificate: all but those inside holes not touched by
the piece map of the core. -/
noncomputable def pcNf (Q : Finset V) (P : Finset D) (Hs : List (Finset V)) : Finset D :=
  P \ P.filter fun d => Inner M Hs d ∧ ∀ b ∈ pdarts M (core M Q P) Hs, ¬ HRel Hs (M.tail b) (M.tail d)

variable (M) in
/-- The pairs of darts attached off the piece map of the core. -/
noncomputable def pcEs (Q : Finset V) (P : Finset D) (Hs : List (Finset V)) : Finset (Finset D) :=
  (pcNf M Q P Hs \ pdarts M (core M Q P) Hs).image fun d => ({d, M.rev d} : Finset D)

variable (M) in
/-- The attached sets, with their vertex sets and anchors, in the order `pc.ord`. -/
noncomputable def pcLs (pc : PcChoice D V) (Q : Finset V) (P : Finset D) (Hs : List (Finset V)) :
    List (Finset D × Finset V × D) :=
  (pc.ord (pcEs M Q P Hs)).map fun E => (E, cls Hs (avQ M Q (pc.rep E)), pc.ancD P Hs (pc.rep E))

variable (M) in
open Classical in
/-- The weight `K` on the anchor dart of every hole. -/
noncomputable def pcExf (pc : PcChoice D V) (Q : Finset V) (P : Finset D) (Hs : List (Finset V))
    (K : ℕ) (d : D) : ℕ :=
  if d ∈ pdarts M (core M Q P) Hs ∧ ∃ H ∈ Hs, M.tail d ∈ H ∧ pc.anch P Hs H = d then K else 0

variable (M) in
/-- **The certificate of a whole piece, as a function**: the certificate `scertD` of the piece
map of the core (rotation `σ`) with the weights of the attached sets moved to their anchors,
lifted (`liftI`) to the attached darts `pcNf`. -/
noncomputable def pcertD (pc : PcChoice D V) (ch : ScChoice M) (Q : Finset V) (P : Finset D)
    (Hs : List (Finset V)) (K : ℕ) (σ : Perm D) :
    Option (Finset D × HPath M × Finset (Finset D)) :=
  (scertD ch Hs (pdarts M (core M Q P) Hs) σ
    (fun d => pcExf M pc Q P Hs K d + lmoved (pcExf M pc Q P Hs K) (pcLs M pc Q P Hs) d)).map
    fun r => (pcNf M Q P Hs, r.1,
      liftI Hs (pdarts M (core M Q P) Hs) r.1 r.2 (pcLs M pc Q P Hs))

open Classical in
/-- **`pcert_of_core` as a function**: under its hypotheses, a rotation `σ` of the piece map of
the core, choices meeting `PcChoice.OK` and `ScChoice.OK` (for `W = #P + K nTouch`), `pcertD`
returns `(pcNf, ρ, I)` meeting `PCertOf`. -/
theorem pcert_of_core' {S T Q : Finset V} (hloopM : ∀ d, M.head d ≠ M.tail d)
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) {P : Finset D} {Hs : List (Finset V)}
    (hP : PcOK M S T P Hs) (hI : CInv M Q P Hs) (hne : (pdarts M (core M Q P) Hs).Nonempty)
    (K : ℕ) {A : ℕ} (hAW : P.card + K * nTouch M P Hs ≤ 2 * A)
    (hA : 2 * (P.card + K * nTouch M P Hs) + 2 + 9 * (6 * Nat.sqrt (2 * P.card) + 4) ≤ 3 * A)
    (hA2 : 2 ≤ A) {σ : Perm D} (hPM : PMap M (pdarts M (core M Q P) Hs) Hs σ)
    (pc : PcChoice D V) (hpc : pc.OK M Q P Hs) (ch : ScChoice M)
    (hch : ch.OK Hs A (P.card + K * nTouch M P Hs)) :
    ∃ ρ I, pcertD M pc ch Q P Hs K σ = some (pcNf M Q P Hs, ρ, I) ∧
      PCertOf (M := M) Q P Hs K A (6 * Nat.sqrt (2 * P.card) + 4) (pcNf M Q P Hs) ρ I := by
  have hd := hP.disj
  have hHQ := hI.1
  set B₀ := pdarts M (core M Q P) Hs with hB₀
  obtain ⟨b₀, hb₀⟩ := hne
  have hQn : ∀ q ∈ Q, q ∉ hunion Hs := fun q hq h => disjoint_left.1 hHQ h hq
  have hB₀P : B₀ ⊆ P := fun d hd => (mem_core.1 (mem_pdarts.1 hd).1).1
  have hB₀Q : ∀ d ∈ B₀, M.tail d ∉ Q ∧ M.head d ∉ Q := fun d hd =>
    (mem_core.1 (mem_pdarts.1 hd).1).2
  -- the darts inside holes not touched by the core
  set Dg := P.filter fun d => Inner M Hs d ∧ ∀ b ∈ B₀, ¬ HRel Hs (M.tail b) (M.tail d) with hDg
  set Nf := P \ Dg with hNf
  have hNfeq : pcNf M Q P Hs = Nf := rfl
  rw [hNfeq]
  have hB₀Nf : B₀ ⊆ Nf := fun d hd => mem_sdiff.2 ⟨hB₀P hd, fun h =>
    (mem_pdarts.1 hd).2 (mem_filter.1 h).2.1⟩
  -- the anchor vertex of a dart off the core
  set av : D → V := fun d => if M.tail d ∈ Q then M.head d else M.tail d with hav
  have hanc : ∀ d ∈ Nf \ B₀, M.tail d ∉ Q → ∃ b ∈ B₀, HRel Hs (M.tail b) (M.tail d) := by
    intro d hd htQ
    obtain ⟨hdNf, hdB⟩ := mem_sdiff.1 hd
    obtain ⟨hdP, hdD⟩ := mem_sdiff.1 hdNf
    by_cases hhQ : M.head d ∈ Q
    · exact exists_core_anchor hQdeg hP hHQ hb₀ hdP hhQ htQ
    · have hinner : Inner M Hs d := by
        by_contra h
        exact hdB (mem_pdarts.2 ⟨mem_core.2 ⟨hdP, htQ, hhQ⟩, h⟩)
      by_contra hno
      push Not at hno
      exact hdD (mem_filter.2 ⟨hdP, hinner, hno⟩)
  have hanc' : ∀ d ∈ Nf \ B₀, ∃ b ∈ B₀, HRel Hs (M.tail b) (av d) := by
    intro d hd
    by_cases htQ : M.tail d ∈ Q
    · have hrd : M.rev d ∈ Nf \ B₀ := by
        obtain ⟨hdNf, hdB⟩ := mem_sdiff.1 hd
        obtain ⟨hdP, hdD⟩ := mem_sdiff.1 hdNf
        refine mem_sdiff.2 ⟨mem_sdiff.2 ⟨hP.rev _ hdP, fun h => ?_⟩, fun h => ?_⟩
        · obtain ⟨H, hH, -, h2⟩ := (mem_filter.1 h).2.1
          rw [CombMap.head_rev] at h2
          exact hQn _ htQ (subset_hunion hH h2)
        · exact (hB₀Q _ h).2 (by rw [CombMap.head_rev]; exact htQ)
      have := hanc _ hrd (by rw [CombMap.tail_rev]; exact fun h => hQ5 d ⟨htQ, h⟩)
      simpa [av, htQ] using this
    · simpa [av, htQ] using hanc d hd htQ
  have havQ : ∀ d, av d ∉ Q := by
    intro d
    by_cases htQ : M.tail d ∈ Q
    · show (if M.tail d ∈ Q then M.head d else M.tail d) ∉ Q
      simp only [htQ, ↓reduceIte]; exact fun h => hQ5 d ⟨htQ, h⟩
    · show (if M.tail d ∈ Q then M.head d else M.tail d) ∉ Q
      simp only [htQ, ↓reduceIte]; exact not_false
  have hrevNf : ∀ d ∈ Nf \ B₀, M.rev d ∈ Nf \ B₀ := by
    intro d hdm
    obtain ⟨hdNf, hdB⟩ := mem_sdiff.1 hdm
    obtain ⟨hdP, hdD⟩ := mem_sdiff.1 hdNf
    refine mem_sdiff.2 ⟨mem_sdiff.2 ⟨hP.rev _ hdP, fun h => hdD ?_⟩, fun h => hdB ?_⟩
    · obtain ⟨-, h1, h2⟩ := mem_filter.1 h
      have hdi : Inner M Hs d := inner_rev.1 h1
      refine mem_filter.2 ⟨hdP, hdi, fun b hb hr => h2 b hb ?_⟩
      obtain ⟨H, hH, ht, hh⟩ := hdi
      rw [CombMap.tail_rev]
      exact hRel_trans' hd hr (Or.inr ⟨H, hH, ht, hh⟩)
    · have := stable_pdarts (revClosed_core hP.rev) Hs _ h
      rw [revPerm_apply, M.rev_rev] at this; exact this
  -- the pairs of darts off the core
  set Es := (Nf \ B₀).image fun d => ({d, M.rev d} : Finset D) with hEs
  have hEsrep : ∀ E ∈ Es, ∃ d ∈ Nf \ B₀, E = {d, M.rev d} := fun E hE => by
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hE; exact ⟨d, hd, rfl⟩
  set rep : Finset D → D := pc.rep with hrepdef
  have hrep : ∀ E ∈ Es, rep E ∈ Nf \ B₀ := by
    intro E hE
    obtain ⟨d, hd', rfl⟩ := mem_image.1 hE
    rcases hpc.rep d with h | h
    · rw [hrepdef, h]; exact hd'
    · rw [hrepdef, h]; exact hrevNf d hd'
  have hrepE : ∀ E ∈ Es, E = {rep E, M.rev (rep E)} := by
    intro E hE
    obtain ⟨d, -, rfl⟩ := mem_image.1 hE
    rcases hpc.rep d with h | h
    · rw [hrepdef, h]
    · rw [hrepdef, h, M.rev_rev, pair_comm]
  set anc : Finset D → D := fun E => pc.ancD P Hs (rep E) with hancdef
  have hancB : ∀ E ∈ Es, anc E ∈ B₀ := fun E hE =>
    (hpc.anc (rep E) (hanc' (rep E) (hrep E hE))).1
  have hancR : ∀ E ∈ Es, HRel Hs (M.tail (anc E)) (av (rep E)) := fun E hE =>
    (hpc.anc (rep E) (hanc' (rep E) (hrep E hE))).2
  have hlE := hpc.ord Es
  set Ls : List (Finset D × Finset V × D) :=
    (pc.ord Es).map fun E => (E, cls Hs (av (rep E)), anc E) with hLs
  -- the anchors of the holes
  set anch : Finset V → D := pc.anch P Hs with hanch
  have hhAspec : ∀ H, (∃ b ∈ B₀, M.tail b ∈ H) → anch H ∈ B₀ ∧ M.tail (anch H) ∈ H :=
    fun H h => hpc.anch H h
  set exf : D → ℕ := fun d => if d ∈ B₀ ∧ ∃ H ∈ Hs, M.tail d ∈ H ∧ anch H = d then K else 0
    with hexf
  have hexf0 : ∀ d, d ∉ B₀ → exf d = 0 := fun d hd => by simp [exf, hd]
  -- the attached sets
  have hmemLs : ∀ e ∈ Ls, ∃ E ∈ Es, e = (E, cls Hs (av (rep E)), anc E) := fun e he => by
    obtain ⟨E, hE, rfl⟩ := List.mem_map.1 he
    exact ⟨E, hlE.2 ▸ List.mem_toFinset.2 hE, rfl⟩
  have hEdisj : ∀ E ∈ Es, Disjoint E B₀ := by
    intro E hE
    rw [hrepE E hE]
    have h1 := hrep E hE
    have h2 := hrevNf _ h1
    refine disjoint_left.2 fun x hx hxB => ?_
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_sdiff.1 h1).2 hxB
    · exact (mem_sdiff.1 h2).2 hxB
  have hEw : ∀ E ∈ Es, ∑ d ∈ E, (1 + exf d) = E.card := fun E hE => by
    rw [card_eq_sum_ones]
    exact sum_congr rfl fun d hdE => by
      rw [hexf0 d (disjoint_left.1 (hEdisj E hE) hdE)]
  have hLsprop : ∀ e ∈ Ls, Stable (revPerm M) e.1 ∧ Disjoint e.1 B₀ ∧ HClosed Hs e.2.1 ∧
      (∀ u ∈ e.2.1, ∀ v ∈ e.2.1, HRel Hs u v) ∧ e.2.2 ∈ B₀ ∧ M.tail e.2.2 ∈ e.2.1 ∧
      (∀ d ∈ e.1, M.tail d ∈ e.2.1 ∨ M.tail d ∈ Q) ∧ ∑ d ∈ e.1, (1 + exf d) ≤ A := by
    intro e he
    obtain ⟨E, hE, rfl⟩ := hmemLs e he
    have hr := hrep E hE
    have hEeq := hrepE E hE
    refine ⟨?_, hEdisj E hE, hClosed_cls hd _, hRel_of_mem_cls hd _, hancB E hE,
      (mem_cls_iff hd).2 (hRel_symm (hancR E hE)), ?_, ?_⟩
    · rw [hEeq]; intro x hx
      simp only [mem_insert, mem_singleton] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (M.rev_rev _)
    · intro d hdE
      rw [hEeq] at hdE
      simp only [mem_insert, mem_singleton] at hdE
      set r := rep E
      have hrP : r ∈ P := (mem_sdiff.1 (mem_sdiff.1 hr).1).1
      rcases hdE with rfl | rfl
      · by_cases htQ : M.tail r ∈ Q
        · exact Or.inr htQ
        · left
          have : av r = M.tail r := by simp [av, htQ]
          rw [this]; exact mem_cls_self _ _
      · rw [CombMap.tail_rev]
        by_cases htQ : M.tail r ∈ Q
        · left
          have : av r = M.head r := by simp [av, htQ]
          rw [this]; exact mem_cls_self _ _
        · by_cases hhQ : M.head r ∈ Q
          · exact Or.inr hhQ
          · left
            have : av r = M.tail r := by simp [av, htQ]
            rw [this]
            -- a dart of the core off the piece map of the core is inside a hole
            have hin : Inner M Hs r := by
              by_contra h
              exact (mem_sdiff.1 hr).2 (mem_pdarts.2 ⟨mem_core.2 ⟨hrP, htQ, hhQ⟩, h⟩)
            obtain ⟨H, hH, h1, h2⟩ := hin
            exact (mem_cls_iff hd).2 (Or.inr ⟨H, hH, h1, h2⟩)
    · rw [hEw E hE, hEeq]; exact card_le_two.trans hA2
  have hEsdisj : ∀ E ∈ Es, ∀ E' ∈ Es, E ≠ E' → Disjoint E E' := by
    intro E hE E' hE' hne
    refine disjoint_left.2 fun x hx hx' => hne ?_
    rw [hrepE E hE] at hx ⊢
    rw [hrepE E' hE'] at hx' ⊢
    simp only [mem_insert, mem_singleton] at hx hx'
    ext y
    simp only [mem_insert, mem_singleton]
    rcases hx with rfl | rfl <;> rcases hx' with h | h
    · rw [h]
    · rw [h, M.rev_rev]; tauto
    · rw [← h, M.rev_rev]; tauto
    · have := congrArg M.rev h; rw [M.rev_rev, M.rev_rev] at this; rw [this]
  have hpw : Ls.Pairwise fun e e' => Disjoint e.1 e'.1 := by
    rw [hLs, List.pairwise_map]
    exact hlE.1.pairwise_of_forall_ne fun E hE E' hE' hne =>
      hEsdisj E (hlE.2 ▸ List.mem_toFinset.2 hE) E' (hlE.2 ▸ List.mem_toFinset.2 hE') hne
  have hlun : B₀ ∪ lunion Ls = Nf := by
    ext x
    rw [mem_union, mem_lunion]
    constructor
    · rintro (h | ⟨e, he, hx⟩)
      · exact hB₀Nf h
      · obtain ⟨E, hE, rfl⟩ := hmemLs e he
        rw [hrepE E hE] at hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact (mem_sdiff.1 (hrep E hE)).1
        · exact (mem_sdiff.1 (hrevNf _ (hrep E hE))).1
    · intro hx
      by_cases hxB : x ∈ B₀
      · exact Or.inl hxB
      · right
        have hxE : ({x, M.rev x} : Finset D) ∈ Es := mem_image_of_mem _ (mem_sdiff.2 ⟨hx, hxB⟩)
        exact ⟨_, List.mem_map.2 ⟨_, List.mem_toFinset.1 (hlE.2.symm ▸ hxE), rfl⟩, by simp⟩
  -- the total weight
  set W := P.card + K * nTouch M P Hs with hW
  have hsumEs : ∑ E ∈ Es, E.card ≤ (Nf \ B₀).card := by
    rw [← card_biUnion hEsdisj]
    refine card_le_card fun x hx => ?_
    obtain ⟨E, hE, hxE⟩ := mem_biUnion.1 hx
    rw [hrepE E hE] at hxE
    simp only [mem_insert, mem_singleton] at hxE
    rcases hxE with rfl | rfl
    · exact hrep E hE
    · exact hrevNf _ (hrep E hE)
  have hmoved : ∑ d ∈ B₀, lmoved exf Ls d ≤ (Nf \ B₀).card := by
    have e1 : ∀ d, lmoved exf Ls d =
        ∑ E ∈ Es, if d = anc E then ∑ x ∈ E, (1 + exf x) else 0 := fun d => by
      simp only [lmoved, hLs, List.map_map]
      rw [show (∑ E ∈ Es, if d = anc E then ∑ x ∈ E, (1 + exf x) else 0) =
          ((pc.ord Es).map fun E => if d = anc E then ∑ x ∈ E, (1 + exf x) else 0).sum from by
        conv_lhs => rw [← hlE.2]
        exact List.sum_toFinset _ hlE.1]
      rfl
    simp_rw [e1]
    rw [sum_comm]
    refine le_trans (sum_le_sum fun E hE => ?_) hsumEs
    rw [sum_ite_eq' B₀ (anc E)]
    simp only [hancB E hE, ↓reduceIte]
    rw [hEw E hE]
  have hexfsum : ∑ d ∈ B₀, exf d ≤ K * nTouch M P Hs := by
    set Bk := B₀.filter fun d => ∃ H ∈ Hs, M.tail d ∈ H ∧ anch H = d
    have h1 : ∑ d ∈ B₀, exf d = K * Bk.card := by
      rw [card_eq_sum_ones, mul_sum, mul_one, sum_filter]
      exact sum_congr rfl fun d hdB => by simp [exf, hdB]
    rw [h1]
    refine Nat.mul_le_mul_left _ ?_
    have hinj : Set.InjOn (fun d => cls Hs (M.tail d)) (Bk : Set D) := by
      intro x hx y hy e
      obtain ⟨-, H, hH, hxH, rfl⟩ := mem_filter.1 hx
      obtain ⟨-, H', hH', hyH', rfl⟩ := mem_filter.1 hy
      simp only at e
      rw [cls_of_mem hd hH hxH, cls_of_mem hd hH' hyH'] at e
      rw [e]
    rw [← card_image_of_injOn hinj]
    unfold nTouch
    refine (card_le_card fun H hH => ?_).trans (List.toFinset_card_le _)
    obtain ⟨d, hd', rfl⟩ := mem_image.1 hH
    obtain ⟨hdB, H, hH, hdH, -⟩ := mem_filter.1 hd'
    rw [List.mem_toFinset, List.mem_filter, cls_of_mem hd hH hdH]
    exact ⟨hH, by simpa using ⟨M.tail d, hdH, d, hB₀P hdB, rfl⟩⟩
  have htot : ∑ d ∈ B₀, (1 + (exf d + lmoved exf Ls d)) ≤ W := by
    rw [sum_add_distrib, sum_add_distrib, sum_const, smul_eq_mul, mul_one]
    have hNfcard : B₀.card + (Nf \ B₀).card ≤ P.card := by
      rw [← card_union_of_disjoint disjoint_sdiff, union_sdiff_of_subset hB₀Nf]
      exact card_le_card sdiff_subset
    omega
  -- the search and the lift
  have hsq : Nat.sqrt (2 * B₀.card) ≤ Nat.sqrt (2 * P.card) :=
    Nat.sqrt_le_sqrt (by have := card_le_card hB₀P; omega)
  obtain ⟨ρ₀, I₀, hscD, hc⟩ := scertD_spec hd hloopM hAW ch hch B₀.card B₀ σ
    (fun d => exf d + lmoved exf Ls d) rfl hPM ⟨b₀, hb₀⟩ htot (by omega)
  have hc' := scert_lift_list' hd hQdeg hHQ Ls B₀ exf (stable_pdarts (revClosed_core hP.rev) Hs)
    hLsprop hpw hc
  rw [hlun] at hc'
  have hpD : pcertD M pc ch Q P Hs K σ =
      (scertD ch Hs B₀ σ (fun d => exf d + lmoved exf Ls d)).map
        fun r => (Nf, r.1, liftI Hs B₀ r.1 r.2 Ls) := rfl
  rw [hpD, hscD, Option.map_some]
  set ρ := ρ₀
  obtain ⟨hs, hdar, hlen, ⟨xl, hxl, hxle⟩, hdisj, hcls, hcov, hwt⟩ := hc'
  have hρQ : Disjoint ρ.mverts Q := by
    refine disjoint_left.2 fun v hv hvQ => ?_
    rcases ρ.mem_mverts.1 hv with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rcases Nat.lt_or_ge j ρ.k with h | h
      · rw [← ρ.tail_d j h] at hvQ
        exact (hB₀Q _ (hdar _ (ρ.mem_darts.2 ⟨j, h, Or.inl rfl⟩))).1 hvQ
      · rw [show j = ρ.k by omega, ← hxle] at hvQ
        exact (hB₀Q _ hxl).1 hvQ
    · exact (hB₀Q _ (hdar _ (ρ.mem_darts.2 ⟨j, hj, Or.inl rfl⟩))).2 hvQ
  refine ⟨ρ, _, rfl, sdiff_subset, fun d hd' => ?_, hs, hdar, hlen.trans (by omega),
    ⟨xl, hB₀P hxl, hxle⟩, hρQ, hdisj, hcls, hcov, fun X hX => ?_⟩
  · -- the darts left out are inside holes not touched by `Nf`
    rw [sdiff_sdiff_right_self, inf_eq_inter, inter_eq_right.2 (filter_subset _ _)] at hd'
    obtain ⟨hdP, hdi, hdn⟩ := mem_filter.1 hd'
    refine ⟨hdi, fun _ x hx hr => ?_⟩
    by_cases hxB : x ∈ B₀
    · exact hdn x hxB hr
    · obtain ⟨b, hb, hbr⟩ := hanc' x (mem_sdiff.2 ⟨hx, hxB⟩)
      by_cases htQ : M.tail x ∈ Q
      · obtain ⟨H, hH, h1, -⟩ := hdi
        have := hRel_eq_of_not_mem (hQn _ htQ) (hRel_symm hr)
        exact hQn _ htQ (this ▸ subset_hunion hH h1)
      · have : av x = M.tail x := by simp [av, htQ]
        rw [this] at hbr
        exact hdn b hb (hRel_trans' hd hbr hr)
  · -- the weight of an item
    refine (hw_le_wtY hd K exf (hcls X hX).1 (hcls X hX).2 fun H hH ⟨d, hdN, hdH⟩ => ?_).trans
      (hwt X hX)
    -- a hole touched by `Nf` has an anchor
    have hHB : ∃ b ∈ B₀, M.tail b ∈ H := by
      by_cases hdB : d ∈ B₀
      · exact ⟨d, hdB, hdH⟩
      · obtain ⟨b, hb, hbr⟩ := hanc' d (mem_sdiff.2 ⟨hdN, hdB⟩)
        have htQ : M.tail d ∉ Q := fun h => hQn _ h (subset_hunion hH hdH)
        have : av d = M.tail d := by simp [av, htQ]
        rw [this] at hbr
        exact ⟨b, hb, hClosed_of_mem hd hH _ hdH _ (hRel_symm hbr)⟩
    obtain ⟨hAB, hAH⟩ := hhAspec H hHB
    have hex : exf (anch H) = K := by
      have hw : ∃ H' ∈ Hs, M.tail (anch H) ∈ H' ∧ anch H' = anch H := ⟨H, hH, hAH, rfl⟩
      simp only [exf, hAB, hw, and_self, ↓reduceIte]
    exact ⟨anch H, hB₀Nf hAB, hAH, hex.ge⟩

variable (M) in
open Classical in
/-- **The certificate of a piece with an empty core, as a function**: if the piece map is
nonempty, the one-vertex path at the attachment of a pendant dart (`pc.pick` of the piece map,
reversed if it leaves `Q`) and the pairs of darts of the piece map; otherwise the one-vertex path at
the tail of `pc.pick P` and no item. -/
noncomputable def pemptyD (pc : PcChoice D V) (Q : Finset V) (P : Finset D)
    (Hs : List (Finset V)) : Finset D × HPath M × Finset (Finset D) :=
  if (pdarts M P Hs).Nonempty then
    (pdarts M P Hs, (SPath.point (M' := M)
      (if M.tail (pc.pick (pdarts M P Hs)) ∈ Q then M.rev (pc.pick (pdarts M P Hs))
        else pc.pick (pdarts M P Hs))
      (M.tail (if M.tail (pc.pick (pdarts M P Hs)) ∈ Q then M.rev (pc.pick (pdarts M P Hs))
        else pc.pick (pdarts M P Hs)))).toH,
      (pdarts M P Hs).image fun d => ({d, M.rev d} : Finset D))
  else (∅, (SPath.point (M' := M) (pc.pick P) (M.tail (pc.pick P))).toH, ∅)

/-- **`pcert_of_empty` as a function**: `pemptyD` meets `PCertOf`. -/
theorem pcert_of_empty' {S T Q : Finset V}
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) {P : Finset D} {Hs : List (Finset V)}
    (hP : PcOK M S T P Hs) (hI : CInv M Q P Hs) (hP0 : P.Nonempty)
    (hne : pdarts M (core M Q P) Hs = ∅) (K : ℕ) {A L : ℕ} (hA2 : 2 ≤ A) (hL : 1 ≤ L)
    (pc : PcChoice D V) (hpc : pc.OK M Q P Hs) :
    PCertOf (M := M) Q P Hs K A L (pemptyD M pc Q P Hs).1 (pemptyD M pc Q P Hs).2.1
      (pemptyD M pc Q P Hs).2.2 := by
  unfold pemptyD
  have hd := hP.disj
  have hHQ := hI.1
  have hQn : ∀ q ∈ Q, q ∉ hunion Hs := fun q hq h => disjoint_left.1 hHQ h hq
  -- the darts of the piece map are pendant
  have hpend : ∀ d ∈ pdarts M P Hs, M.tail d ∈ Q ∨ M.head d ∈ Q := by
    intro d hd'
    by_contra h
    push Not at h
    have : d ∈ pdarts M (core M Q P) Hs := by
      rw [mem_pdarts] at hd' ⊢; exact ⟨mem_core.2 ⟨hd'.1, h.1, h.2⟩, hd'.2⟩
    rw [hne] at this; simp at this
  by_cases hpd : (pdarts M P Hs).Nonempty
  · simp only [hpd, ↓reduceIte]
    have hy₀ : pc.pick (pdarts M P Hs) ∈ pdarts M P Hs := hpc.pick _ hpd
    set y₀ := pc.pick (pdarts M P Hs) with hy₀def
    -- a pendant dart leaving its attachment
    set y := if M.tail y₀ ∈ Q then M.rev y₀ else y₀ with hydef
    obtain ⟨hy, hyQ⟩ : y ∈ pdarts M P Hs ∧ M.tail y ∉ Q := by
      by_cases h : M.tail y₀ ∈ Q
      · simp only [hydef, h, ↓reduceIte]
        refine ⟨stable_pdarts hP.rev Hs _ hy₀, ?_⟩
        rw [CombMap.tail_rev]; exact fun h' => hQ5 y₀ ⟨h, h'⟩
      · simp only [hydef, h, ↓reduceIte]; exact ⟨hy₀, not_false⟩
    set a := M.tail y
    -- every dart of the piece map leaving a vertex off `Q` leaves the class of `a`
    have hatt : ∀ z ∈ pdarts M P Hs, M.tail z ∉ Q → HRel Hs (M.tail z) a := by
      intro z hz hzQ
      have key : ∀ w, ReflTransGen (fun a b => b ∈ pdarts M P Hs ∧
          (b = M.rev a ∨ HRel Hs (M.tail a) (M.tail b))) y w →
          (M.tail w ∉ Q → HRel Hs (M.tail w) a) ∧ (M.tail w ∈ Q → HRel Hs (M.head w) a) := by
        intro w hw
        induction hw with
        | refl => exact ⟨fun _ => Or.inl rfl, fun h => absurd h hyQ⟩
        | tail _ hst ih =>
          rename_i b c _
          obtain ⟨ih1, ih2⟩ := ih
          obtain ⟨hc, hbc⟩ := hst
          rcases hbc with e | e
          · subst e
            rw [CombMap.tail_rev, CombMap.head_rev]
            refine ⟨fun h => ?_, fun h => ?_⟩
            · by_cases hb : M.tail b ∈ Q
              · exact ih2 hb
              · exact absurd ((hpend _ hc).resolve_left h) (by rw [CombMap.head_rev]; exact hb)
            · by_cases hb : M.tail b ∈ Q
              · exact absurd ⟨hb, h⟩ (hQ5 b)
              · exact ih1 hb
          · by_cases hb : M.tail b ∈ Q
            · have : M.tail c = M.tail b := hRel_eq_of_not_mem (hQn _ hb) (hRel_symm e)
              have hcb : c = b := hQdeg _ hb c b this rfl
              subst hcb; exact ⟨ih1, ih2⟩
            · have hca : HRel Hs (M.tail c) a := hRel_trans' hd (hRel_symm e) (ih1 hb)
              refine ⟨fun _ => hca, fun h => ?_⟩
              exfalso
              -- `c` leaves a vertex of `Q` related to `a`, which is off `Q`
              have : M.tail c = a := by
                rcases hca with e' | ⟨H, hH, h1, -⟩
                · exact e'
                · exact absurd (subset_hunion hH h1) (hQn _ h)
              exact hyQ (this ▸ h)
      exact (key z (hP.conn y hy z hz)).1 hzQ
    set ρ := (SPath.point (M' := M) y a).toH with hρ
    have hm : ρ.mverts = {a} := HPath.toH_point_mverts y a
    have hh : ∀ v, v ∈ newHole Hs ρ.mverts ↔ HRel Hs v a := by
      intro v
      rw [mem_newHole_iff hd ⟨fun j hj => absurd hj (Nat.not_lt_zero _),
        fun i hi j hj _ => by simp [ρ, SPath.toH, SPath.point] at hi hj; omega⟩]
      simp [ρ, SPath.toH, SPath.point]
    set Nf := pdarts M P Hs
    refine ⟨pdarts_subset _ _,
      fun d hd' => ?_, ⟨fun j hj => absurd hj (Nat.not_lt_zero _),
        fun i hi j hj _ => by simp [ρ, SPath.toH, SPath.point] at hi hj; omega⟩,
      fun e he => by simp [ρ, SPath.toH_darts, SPath.point_darts'] at he,
      by simp [ρ, SPath.toH, SPath.point]; omega, ⟨y, pdarts_subset _ _ hy, rfl⟩,
      by rw [hm]; exact disjoint_singleton_left.2 hyQ, ?_, ?_, ?_, ?_⟩
    · -- the darts off the piece map are inside holes
      obtain ⟨hdP, hdN⟩ := mem_sdiff.1 hd'
      have hdi : Inner M Hs d := by
        by_contra h; exact hdN (mem_pdarts.2 ⟨hdP, h⟩)
      refine ⟨hdi, fun hdh x hx hr => hdh ((hh _).2 ?_)⟩
      by_cases hxQ : M.tail x ∈ Q
      · obtain ⟨H, hH, h1, -⟩ := hdi
        have := hRel_eq_of_not_mem (hQn _ hxQ) (hRel_symm hr)
        exact absurd (this ▸ subset_hunion hH h1) (hQn _ hxQ)
      · exact hRel_trans' hd (hRel_symm hr) (hatt x hx hxQ)
    · intro X hX Y hY hXY
      obtain ⟨x, -, rfl⟩ := mem_image.1 hX
      obtain ⟨z, -, rfl⟩ := mem_image.1 hY
      refine disjoint_left.2 fun w hw hw' => hXY ?_
      simp only [mem_insert, mem_singleton] at hw hw'
      ext u; simp only [mem_insert, mem_singleton]
      rcases hw with rfl | rfl <;> rcases hw' with h | h
      · rw [h]
      · rw [h, M.rev_rev]; tauto
      · rw [← h, M.rev_rev]; tauto
      · have := congrArg M.rev h; rw [M.rev_rev, M.rev_rev] at this; rw [this]
    · intro X hX
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hX
      refine ⟨fun w hw => ?_, fun b hb c hbc => ?_⟩
      · simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hx
        · exact stable_pdarts hP.rev Hs _ hx
      · simp only [mem_insert, mem_singleton] at hb ⊢
        rcases hbc.2 with e | ⟨e, hbh⟩
        · rcases hb with rfl | rfl
          · exact Or.inr e
          · exact Or.inl (by rw [e, M.rev_rev])
        · -- the pivot is the pendant vertex
          have hbN : b ∈ Nf := by
            rcases hb with rfl | rfl
            · exact hx
            · exact stable_pdarts hP.rev Hs _ hx
          have hbQ : M.tail b ∈ Q := by
            by_contra hbQ; exact hbh ((hh _).2 (hatt b hbN hbQ))
          have : M.tail c = M.tail b := hRel_eq_of_not_mem (hQn _ hbQ) (hRel_symm e)
          rw [hQdeg _ hbQ c b this rfl]; exact hb
    · intro d hd' _
      exact ⟨_, mem_image_of_mem _ hd', by simp⟩
    · intro X hX
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hX
      unfold hw
      have hnone : (Hs.toFinset.filter fun H => Disjoint H ρ.mverts ∧
          ∃ d ∈ ({x, M.rev x} : Finset D), M.tail d ∈ H) = ∅ := by
        refine filter_eq_empty_iff.2 fun H hH ⟨hHC, d, hdX, hdH⟩ => ?_
        have hdN : d ∈ Nf := by
          simp only [mem_insert, mem_singleton] at hdX
          rcases hdX with rfl | rfl
          · exact hx
          · exact stable_pdarts hP.rev Hs _ hx
        have hdQ : M.tail d ∉ Q := fun h => hQn _ h (subset_hunion (List.mem_toFinset.1 hH) hdH)
        have := hatt d hdN hdQ
        have hHa : a ∈ H := hClosed_of_mem hd (List.mem_toFinset.1 hH) _ hdH _ this
        rw [hm] at hHC
        exact disjoint_left.1 hHC hHa (mem_singleton_self _)
      rw [hnone, card_empty, mul_zero, add_zero]
      exact card_le_two.trans hA2
  · -- only darts inside holes
    simp only [hpd, ↓reduceIte]
    rw [not_nonempty_iff_eq_empty] at hpd
    have hx : pc.pick P ∈ P := hpc.pick _ hP0
    set x := pc.pick P with hxdef
    have hxi : Inner M Hs x := by
      by_contra h
      have : x ∈ pdarts M P Hs := mem_pdarts.2 ⟨hx, h⟩
      rw [hpd] at this; simp at this
    obtain ⟨H, hH, h1, -⟩ := hxi
    set ρ := (SPath.point (M' := M) x (M.tail x)).toH with hρ
    have hm : ρ.mverts = {M.tail x} := HPath.toH_point_mverts x _
    refine ⟨empty_subset _, fun d hd' => ⟨?_, fun _ _ h => by simp at h⟩,
      ⟨fun j hj => absurd hj (Nat.not_lt_zero _),
        fun i hi j hj _ => by simp [ρ, SPath.toH, SPath.point] at hi hj; omega⟩,
      fun e he => by simp [ρ, SPath.toH_darts, SPath.point_darts'] at he,
      by simp [ρ, SPath.toH, SPath.point]; omega, ⟨x, hx, rfl⟩,
      by rw [hm]; exact disjoint_singleton_left.2 fun h => hQn _ h (subset_hunion hH h1),
      by simp, by simp, by simp, by simp⟩
    rw [sdiff_empty] at hd'
    by_contra h
    have : d ∈ pdarts M P Hs := mem_pdarts.2 ⟨hd', h⟩
    rw [hpd] at this; simp at this

end BKMNW

end PlanarFlow
