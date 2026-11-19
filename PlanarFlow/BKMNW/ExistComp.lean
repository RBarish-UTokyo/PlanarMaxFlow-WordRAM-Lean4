module

public import PlanarFlow.BKMNW.ExistMiller

/-!
# Components of a piece map off a set of vertices, and deleting darts

* `AStep`: the steps of a piece map that do not pivot at a set `Y` of vertices; the components of
  the piece map with `Y` removed are their classes.
* `reach_of_conn`, `conn_of_closed`: **a set of darts closed under the steps avoiding a hole, every
  dart of which reaches the hole, is connected** after contracting the holes. This is how the
  children of a split are shown connected.
* `PMap`: a piece map given by its darts and rotation (the fields of
  `PlanarFlow.BKMNW.PieceInv` with connectivity, no dart inside a hole, and `FOK`); `PMap.del`:
  a component off a hole is again one (`FOK.del`: its faces stay small or around a hole).
* `PMap.small_of_noCut`: **in a piece map whose holes are not cut vertices (`NoCut`), all faces
  are small**, by `PlanarSeparator.Map.not_reach_of_face_twice`.
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
/-- A step of the piece map on the darts `N` (to the reverse dart, or around a vertex). -/
def HStep (N : Finset D) (Hs : List (Finset V)) (a b : D) : Prop :=
  b ∈ N ∧ (b = M.rev a ∨ HRel Hs (M.tail a) (M.tail b))

variable (M) in
/-- A step of the piece map on the darts `N` avoiding the vertices of `Y` as pivots: to the
reverse dart, or around a vertex off `Y`. -/
def AStep (N : Finset D) (Hs : List (Finset V)) (Y : Finset V) (a b : D) : Prop :=
  b ∈ N ∧ (b = M.rev a ∨ (HRel Hs (M.tail a) (M.tail b) ∧ M.tail a ∉ Y))

lemma AStep.hStep {N : Finset D} {Hs : List (Finset V)} {Y : Finset V} {a b : D}
    (h : AStep M N Hs Y a b) : HStep M N Hs a b :=
  ⟨h.1, h.2.imp id fun h => h.1⟩

/-- A set of vertices closed under the relation of the holes. -/
def HClosed (Hs : List (Finset V)) (Y : Finset V) : Prop := ∀ a ∈ Y, ∀ b, HRel Hs a b → b ∈ Y

lemma hRel_trans' {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {a b c : V}
    (h1 : HRel Hs a b) (h2 : HRel Hs b c) : HRel Hs a c := by
  rcases h1 with rfl | ⟨H, hH, ha, hb⟩
  · exact h2
  rcases h2 with rfl | ⟨H', hH', hb', hc⟩
  · exact Or.inr ⟨H, hH, ha, hb⟩
  by_cases e : H = H'
  · subst e; exact Or.inr ⟨H, hH, ha, hc⟩
  · exact absurd hb' (disjoint_left.1 (disjoint_of_pairwise hd hH hH' e) hb)

/-- The avoiding steps are symmetric when `Y` is closed under the relation of the holes. -/
lemma AStep.symm {N : Finset D} {Hs : List (Finset V)} {Y : Finset V} (hY : HClosed Hs Y)
    {a b : D} (ha : a ∈ N) (h : AStep M N Hs Y a b) : AStep M N Hs Y b a := by
  refine ⟨ha, ?_⟩
  rcases h.2 with e | ⟨e, hy⟩
  · exact Or.inl (by rw [e, M.rev_rev])
  · exact Or.inr ⟨hRel_symm e, fun hb => hy (hY _ hb _ (hRel_symm e))⟩

/-- **Every dart reaches the pivots `Y`** by avoiding steps, in a connected piece map with a dart
leaving `Y`. -/
lemma reach_of_conn {N : Finset D} {Hs : List (Finset V)} {Y : Finset V}
    (hc : ∀ x ∈ N, ∀ y ∈ N, ReflTransGen (HStep M N Hs) x y) {y₀ : D} (hy₀ : y₀ ∈ N)
    (hY : M.tail y₀ ∈ Y) {x : D} (hx : x ∈ N) :
    ∃ y ∈ N, M.tail y ∈ Y ∧ ReflTransGen (AStep M N Hs Y) x y := by
  have key : ∀ z, ReflTransGen (HStep M N Hs) x z → z ∈ N →
      (ReflTransGen (AStep M N Hs Y) x z ∨
        ∃ y ∈ N, M.tail y ∈ Y ∧ ReflTransGen (AStep M N Hs Y) x y) := by
    intro z hz
    induction hz with
    | refl => exact fun _ => Or.inl .refl
    | tail h1 hst ih =>
      rename_i b c
      intro hc0
      have hb0 : b ∈ N := by
        rcases h1.cases_tail with h | ⟨_, _, h⟩
        · exact h ▸ hx
        · exact h.1
      rcases ih hb0 with h | h
      · rcases hst.2 with e | e
        · exact Or.inl (h.tail ⟨hc0, Or.inl e⟩)
        · by_cases hbY : M.tail b ∈ Y
          · exact Or.inr ⟨b, hb0, hbY, h⟩
          · exact Or.inl (h.tail ⟨hc0, Or.inr ⟨e, hbY⟩⟩)
      · exact Or.inr h
  rcases key y₀ (hc x hx y₀ hy₀) hy₀ with h | h
  · exact ⟨y₀, hy₀, hY, h⟩
  · exact h

/-- **A set of darts closed under the avoiding steps is connected** after contracting `Y`, when `Y`
is a hole and every dart of the set reaches `Y` inside the set. -/
lemma conn_of_closed {N L : Finset D} {Hs : List (Finset V)} {Y : Finset V} (hYH : Y ∈ Hs)
    (hYc : HClosed Hs Y) (hLN : L ⊆ N)
    (hcl : ∀ a ∈ L, ∀ b, AStep M N Hs Y a b → b ∈ L)
    (hreach : ∀ x ∈ L, ∃ y ∈ N, M.tail y ∈ Y ∧ ReflTransGen (AStep M N Hs Y) x y) :
    ∀ x ∈ L, ∀ y ∈ L, ReflTransGen (HStep M L Hs) x y := by
  -- avoiding steps from `L` stay in `L`
  have hstay : ∀ x ∈ L, ∀ z, ReflTransGen (AStep M N Hs Y) x z →
      z ∈ L ∧ ReflTransGen (HStep M L Hs) x z := by
    intro x hx z hz
    induction hz with
    | refl => exact ⟨hx, .refl⟩
    | tail _ hst ih =>
      obtain ⟨hb, ih⟩ := ih
      have hc := hcl _ hb _ hst
      exact ⟨hc, ih.tail ⟨hc, (hst.hStep).2⟩⟩
  have hback : ∀ x ∈ L, ∀ z, ReflTransGen (AStep M N Hs Y) x z →
      ReflTransGen (HStep M L Hs) z x := by
    intro x hx z hz
    induction hz with
    | refl => exact .refl
    | tail h1 hst ih =>
      rename_i b c
      have hb := (hstay x hx b h1).1
      have hc := hcl _ hb _ hst
      exact ReflTransGen.head ⟨hb, (hst.symm hYc (hLN hb)).hStep.2⟩ ih
  intro x hx y hy
  obtain ⟨yx, -, hyx, hrx⟩ := hreach x hx
  obtain ⟨yy, -, hyy, hry⟩ := hreach y hy
  have h1 := (hstay x hx yx hrx).2
  have h2 := hback y hy yy hry
  have hyyL := (hstay y hy yy hry).1
  exact (h1.tail ⟨hyyL, Or.inr (Or.inr ⟨Y, hYH, hyx, hyy⟩)⟩).trans h2

/-- The holes are closed under their relation, when pairwise disjoint. -/
lemma hClosed_of_mem {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {H : Finset V}
    (hH : H ∈ Hs) : HClosed Hs H := by
  intro a ha b hab
  rcases hab with rfl | ⟨H', hH', ha', hb⟩
  · exact ha
  by_cases e : H' = H
  · exact e ▸ hb
  · exact absurd ha (disjoint_left.1 (disjoint_of_pairwise hd hH' hH e) ha')

/-! ### Piece maps given by their darts -/

variable (M) in
/-- **A piece map given by its darts** `N` and rotation `τ`, the holes `Hs` contracted: closed
under reversal and rotation, zero Euler gap, the orbits the vertices with the holes contracted,
connected, no dart inside a hole, faces small or around a hole (`FOK`). -/
structure PMap (N : Finset D) (Hs : List (Finset V)) (τ : Perm D) : Prop where
  rev : Stable (revPerm M) N
  stable : Stable τ N
  gap : gap (revPerm M) τ N = 0
  vert : ∀ x ∈ N, ∀ y ∈ N, τ.SameCycle x y ↔ HRel Hs (M.tail x) (M.tail y)
  conn : ∀ x ∈ N, ∀ y ∈ N, ReflTransGen (HStep M N Hs) x y
  inner : ∀ x ∈ N, ¬ Inner M Hs x
  fok : FOK M τ N Hs

lemma PMap.conn' {N : Finset D} {Hs : List (Finset V)} {τ : Perm D} (h : PMap M N Hs τ) :
    ∀ x ∈ N, ∀ y ∈ N, Conn (revPerm M) τ x y := by
  intro x hx y hy
  have key : ∀ z, ReflTransGen (HStep M N Hs) x z → z ∈ N ∧ Conn (revPerm M) τ x z := by
    intro z hz
    induction hz with
    | refl => exact ⟨hx, .refl⟩
    | tail _ hst ih =>
      rename_i b c _
      refine ⟨hst.1, ih.2.trans ?_⟩
      rcases hst.2 with e | e
      · exact .single (Or.inr e)
      · exact conn_of_sameCycle ((h.vert b ih.1 c hst.1).2 e)
  exact (key y (h.conn x hx y hy)).2

/-- **Deleting darts around a hole keeps the faces small or around a hole**: the faces of the darts
`K`, closed under the steps avoiding the hole `g`, are faces of `N` or glued at `g`. -/
theorem FOK.del {N K : Finset D} {Hs : List (Finset V)} {τ : Perm D} (hd : Hs.Pairwise Disjoint)
    (hN : PMap M N Hs τ) {g : Finset V} (hg : g ∈ Hs) (hKN : K ⊆ N)
    (hK : Stable (revPerm M) K) (hcl : ∀ a ∈ K, ∀ b, AStep M N Hs g a b → b ∈ K) :
    FOK M (ret τ K) K Hs := by
  have hψN : Stable (τ * revPerm M) N := hN.stable.mul hN.rev
  have hnext : ∀ z ∈ N, HRel Hs (M.head z) (M.tail ((τ * revPerm M) z)) := fun z hz => by
    have := (hN.vert (M.rev z) (hN.rev z hz) (τ (M.rev z)) (hN.stable _ (hN.rev z hz))).1
      ⟨1, by simp⟩
    simpa [Perm.mul_apply] using this
  have hgc := hClosed_of_mem hd hg
  -- a dart of `K` off `g` has its whole face in `K`
  have key : ∀ z ∈ K, M.tail z ∉ g → M.head z ∉ g → pface M τ N z ⊆ K := by
    intro z hz ht hh w hw
    have hwN := (mem_pface.1 hw).1
    have hzN := hKN hz
    have hrz : M.rev z ∈ K := hcl z hz _ ⟨hN.rev z hzN, Or.inl rfl⟩
    rcases hN.fok z hzN with hs | ⟨H, hH, hal⟩
    · rcases hs w hw with rfl | rfl | rfl
      · exact hz
      · exact hcl _ hrz _ ⟨hwN, Or.inr ⟨by rw [CombMap.tail_rev]; exact hnext z hzN,
          by rw [CombMap.tail_rev]; exact hh⟩⟩
      · have h1 := hnext _ hwN
        rw [Equiv.apply_symm_apply] at h1
        have hrw : M.rev ((τ * revPerm M).symm z) ∈ K := hcl z hz _
          ⟨hN.rev _ hwN, Or.inr ⟨by rw [CombMap.tail_rev]; exact hRel_symm h1, ht⟩⟩
        have := hcl _ hrw _ ⟨hwN, Or.inl (M.rev_rev _).symm⟩
        exact this
    · by_cases e : H = g
      · subst e
        rcases hal z (self_mem_pface hzN) with h | h
        · exact absurd h ht
        · exact absurd h hh
      · have hHg : Disjoint H g := disjoint_of_pairwise hd hH hg e
        -- a dart of `K` leaving the vertex of `H` met by `z`
        obtain ⟨u, hu, huH⟩ : ∃ u ∈ K, M.tail u ∈ H := by
          rcases hal z (self_mem_pface hzN) with h | h
          · exact ⟨z, hz, h⟩
          · exact ⟨M.rev z, hrz, by rw [CombMap.tail_rev]; exact h⟩
        have huN := hKN hu
        have hug : M.tail u ∉ g := fun h => disjoint_left.1 hHg huH h
        rcases hal w hw with h | h
        · exact hcl u hu w ⟨hwN, Or.inr ⟨Or.inr ⟨H, hH, huH, h⟩, hug⟩⟩
        · have hrw : M.rev w ∈ K := hcl u hu _ ⟨hN.rev w hwN,
            Or.inr ⟨Or.inr ⟨H, hH, huH, by rw [CombMap.tail_rev]; exact h⟩, hug⟩⟩
          exact hcl _ hrw _ ⟨hwN, Or.inl (M.rev_rev _).symm⟩
  intro x hx
  by_cases hall : ∀ z ∈ pface M (ret τ K) K x, pface M τ N z ⊆ K
  · have hxs := hall x (self_mem_pface hx)
    have e := pface_ret_of_subset hψN hKN hK hx hxs
    rw [e]
    rcases hN.fok x (hKN hx) with hs | ⟨H, hH, hal⟩
    · left
      intro z hz
      rcases hs z hz with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (ret_mul_rev_eq hK hx (hxs hz)).symm)
      · refine Or.inr (Or.inr ?_)
        have h1 : (ret τ K * revPerm M) ((τ * revPerm M).symm x) = x := by
          rw [ret_mul_rev_eq hK (hxs hz) (by rw [Equiv.apply_symm_apply]; exact hx),
            Equiv.apply_symm_apply]
        exact ((Equiv.symm_apply_eq _).2 h1.symm).symm
    · exact Or.inr ⟨H, hH, hal⟩
  · push Not at hall
    obtain ⟨z₀, hz₀, hz₀n⟩ := hall
    refine Or.inr ⟨g, hg, fun z hz => ?_⟩
    by_contra hne
    push Not at hne
    have hzK := (mem_pface.1 hz).1
    have hs := key z hzK hne.1 hne.2
    have e := pface_ret_of_subset hψN hKN hK hzK hs
    have hz₀' : z₀ ∈ pface M (ret τ K) K z := by rw [pface_eq_of_mem hz]; exact hz₀
    rw [e] at hz₀'
    exact hz₀n (by rw [pface_eq_of_mem hz₀']; exact hs)

/-- **A set of darts closed under the steps avoiding a hole, and connected, is a piece map**, with
the rotation cut down to it. -/
theorem PMap.del {N K : Finset D} {Hs : List (Finset V)} {τ : Perm D} (hd : Hs.Pairwise Disjoint)
    (hN : PMap M N Hs τ) {g : Finset V} (hg : g ∈ Hs) (hKN : K ⊆ N)
    (hK : Stable (revPerm M) K) (hcl : ∀ a ∈ K, ∀ b, AStep M N Hs g a b → b ∈ K)
    (hc : ∀ x ∈ K, ∀ y ∈ K, ReflTransGen (HStep M K Hs) x y) : PMap M K Hs (ret τ K) where
  rev := hK
  stable := stable_ret _ _
  gap := gap_ret_eq_zero (revPerm_isInv M) hN.stable hN.rev hKN hK hN.gap
  vert x hx y hy := (sameCycle_ret hx hy).trans (hN.vert x (hKN hx) y (hKN hy))
  conn := hc
  inner x hx := hN.inner x (hKN hx)
  fok := FOK.del hd hN hg hKN hK hcl

variable (M) in
/-- **No hole is a cut vertex** of the piece map on the darts `N`: any two darts leaving vertices
off a hole are joined by steps avoiding it. -/
def NoCut (N : Finset D) (Hs : List (Finset V)) : Prop :=
  ∀ g ∈ Hs, ∀ x ∈ N, ∀ y ∈ N, M.tail x ∉ g → M.tail y ∉ g → ReflTransGen (AStep M N Hs g) x y

/-- **In a piece map whose holes are not cut vertices all faces are small**: a face around a hole
with at least four darts meets the hole twice, which would separate the following corners
(`PlanarSeparator.Map.not_reach_of_face_twice`). -/
theorem PMap.small_of_noCut {N : Finset D} {Hs : List (Finset V)} {τ : Perm D}
    (hd : Hs.Pairwise Disjoint) (hloopM : ∀ d, M.head d ≠ M.tail d) (hN : PMap M N Hs τ)
    {x₀ : D} (hx₀ : x₀ ∈ N) (hnc : NoCut M N Hs) :
    ∀ x ∈ N, ∀ z ∈ pface M τ N x, z = x ∨ z = (τ * revPerm M) x ∨ z = (τ * revPerm M).symm x := by
  intro x hx
  rcases hN.fok x hx with hs | ⟨H, hH, hal⟩
  · exact hs
  by_contra hns
  push Not at hns
  obtain ⟨z, hz, hz1, hz2, hz3⟩ := hns
  set ψ := τ * revPerm M with hψ
  have hψN : Stable ψ N := hN.stable.mul hN.rev
  have hHc := hClosed_of_mem hd hH
  -- the period of the face is at least four
  have hp : 4 ≤ minimalPeriod ψ x := by
    by_contra hp
    push Not at hp
    obtain ⟨n, hn⟩ := sameCycle_iff.1 (mem_pface.1 hz).2
    have hpos := period_pos ψ x
    have e := iterate_mod ψ x n
    rw [hn] at e
    have hper := iterate_period ψ x
    interval_cases h : minimalPeriod ψ x
    · have : n % 1 = 0 := Nat.mod_one n
      rw [this] at e; exact hz1 e.symm
    · rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
      · rw [h2] at e; exact hz1 e.symm
      · rw [h2] at e; exact hz2 (by rw [← e]; rfl)
    · have h3 : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
      interval_cases hm : n % 3
      · exact hz1 e.symm
      · exact hz2 (by rw [← e]; rfl)
      · refine hz3 ?_
        rw [← e, Equiv.eq_symm_apply]
        have : ψ^[3] x = x := hper
        simpa [iterate_succ_apply'] using this
  -- two darts of the face leaving `H`
  have hend : ∀ i, ∃ j, i ≤ j ∧ j ≤ i + 1 ∧ M.tail (ψ^[j] x) ∈ H := by
    intro i
    have hmem : ψ^[i] x ∈ pface M τ N x :=
      mem_pface.2 ⟨hψN.iterate hx i, sameCycle_iterate _ _ _⟩
    rcases hal _ hmem with h | h
    · exact ⟨i, le_rfl, by omega, h⟩
    · refine ⟨i + 1, by omega, le_rfl, ?_⟩
      have hi := hψN.iterate hx i
      have := (hN.vert (M.rev (ψ^[i] x)) (hN.rev _ hi) (τ (M.rev (ψ^[i] x)))
        (hN.stable _ (hN.rev _ hi))).1 ⟨1, by simp⟩
      rw [CombMap.tail_rev] at this
      rw [iterate_succ_apply']
      exact hHc _ h _ this
  obtain ⟨i, hi0, hi1, hiH⟩ := hend 0
  obtain ⟨j, hj0, hj1, hjH⟩ := hend 2
  set y := ψ^[i] x with hy
  set y' := ψ^[j] x with hy'
  have hyN : y ∈ N := hψN.iterate hx i
  have hy'N : y' ∈ N := hψN.iterate hx j
  have hyy' : y ≠ y' := fun e => by
    have := iterate_inj (by omega) (by omega) e; omega
  -- the heads of `y` and `y'` are joined avoiding `H`
  have hny : ∀ w ∈ N, M.tail w ∈ H → M.head w ∉ H := fun w hw ht hh =>
    hN.inner w hw ⟨H, hH, ht, hh⟩
  have hreach := hnc H hH (M.rev y) (hN.rev _ hyN) (M.rev y') (hN.rev _ hy'N)
    (by rw [CombMap.tail_rev]; exact hny y hyN hiH)
    (by rw [CombMap.tail_rev]; exact hny y' hy'N hjH)
  -- in the piece map of `PlanarSeparator`
  have hσ := hN.stable
  have hB := hN.rev
  set Ns := psep M hσ hB with hNs
  have hsc : ∀ u w : SDart N, Ns.vert u = Ns.vert w ↔ HRel Hs (M.tail u.1) (M.tail w.1) :=
    fun u w => (psep_vert_eq hσ hB).trans (hN.vert _ u.2 _ w.2)
  have hl : ∀ d, Ns.vert (Ns.α d) ≠ Ns.vert d := by
    intro d h
    rw [hsc, psep_α, CombMap.tail_rev] at h
    rcases h with e | ⟨H', hH', h1, h2⟩
    · exact hloopM d.1 e
    · exact hN.inner d.1 d.2 ⟨H', hH', h2, h1⟩
  set Y : SDart N := ⟨y, hyN⟩
  set Y' : SDart N := ⟨y', hy'N⟩
  have hYY : Y ≠ Y' := fun e => hyy' (congrArg Subtype.val e)
  have hf : Ns.φ.SameCycle Y Y' := by
    rw [← PlanarSeparator.Map.face_eq_face_iff, psep_face_eq hσ hB]
    exact (sameCycle_iterate ψ x i).symm.trans (sameCycle_iterate ψ x j)
  have hv : Ns.vert Y = Ns.vert Y' := (hsc Y Y').2 (Or.inr ⟨H, hH, hiH, hjH⟩)
  have hNp : Ns.IsPlane := psep_isPlane hσ hB hx₀ hN.conn' hN.gap
  refine PlanarSeparator.Map.not_reach_of_face_twice hNp hl hYY hf hv ?_
  -- convert the steps avoiding `H`
  have hoff : ∀ w : SDart N, M.tail w.1 ∉ H → Ns.vert w ≠ Ns.vert Y := fun w hw e =>
    hw (hHc _ hiH _ (hRel_symm ((hsc w Y).1 e)))
  have key : ∀ z, ReflTransGen (AStep M N Hs H) (M.rev y) z → z ∈ N →
      (∀ hz : z ∈ N, M.tail z ∉ H →
        ReflTransGen (fun a b => (b = Ns.α a ∨ Ns.vert b = Ns.vert a) ∧ Ns.vert b ≠ Ns.vert Y)
          (Ns.α Y) ⟨z, hz⟩) ∧
      (∀ hz : z ∈ N, M.tail z ∈ H → M.tail (M.rev z) ∉ H ∧
        ReflTransGen (fun a b => (b = Ns.α a ∨ Ns.vert b = Ns.vert a) ∧ Ns.vert b ≠ Ns.vert Y)
          (Ns.α Y) ⟨M.rev z, hB _ hz⟩) := by
    intro z hz
    induction hz with
    | refl =>
      intro _
      refine ⟨fun _ _ => .refl, fun _ h => absurd h ?_⟩
      rw [CombMap.tail_rev]; exact hny y hyN hiH
    | tail h1 hst ih =>
      rename_i c d
      intro hd0
      have hc0 : c ∈ N := by
        rcases h1.cases_tail with h | ⟨_, _, h⟩
        · exact h ▸ hB _ hyN
        · exact h.1
      obtain ⟨ihn, ihm⟩ := ih hc0
      rcases hst.2 with e | ⟨e, hcH⟩
      · subst e
        refine ⟨fun hz hdH => ?_, fun hz hdH => ?_⟩
        · by_cases hcH : M.tail c ∈ H
          · obtain ⟨-, h⟩ := ihm hc0 hcH
            exact h
          · exact (ihn hc0 hcH).tail ⟨Or.inl rfl, hoff _ hdH⟩
        · refine ⟨by rw [M.rev_rev]; exact (by
            intro hcH'
            exact hny _ hd0 hdH (by rw [CombMap.head_rev]; exact hcH')), ?_⟩
          have hcH : M.tail c ∉ H := fun hcH' =>
            hny _ hd0 hdH (by rw [CombMap.head_rev]; exact hcH')
          have := ihn hc0 hcH
          simpa [M.rev_rev] using this
      · have hdH : M.tail d ∉ H := fun h => hcH (hHc _ h _ (hRel_symm e))
        refine ⟨fun hz _ => (ihn hc0 hcH).tail ⟨Or.inr ((hsc _ _).2 (hRel_symm e)),
          hoff _ hdH⟩, fun _ h => absurd h hdH⟩
  have := (key _ hreach (hB _ hy'N)).1 (hB _ hy'N) (by rw [CombMap.tail_rev]; exact hny y' hy'N hjH)
  exact this

end BKMNW

end PlanarFlow
