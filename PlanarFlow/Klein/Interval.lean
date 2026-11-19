module

public import PlanarFlow.MSSP.NonCrossing
public import PlanarFlow.Plane.Pivot
public import PlanarFlow.BKMNW.CutBuild
public import PlanarFlow.Plane.Rotation

/-!
# Each dart pivots in at most once around a face

The analysis of Klein's multiple-source shortest paths (SODA 2005), in the form of Cabello,
Chambers and Erickson (SIAM J. Comput. 42, 2013, Lemma 3.7): as the source moves around the
boundary of a face `f`, the shortest-path tree changes by pivots, and **each dart pivots into the
tree at most once**, so the total number of pivots is at most the number of darts.

The setting is `PlanarFlow.MSSP.Hyp` (a plane map with transitive rotations, a face whose boundary
walk is a simple cycle `g 0, …, g (k - 1)` with the roots `r j = tail (g j)`, positive lengths, no
arc entering a root, unique shortest paths). With unique shortest paths, the shortest-path tree of
the root `r j` is the set of arcs tight for `r j` (`sptree`).

* `exists_hangs`: if an arc `a` is tight for two roots, the shortest paths from the two roots
  meet at a vertex `x`, entering it by different arcs, and continue together to `a`.
* `CombMap.rotBetween_or`: at `x`, the first common arc lies on one side or the other of the two
  arcs entering `x`, in the rotation.
* `hyp_shift`: the setting is invariant under a cyclic shift of the face cycle.
* `tight_interval`: **the roots for which an arc is tight form a cyclic interval** (from
  `PlanarFlow.MSSP.dist_hangs`, the non-crossing of shortest paths from a face, by the Jordan
  curve theorem), when all the roots reach the same vertices off the face (`SameReach`).
* `sum_card_sptree_le`: **the total number of pivots**, the darts entering the tree as the source
  moves from `r j` to `r ((j + 1) % k)` for every `j < k`, is at most the number of darts.
* `edge_hyp`: the hypotheses `Hyp` and `SameReach` can be met together (the map of a single
  edge, whose face has two roots; a witness of satisfiability only).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace CombMap

variable {D V F : Type*} (M : CombMap D V F)

/-- **The two sides at a vertex**: an arc `e ≠ b` in the rotation orbit of `b` comes after `b` and
not after `c`, or after `c` and not after `b`. -/
lemma rotBetween_or {b c e : D} (hn : ∃ n, M.rot^[n] b = e) (hb : e ≠ b) :
    M.RotBetween b c e ∨ M.RotBetween c b e := by
  classical
  have hex : ∃ i, 0 < i ∧ M.rot^[i] b = e := by
    obtain ⟨n, hn⟩ := hn
    refine ⟨n, Nat.pos_of_ne_zero fun h => ?_, hn⟩
    subst h; exact hb hn.symm
  generalize hi : Nat.find hex = i
  have hi1 : 0 < i ∧ M.rot^[i] b = e := hi ▸ Nat.find_spec hex
  have hmin : ∀ i', 0 < i' → i' < i → M.rot^[i'] b ≠ e := fun i' h0 hlt h =>
    Nat.find_min hex (hi ▸ hlt) ⟨h0, h⟩
  by_cases hj : ∃ j, 0 < j ∧ j < i ∧ M.rot^[j] b = c
  · right
    obtain ⟨j, hj0, hji, hjc⟩ := hj
    refine ⟨i - j, by omega, ?_, fun j' h0 hlt h => ?_⟩
    · rw [← hjc, ← Function.iterate_add_apply, Nat.sub_add_cancel hji.le]; exact hi1.2
    · apply hmin (i - j - j') (by omega) (by omega)
      rw [← h, ← hjc, ← Function.iterate_add_apply, ← Function.iterate_add_apply,
        show i - j - j' + j' + j = i by omega]
      exact hi1.2
  · left
    push Not at hj
    exact ⟨i, hi1.1, hi1.2, fun j h0 hlt => hj j h0 hlt⟩

end CombMap

namespace Klein

open Finset CombMap MSSP

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

/-! ### Shifting the face cycle -/

lemma mod_shift {k j i : ℕ} (_hk : 0 < k) : ((i + j) % k + 1) % k = ((i + 1) % k + j) % k := by
  rw [Nat.mod_add_mod, Nat.mod_add_mod]; congr 1; ring

lemma faceCycle_shift (hf : FaceCycle M k g) (j : ℕ) : FaceCycle M k fun i => g ((i + j) % k) where
  two_le := hf.two_le
  face i _ := by
    have hk : 0 < k := by have := hf.two_le; omega
    rw [hf.face _ (Nat.mod_lt _ hk), hf.face _ (Nat.mod_lt _ hk)]
  next i _ := by
    have hk : 0 < k := by have := hf.two_le; omega
    rw [hf.next _ (Nat.mod_lt _ hk), mod_shift hk]
  inj i hi i' hi' h := by
    have hk : 0 < k := by have := hf.two_le; omega
    have := hf.inj _ (Nat.mod_lt _ hk) _ (Nat.mod_lt _ hk) h
    have h2 : i ≡ i' [MOD k] := Nat.ModEq.add_right_cancel' j this
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at h2

/-- The shifted index of the root `i` in the cycle shifted by `j`. -/
lemma shift_back {k j i : ℕ} (hj : j < k) (hi : i < k) : ((i + k - j) % k + j) % k = i := by
  rw [Nat.mod_add_mod, show i + k - j + j = i + k by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt hi]

lemma isRoot_shift {j : ℕ} (hj : j < k) {v : V} :
    IsRoot M k (fun i => g ((i + j) % k)) v ↔ IsRoot M k g v := by
  have hk : 0 < k := by omega
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨_, Nat.mod_lt _ hk, h⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨(i + k - j) % k, Nat.mod_lt _ hk, by simp only; rw [shift_back hj hi]⟩

/-- **The setting is invariant under a cyclic shift of the face cycle.** -/
lemma hyp_shift (H : Hyp M k g S ℓ) {j : ℕ} (hj : j < k) :
    Hyp M k (fun i => g ((i + j) % k)) S ℓ where
  plane := H.plane
  rot := H.rot
  face := faceCycle_shift H.face j
  pos := H.pos
  noIn d hd := by rw [isRoot_shift hj]; exact H.noIn d hd
  uniq := H.uniq

/-! ### Where two shortest paths meet -/

section Meet

variable (H : Hyp M k g S ℓ)
include H

local notation "G" => pieceGraph M S ℓ

omit H in
lemma treach2_swap {r₁ r₂ y w : V} (h : TReach2 (M := M) (S := S) (ℓ := ℓ) r₁ r₂ y w) :
    TReach2 (M := M) (S := S) (ℓ := ℓ) r₂ r₁ y w := by
  induction h with
  | refl => exact .refl _
  | tail _ h1 h2 ih => exact .tail ih h2 h1

omit H in
lemma hangs_swap {r₁ r₂ x u : V} {p₁ p₂ e : {d // d ∈ S}} (h : Hangs M S ℓ r₁ r₂ x u p₁ p₂ e) :
    Hangs M S ℓ r₂ r₁ x u p₂ p₁ e :=
  ⟨h.tight₂, h.tight₁, h.dst₂, h.dst₁, Ne.symm h.ne, h.e₂, h.e₁, h.src_e, treach2_swap h.chain⟩

/-- **Where two shortest paths meet**: if an arc `a` is tight for two distinct roots, the shortest
paths from them enter a vertex `x` by different arcs and continue together, by arcs tight for
both, to `a`. -/
theorem exists_hangs {r₁ r₂ : V} (hr₁ : IsRoot M k g r₁) (hr₂ : IsRoot M k g r₂) (hne : r₁ ≠ r₂) :
    ∀ (n : ℕ) (a : {d // d ∈ S}), (dist G r₁ ((G).src a)).toNat = n → Tight G r₁ a →
      Tight G r₂ a → ∃ x p₁ p₂ e, Hangs M S ℓ r₁ r₂ x ((G).dst a) p₁ p₂ e ∧
        TReach G r₁ x ((G).src a) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a hn ha₁ ha₂
    have hz₁ : ((G).src a) ≠ r₁ := fun h => hne (by
      have := H.eq_of_reach_root ha₂.1 (h ▸ hr₁); rw [← h, this])
    have hz₂ : ((G).src a) ≠ r₂ := fun h => hne (by
      have := H.eq_of_reach_root ha₁.1 (h ▸ hr₂); rw [← this, h])
    obtain ⟨q₁, hq₁, hd₁⟩ := exists_tight H.nn ha₁.1 hz₁
    obtain ⟨q₂, hq₂, hd₂⟩ := exists_tight H.nn ha₂.1 hz₂
    by_cases hq : q₁ = q₂
    · subst hq
      have hlt : (dist G r₁ ((G).src q₁)).toNat < n := by
        have h1 := hq₁.2
        have h2 := H.pos' q₁
        have h3 := dist_nonneg H.nn hq₁.1
        rw [hd₁] at h1
        omega
      obtain ⟨x, p₁, p₂, e, hh, ht⟩ := ih _ hlt q₁ rfl hq₁ hq₂
      rw [hd₁] at hh
      exact ⟨x, p₁, p₂, e, { hh with chain := hh.chain.tail ha₁ ha₂ },
        hd₁ ▸ ht.tail hq₁⟩
    · exact ⟨_, q₁, q₂, a, ⟨hq₁, hq₂, hd₁, hd₂, hq, ha₁, ha₂, rfl, .refl _⟩, .refl _⟩

/-- An arc tight for `r₁` after the meeting vertex `x` is tight for every root `r` whose shortest
paths to its head pass through `x`. -/
lemma tight_of_dist {r₁ r x : V} {a : {d // d ∈ S}} (ha : Tight G r₁ a) (hx₁ : Reach G r₁ x)
    (hz : TReach G r₁ x ((G).src a)) (hx : Reach G r x)
    (hd : dist G r ((G).dst a) = dist G r x + dist G x ((G).dst a)) : Tight G r a := by
  obtain ⟨hxz, e1⟩ := hz.dist_eq H.nn hx₁
  obtain ⟨-, e2⟩ := (hz.tail ha).dist_eq H.nn hx₁
  have e3 := ha.2
  have hrz : Reach G r ((G).src a) := hx.trans hxz
  have e4 := dist_triangle H.nn hx hxz
  have e5 := dist_arc H.nn hrz
  exact ⟨hrz, by omega⟩

end Meet

/-! ### The interval -/

/-- **All the roots reach the same vertices off the face.** -/
def SameReach (M : CombMap D V F) (k : ℕ) (g : ℕ → D) (S : Finset D) (ℓ : D → ℤ) : Prop :=
  ∀ i < k, ∀ j < k, ∀ v, ¬ IsRoot M k g v →
    Reach (pieceGraph M S ℓ) (M.tail (g i)) v → Reach (pieceGraph M S ℓ) (M.tail (g j)) v

section Interval

variable (H : Hyp M k g S ℓ)
include H

local notation "G" => pieceGraph M S ℓ

/-- **The roots for which an arc is tight form a cyclic interval** (Cabello, Chambers and
Erickson, Lemma 3.7). -/
theorem tight_interval (hR : SameReach M k g S ℓ) (a : {d // d ∈ S}) :
    Pivot.CycInterval k fun j => Tight G (M.tail (g j)) a := by
  intro j₁ j₂ h12 hk ht₁ ht₂
  have hne : M.tail (g j₁) ≠ M.tail (g j₂) := fun h =>
    absurd (H.face.inj _ (by omega) _ hk h) (by omega)
  obtain ⟨x, p₁, p₂, e, hh, hz⟩ := exists_hangs H ⟨j₁, by omega, rfl⟩ ⟨j₂, hk, rfl⟩ hne _ a rfl
    ht₁ ht₂
  have hx₁ : Reach G (M.tail (g j₁)) x := hh.dst₁ ▸ hh.tight₁.1.arc
  have hxroot : ¬ IsRoot M k g x := hh.dst₁ ▸ H.noIn p₁.1 p₁.2
  have hxl : ∀ l < k, Reach G (M.tail (g l)) x := fun l hl =>
    hR j₁ (by omega) l hl x hxroot hx₁
  -- the arcs at `x`
  have he₁ : e.1 ≠ M.rev p₁.1 := by
    intro h
    have t1 := hh.tight₁.2
    have t2 := hh.e₁.2
    have hp := H.pos' p₁
    have hq := H.pos' e
    change dist G _ (M.tail p₁.1) + _ = dist G _ (M.head p₁.1) at t1
    change dist G _ (M.tail e.1) + _ = dist G _ (M.head e.1) at t2
    rw [h, M.tail_rev, M.head_rev] at t2
    omega
  have hn : ∃ n, M.rot^[n] (M.rev p₂.1) = e.1 := H.rot _ _ (by
    rw [M.tail_rev, hh.dst₂, hh.src_e])
  have he₂ : e.1 ≠ M.rev p₂.1 := by
    intro h
    have t1 := hh.tight₂.2
    have t2 := hh.e₂.2
    have hp := H.pos' p₂
    have hq := H.pos' e
    change dist G _ (M.tail p₂.1) + _ = dist G _ (M.head p₂.1) at t1
    change dist G _ (M.tail e.1) + _ = dist G _ (M.head e.1) at t2
    rw [h, M.tail_rev, M.head_rev] at t2
    omega
  rcases M.rotBetween_or (c := M.rev p₁.1) hn he₂ with hrb | hrb
  · left
    intro l h1 h2
    have hd := (dist_hangs H h1 h2 h12 hk hh hrb).2 (hxl l (by omega))
    exact tight_of_dist H ht₁ hx₁ hz (hxl l (by omega)) hd
  · right
    -- shift the face cycle so that `j₂` comes first
    have H' := hyp_shift H hk
    have e₂ : M.tail ((fun i => g ((i + j₂) % k)) 0) = M.tail (g j₂) := by
      simp [Nat.mod_eq_of_lt hk]
    have e₁ : M.tail ((fun i => g ((i + j₂) % k)) (j₁ + k - j₂)) = M.tail (g j₁) := by
      simp only; rw [show j₁ + k - j₂ + j₂ = j₁ + k by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    have hh' : Hangs M S ℓ (M.tail ((fun i => g ((i + j₂) % k)) 0))
        (M.tail ((fun i => g ((i + j₂) % k)) (j₁ + k - j₂))) x ((pieceGraph M S ℓ).dst a)
        p₂ p₁ e := by
      rw [e₁, e₂]; exact hangs_swap hh
    intro l hl hl'
    have hl'' : (if j₂ ≤ l then l - j₂ else l + k - j₂) ≤ j₁ + k - j₂ := by split_ifs <;> omega
    have hd := (dist_hangs H' (Nat.zero_le _) hl'' (by omega) (by omega) hh' hrb).2
    have er : M.tail ((fun i => g ((i + j₂) % k)) (if j₂ ≤ l then l - j₂ else l + k - j₂)) =
        M.tail (g l) := by
      simp only
      split_ifs with h
      · rw [show l - j₂ + j₂ = l by omega, Nat.mod_eq_of_lt hl]
      · rw [show l + k - j₂ + j₂ = l + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hl]
    rw [er] at hd
    exact tight_of_dist H ht₁ hx₁ hz (hxl l hl) (hd (hxl l hl))

open Classical in
/-- **The shortest-path tree of the root `r j`**: the arcs tight for `r j` (with unique shortest
paths, one arc entering every vertex reached, other than the root). -/
noncomputable def sptree (M : CombMap D V F) (g : ℕ → D) (S : Finset D) (ℓ : D → ℤ) (j : ℕ) :
    Finset {d // d ∈ S} :=
  univ.filter fun a => Tight (pieceGraph M S ℓ) (M.tail (g j)) a

/-- **Each dart pivots in at most once around the face**: the total number of darts entering the
shortest-path tree as the source moves from `r j` to `r ((j + 1) % k)`, over all `j < k`, is at
most the number of darts. -/
theorem sum_card_sptree_le (hR : SameReach M k g S ℓ) :
    ∑ j ∈ range k, (sptree M g S ℓ ((j + 1) % k) \ sptree M g S ℓ j).card ≤ S.card := by
  classical
  have := Pivot.sum_card_cyc_le (T := sptree M g S ℓ) (k := k) fun a => by
    simpa [sptree] using tight_interval H hR a
  simpa using this

end Interval

/-! ### Satisfiability -/

/-- The rotation system of a single edge (as `PlanarFlow.kEdgeRot`, kept here so that this
file does not depend on the maximum-flow algorithm). -/
def kEdgeRot : Kasteleyn.RotationSystem (⊤ : SimpleGraph (Fin 2)) where
  rot := 1
  fst_rot _ := rfl
  sameCycle_of_fst_eq d d' h := by
    have : d = d' := by
      obtain ⟨⟨a, b⟩, hab⟩ := d
      obtain ⟨⟨a', b'⟩, hab'⟩ := d'
      simp only at h
      subst h
      have : b = b' := by
        simp only [SimpleGraph.top_adj] at hab hab'
        omega
      subst this
      rfl
    exact this ▸ Equiv.Perm.SameCycle.refl _ _

/-- A single edge is a plane graph. -/
theorem kEdgeRot_isPlane : kEdgeRot.IsPlane := by
  refine ⟨SimpleGraph.connected_top, ?_⟩
  have h1 : Fintype.card kEdgeRot.Face = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨kEdgeRot.face ⟨(0, 1), by decide⟩, fun y => ?_⟩
    obtain ⟨⟨⟨a, b⟩, hab⟩, rfl⟩ := kEdgeRot.face_surjective y
    refine kEdgeRot.face_eq_face_iff.2 ?_
    fin_cases a <;> fin_cases b
    · exact absurd hab (by decide)
    · exact Equiv.Perm.SameCycle.refl _ _
    · exact ⟨-1, rfl⟩
    · exact absurd hab (by decide)
  rw [h1]
  decide

/-- The two darts of a single edge. -/
def edgeG (i : ℕ) : (⊤ : SimpleGraph (Fin 2)).Dart :=
  if i = 0 then ⟨(0, 1), by decide⟩ else ⟨(1, 0), by decide⟩

/-- **The hypotheses `Hyp` and `SameReach` can be met together**: the map of a single edge, its
face of two darts, no arcs (a witness of satisfiability only). -/
theorem edge_hyp (ℓ : (⊤ : SimpleGraph (Fin 2)).Dart → ℤ) :
    Hyp (CombMap.ofRotation kEdgeRot) 2 edgeG ∅ ℓ ∧
      SameReach (CombMap.ofRotation kEdgeRot) 2 edgeG ∅ ℓ := by
  have hroot : ∀ v, IsRoot (CombMap.ofRotation kEdgeRot) 2 edgeG v := by
    intro v
    fin_cases v
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
  have hnext : ∀ i < 2,
      (CombMap.ofRotation kEdgeRot).next (edgeG i) = edgeG ((i + 1) % 2) := by
    intro i hi
    interval_cases i <;> rfl
  refine ⟨⟨CombMap.ofRotation_isPlane kEdgeRot_isPlane, MSSP.ofRotation_rotTrans _,
    ⟨le_rfl, fun i hi => ?_, hnext, fun i hi j hj h => ?_⟩, fun d hd => by simp at hd,
    fun d hd => by simp at hd, fun _ a => isEmptyElim a⟩, fun _ _ _ _ v hv => absurd (hroot v) hv⟩
  · interval_cases i
    · rfl
    · have := (CombMap.ofRotation kEdgeRot).face_next (edgeG 0)
      rw [hnext 0 (by norm_num)] at this
      exact this
  · interval_cases i <;> interval_cases j <;> first | rfl | exact absurd h (by decide)

end Klein

end PlanarFlow
