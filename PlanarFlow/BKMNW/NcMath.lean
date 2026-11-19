module

public import PlanarFlow.BKMNW.NpPushG
public import PlanarFlow.BKMNW.FixIndep
public import PlanarFlow.NegSSSP.KEncReach
public import PlanarFlow.BKMNW.StCall

/-!
# The mathematics of `c2sP`: the unfolded `c2sG` and the residual reachability by darts

* **`c2sG_eqE`**: on a map where every vertex is the tail of a dart, `c2sG` is
  `f + push β ∅ (fixFrozen e … (f + stflow cap C H) π Del - f)` with **any** dart `e v` at each
  vertex (`fixFrozen_indep`), `β = c2sBeta`, `cap = c2sCap`, `Del = delSet`.
* **The dart graph of the residual reachability** (`rbOb`, `rbOe`, `rbHd`; arcs listed by
  `ol = id`): nodes `0 … m-1` the darts, `m` a source joined to the darts with tail in `X`
  (`src i = 1`), `m + 1` a sink for the others; from the dart `i` the arc to `sg i` (the next
  dart around its tail) and, when it is residual (`res i = 1`), the arc to `rv i` (its reverse,
  whose tail is its head). **`rb_reach`**: for `i < m`, the dart `i` is reached from `m`
  (`BfsAdj`, the search of `NegSSSP.bfsProg`) **iff its tail is reached from `X` by residual paths**
  (`ResAdj M U g`), on a numbered map with transitive rotations; `rb_in` (`BfsIn` of the arrays).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open Finset Function Relation CombMap NsStep NegSSSP

universe w

/-! ### `c2sG` unfolded -/

section Unfold

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-- **`c2sG` with any dart at each vertex.** -/
theorem c2sG_eqE (e : V → D) (he : ∀ v, M.tail (e v) = v) (push : PushFn D V)
    (mssp : List D → (D → ℤ) → F → F → Option ℤ) (fr : FRFun F)
    (neg : (D → ℤ) → Option (F → ℤ)) (stflow : (D → ℤ) → Finset V → Finset V → D → ℤ)
    (U f : D → ℤ) (π : SPath M) (H : Finset V) :
    c2sG M push mssp fr neg stflow U f π H =
      f + push (c2sBeta M U f π.verts) ∅
        (fixFrozen M e he mssp fr neg U (f + stflow (c2sCap M U f π.verts) π.verts H) π
          (delSet M U f π.verts) - f) := by
  have hall : ∀ v, ∃ d, M.tail d = v := fun v => ⟨e v, he v⟩
  unfold c2sG
  simp only [hall, implies_true, ↓reduceDIte]
  rw [fixFrozen_indep (fun v => (hall v).choose_spec) he]

/-- `s2cG` is `c2sG` on the reversed capacities and the opposite flow, negated. -/
lemma s2cG_eq (push : PushFn D V) (mssp : List D → (D → ℤ) → F → F → Option ℤ) (fr : FRFun F)
    (neg : (D → ℤ) → Option (F → ℤ)) (stflow : (D → ℤ) → Finset V → Finset V → D → ℤ)
    (U f : D → ℤ) (π : SPath M) (H : Finset V) :
    s2cG M push mssp fr neg stflow U f π H =
      -(c2sG M push mssp fr neg stflow (fun d => U (M.rev d)) (-f) π H) := rfl

end Unfold

/-! ### The dart graph of the residual reachability -/

/-- First out-arc position of a node. -/
def rbOb (m u : ℕ) : ℕ := if u ≤ m then 2 * u else 3 * m

/-- End of the out-arcs of a node (`res u ∈ {0, 1}`). -/
def rbOe (m : ℕ) (res : ℕ → ℕ) (u : ℕ) : ℕ := if u < m then 2 * u + 1 + res u else 3 * m

/-- The head of an arc position. -/
def rbHd (m : ℕ) (sg rv src : ℕ → ℕ) (a : ℕ) : ℕ :=
  if a < 2 * m then (if a % 2 = 0 then sg (a / 2) else rv (a / 2))
  else if src (a - 2 * m) = 1 then a - 2 * m else m + 1

/-- The arcs of the dart graph. -/
lemma rb_adj_iff {m : ℕ} {res sg rv src : ℕ → ℕ} (hres : ∀ i < m, res i ≤ 1) {u v : ℕ} :
    BfsAdj (rbOb m) (rbOe m res) id (rbHd m sg rv src) u v ↔
      (u < m ∧ (v = sg u ∨ (res u = 1 ∧ v = rv u))) ∨
      (u = m ∧ ∃ i < m, (src i = 1 ∧ v = i) ∨ (src i ≠ 1 ∧ v = m + 1)) := by
  unfold BfsAdj rbOb rbOe rbHd
  constructor
  · rintro ⟨k, h1, h2, h3⟩
    simp only [id] at h3
    by_cases hu : u < m
    · simp only [hu, show u ≤ m by omega, ↓reduceIte] at h1 h2
      have := hres u hu
      left; refine ⟨hu, ?_⟩
      rcases Nat.lt_or_ge k (2 * u + 1) with hk | hk
      · have e : k = 2 * u := by omega
        subst e
        simp only [show 2 * u < 2 * m by omega, ↓reduceIte, Nat.mul_mod_right,
          show 2 * u / 2 = u by omega] at h3
        exact Or.inl h3.symm
      · have e : k = 2 * u + 1 := by omega
        subst e
        simp only [show 2 * u + 1 < 2 * m by omega, ↓reduceIte,
          show (2 * u + 1) % 2 = 1 by omega, show (2 * u + 1) / 2 = u by omega,
          one_ne_zero] at h3
        exact Or.inr ⟨by omega, h3.symm⟩
    · by_cases hum : u = m
      · subst hum
        simp only [lt_irrefl, le_refl, ↓reduceIte] at h1 h2
        right
        refine ⟨rfl, k - 2 * u, by omega, ?_⟩
        simp only [show ¬ k < 2 * u by omega, ↓reduceIte] at h3
        by_cases hs : src (k - 2 * u) = 1
        · simp only [hs, ↓reduceIte] at h3; exact Or.inl ⟨hs, h3.symm⟩
        · simp only [hs, ↓reduceIte] at h3; exact Or.inr ⟨hs, h3.symm⟩
      · simp only [hu, show ¬ u ≤ m by omega, ↓reduceIte] at h1 h2; omega
  · rintro (⟨hu, hv | ⟨hr, hv⟩⟩ | ⟨rfl, i, hi, ⟨hs, hv⟩ | ⟨hs, hv⟩⟩)
    · refine ⟨2 * u, by simp [hu, show u ≤ m by omega], by simp [hu]; omega, ?_⟩
      simp only [id, show 2 * u < 2 * m by omega, ↓reduceIte, Nat.mul_mod_right,
        show 2 * u / 2 = u by omega, hv]
    · refine ⟨2 * u + 1, by simp [hu, show u ≤ m by omega], by simp [hu, hr], ?_⟩
      simp only [id, show 2 * u + 1 < 2 * m by omega, ↓reduceIte,
        show (2 * u + 1) % 2 = 1 by omega, show (2 * u + 1) / 2 = u by omega, one_ne_zero, hv]
    · refine ⟨2 * u + i, by simp, by simp; omega, ?_⟩
      simp only [id, show ¬ 2 * u + i < 2 * u by omega, ↓reduceIte,
        show 2 * u + i - 2 * u = i by omega, hs, hv]
    · refine ⟨2 * u + i, by simp, by simp; omega, ?_⟩
      simp only [id, show ¬ 2 * u + i < 2 * u by omega, ↓reduceIte,
        show 2 * u + i - 2 * u = i by omega, hs, hv]

section Reach

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {en : ℕ → D} {m : ℕ}

variable (M en m) in
/-- The index of the next dart around the tail. -/
noncomputable def sgI (i : ℕ) : ℕ := ixOf en m (M.rot (en i))

/-- **The dart graph reaches exactly the darts whose tail is reached by residual paths.** -/
theorem rb_reach (h : EnumOK M en m) (hrot : M.RotTrans) (hV : ∀ v, ∃ d, M.tail d = v)
    {U g : D → ℤ} {X : Finset V} {res src : ℕ → ℕ}
    (hres : ∀ i < m, res i = if g (en i) < U (en i) then 1 else 0)
    (hsrc : ∀ i < m, src i = if M.tail (en i) ∈ X then 1 else 0) {i : ℕ} (hi : i < m) :
    ReflTransGen (BfsAdj (rbOb m) (rbOe m res) id (rbHd m (sgI M en m) (rvI M en m) src)) m i ↔
      ∃ x ∈ X, ReflTransGen (ResAdj M U g) x (M.tail (en i)) := by
  classical
  have hres1 : ∀ i < m, res i ≤ 1 := fun i hi => by rw [hres i hi]; split_ifs <;> omega
  set A := BfsAdj (rbOb m) (rbOe m res) id (rbHd m (sgI M en m) (rvI M en m) src) with hA
  have adj := fun {u v : ℕ} => rb_adj_iff (sg := sgI M en m) (rv := rvI M en m) (src := src)
    hres1 (u := u) (v := v)
  -- moving around a vertex
  have hsg : ∀ u < m, A u (sgI M en m u) := fun u hu => adj.2 (Or.inl ⟨hu, Or.inl rfl⟩)
  have hsg_lt : ∀ u, sgI M en m u < m := fun u => ixOf_lt h _
  have around : ∀ j < m, ReflTransGen A m j → ∀ k < m, M.tail (en k) = M.tail (en j) →
      ReflTransGen A m k := by
    intro j hj hr k hk e
    obtain ⟨n, hn⟩ := hrot (en j) (en k) e.symm
    have key : ∀ n, ReflTransGen A m (ixOf en m (M.rot^[n] (en j))) := by
      intro n
      induction n with
      | zero => simp only [Function.iterate_zero, id, ixOf_en h hj]; exact hr
      | succ n ih =>
        refine ih.tail ?_
        have := hsg _ (ixOf_lt h (M.rot^[n] (en j)))
        unfold sgI at this
        rwa [en_ixOf h, ← Function.iterate_succ_apply' M.rot] at this
    have := key n
    rwa [hn, ixOf_en h hk] at this
  constructor
  · -- the invariant of the reached nodes
    intro hr
    let Q : ℕ → Prop := fun n => n = m ∨ n = m + 1 ∨
      (n < m ∧ ∃ x ∈ X, ReflTransGen (ResAdj M U g) x (M.tail (en n)))
    have step : ∀ u v, A u v → Q u → Q v := by
      intro u v huv hu
      rcases adj.1 huv with ⟨hu', hv | ⟨hr1, hv⟩⟩ | ⟨rfl, k, hk, ⟨hs, hv⟩ | ⟨hs, hv⟩⟩
      · rcases hu with hu | hu | ⟨-, x, hx, hxr⟩
        · omega
        · omega
        · right; right
          refine ⟨hv ▸ hsg_lt u, x, hx, ?_⟩
          rw [hv]; unfold sgI; rw [en_ixOf h, tail_rot]; exact hxr
      · rcases hu with hu | hu | ⟨-, x, hx, hxr⟩
        · omega
        · omega
        · right; right
          have hlt : g (en u) < U (en u) := by
            have := hres u hu'; rw [hr1] at this
            split_ifs at this with hlt; exact hlt
          refine ⟨hv ▸ ixOf_lt h _, x, hx, hxr.tail ⟨en u, rfl, ?_, hlt⟩⟩
          rw [hv]; unfold rvI; rw [en_ixOf h, tail_rev]
      · right; right
        subst hv
        refine ⟨hk, M.tail (en v), ?_, .refl⟩
        have := hsrc v hk; rw [hs] at this
        split_ifs at this with hx; exact hx
      · right; left; exact hv
    have hQ' : ∀ n, ReflTransGen A m n → Q n := by
      intro n hn
      induction hn with
      | refl => exact Or.inl rfl
      | tail _ hbc ih => exact step _ _ hbc ih
    rcases hQ' i hr with e | e | ⟨-, hx⟩
    · omega
    · omega
    · exact hx
  · rintro ⟨x, hx, hxr⟩
    suffices H : ∀ b, ReflTransGen (ResAdj M U g) x b → ∀ k < m, M.tail (en k) = b →
        ReflTransGen A m k from H _ hxr i hi rfl
    intro b hb
    induction hb with
    | refl =>
      intro k hk e
      obtain ⟨d, hd⟩ := hV x
      have hj := ixOf_lt h d
      have hs : src (ixOf en m d) = 1 := by
        rw [hsrc _ hj, en_ixOf h, hd]; simp [hx]
      have hm : A m (ixOf en m d) := adj.2 (Or.inr ⟨rfl, _, hj, Or.inl ⟨hs, rfl⟩⟩)
      exact around _ hj (.single hm) k hk (by rw [e, en_ixOf h, hd])
    | tail _ hbc ih =>
      rename_i b' c'
      obtain ⟨d, h1, h2, h3⟩ := hbc
      intro k hk e
      have hj := ixOf_lt h d
      have rj := ih _ hj (by rw [en_ixOf h, h1])
      have hr : res (ixOf en m d) = 1 := by rw [hres _ hj, en_ixOf h]; simp [h3]
      have hst : A (ixOf en m d) (rvI M en m (ixOf en m d)) :=
        adj.2 (Or.inl ⟨hj, Or.inr ⟨hr, rfl⟩⟩)
      refine around _ (ixOf_lt h _) (rj.tail hst) k hk ?_
      rw [e]; simp only [rvI, en_ixOf h, tail_rev, h2]

end Reach

end NcStep

end BKMNW

end PlanarFlow
