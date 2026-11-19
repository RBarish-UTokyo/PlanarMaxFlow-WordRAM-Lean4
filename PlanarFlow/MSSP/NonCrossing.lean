module

public import PlanarFlow.MSSP.Walk
public import PlanarFlow.MSSP.Winding

/-!
# Non-crossing shortest paths from a face

The structural lemma behind the multiple-source shortest path algorithm of Das, Kipouridis,
Probst Gutenberg and Wulff-Nilsen (SOSA 2022, Lemma 5.4), on a plane combinatorial map.

**Setting** (`Hyp`, the simplifying assumptions of the article, Section 2). A plane map `M` with
transitive rotations; a face whose boundary walk is a simple cycle of darts `g 0, …, g (k - 1)`
(`FaceCycle`), with the *roots* `r i = tail (g i)`; a set `S` of darts (the arcs of the digraph
`pieceGraph M S ℓ`) with positive lengths `ℓ`, none of them entering a root; and unique tight arcs
(`UniqTight`, unique shortest paths).

**The lemma.** Let `j₁ < j₂` be two roots, let the shortest paths from `r j₁` and `r j₂` reach a
vertex `x` by different last arcs `p₁ ≠ p₂`, and let `u` hang from `x` by arcs tight for both
roots, starting with the arc `e` (`Hangs`). If `e` comes, in the rotation at `x`, after the
reverse of `p₂` and not after the reverse of `p₁` (`RotBetween`), then for every root `r j` with
`j₁ ≤ j ≤ j₂`, the shortest paths from `r j` to `u` pass through `x`:
`dist (r j) u = dist (r j) x + dist x u` (`dist_hangs`), and the arcs from `x` to `u` are tight
for `r j` (`tight_hangs`).

**Proof.** The shortest paths from `r j₁` and `r j₂` to `x` and the boundary walk of the face from
`r j₂` back to `r j₁` form a simple cycle (`exists_cycle`; the two paths meet only at `x` by unique
tight arcs). By the winding function of the cycle (`PlanarFlow.CombMap.exists_winding`), the root
`r j` and the vertex `u` are on different sides, so every walk from `r j` to `u` meets the cycle;
it cannot meet it on the face (no arc enters a root), so it meets one of the two shortest paths
(`hit`), and from there the shortest path to `u` passes through `x`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace MSSP

open Finset CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-! ### Walks of darts in the map -/

/-- The darts of a map as a digraph (with lengths `0`): its walks are the walks of the map. -/
def mapGraph (M : CombMap D V F) : Digraph V D := ⟨M.tail, M.head, fun _ => 0⟩

variable {M : CombMap D V F}

lemma lwalk_map {S : Finset D} {ℓ : D → ℤ} {x y : V} {L : List {d // d ∈ S}}
    (h : LWalk (pieceGraph M S ℓ) x y L) : LWalk (mapGraph M) x y (L.map Subtype.val) := by
  induction h with
  | nil => exact .nil _
  | @cons a y l _ ih => exact LWalk.cons (G := mapGraph M) (a := a.1) ih

lemma lwalk_reverse {x y : V} {l : List D} (h : LWalk (mapGraph M) x y l) :
    LWalk (mapGraph M) y x (l.reverse.map M.rev) := by
  induction h with
  | nil => exact .nil _
  | @cons a y l _ ih =>
    rw [List.reverse_cons, List.map_append, List.map_singleton]
    have : (mapGraph M).src (M.rev a) = (mapGraph M).dst a := rfl
    have e : (mapGraph M).dst (M.rev a) = (mapGraph M).src a := by
      change M.head (M.rev a) = M.tail a; simp
    rw [← e]
    exact ih.concat (G := mapGraph M) this

lemma getD_of_lt {α : Type*} {l : List α} {i : ℕ} (h : i < l.length) (a : α) :
    l.getD i a = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- A closed walk of darts with distinct tails, of length at least three, is a simple cycle. -/
lemma isSimpleCycle_of_list {cw : List D} {v : V} (h : LWalk (mapGraph M) v v cw)
    (hnd : (cw.map M.tail).Nodup) (h3 : 3 ≤ cw.length) (d₀ : D) :
    M.IsSimpleCycle cw.length (fun t => cw.getD t d₀) := by
  obtain ⟨hw, -⟩ := isWalk_of_lwalk h d₀
  rcases hw with ⟨h0, -⟩ | ⟨-, hs, hl, hc⟩
  · omega
  refine ⟨h3, fun t ht => ?_, fun s hs t ht hst => ?_⟩
  · rw [succ_mod ht]
    split_ifs with h1
    · have : t = cw.length - 1 := by omega
      subst this; exact hl.trans hs.symm
    · exact hc t (by omega)
  · have e := (List.Nodup.getElem_inj_iff hnd (i := s) (j := t) (hi := by simpa using hs)
      (hj := by simpa using ht)).1
    simp only [List.getElem_map] at e
    rw [getD_of_lt hs, getD_of_lt ht] at hst
    exact e hst

lemma onCyc_list {cw : List D} (d₀ : D) {w : V} :
    M.OnCyc cw.length (fun t => cw.getD t d₀) w ↔ w ∈ cw.map M.tail := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    dsimp only
    rw [getD_of_lt ht]
    exact List.mem_map.2 ⟨_, List.getElem_mem ht, rfl⟩
  · intro hw
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hw
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hd
    exact ⟨t, ht, by dsimp only; rw [getD_of_lt ht]⟩

/-! ### The setting -/

/-- The boundary walk of a face is a simple cycle `g 0, …, g (k - 1)` of `k ≥ 2` darts. -/
structure FaceCycle (M : CombMap D V F) (k : ℕ) (g : ℕ → D) : Prop where
  two_le : 2 ≤ k
  face : ∀ i < k, M.face (g i) = M.face (g 0)
  next : ∀ i < k, M.next (g i) = g ((i + 1) % k)
  inj : ∀ i < k, ∀ j < k, M.tail (g i) = M.tail (g j) → i = j

/-- The vertex `v` is a root: the tail of a boundary dart of the face. -/
def IsRoot (M : CombMap D V F) (k : ℕ) (g : ℕ → D) (v : V) : Prop := ∃ i < k, M.tail (g i) = v

/-- **The simplifying assumptions of the article.** -/
structure Hyp (M : CombMap D V F) (k : ℕ) (g : ℕ → D) (S : Finset D) (ℓ : D → ℤ) : Prop where
  plane : M.IsPlane
  rot : M.RotTrans
  face : FaceCycle M k g
  pos : ∀ d ∈ S, 0 < ℓ d
  noIn : ∀ d ∈ S, ¬ IsRoot M k g (M.head d)
  uniq : UniqTight (pieceGraph M S ℓ)

lemma FaceCycle.lwalk_seg {k : ℕ} {g : ℕ → D} (hf : FaceCycle M k g) {i₀ : ℕ} (hi₀ : i₀ < k)
    (m : ℕ) : LWalk (mapGraph M) (M.tail (g i₀)) (M.tail (g ((i₀ + m) % k)))
      ((List.range m).map fun i => g ((i₀ + i) % k)) := by
  induction m with
  | zero => rw [Nat.add_zero, Nat.mod_eq_of_lt hi₀]; exact .nil _
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_singleton]
    have hq : (i₀ + m) % k < k := Nat.mod_lt _ (by have := hf.two_le; omega)
    have h1 : (mapGraph M).src (g ((i₀ + m) % k)) = M.tail (g ((i₀ + m) % k)) := rfl
    have h2 : (mapGraph M).dst (g ((i₀ + m) % k)) = M.tail (g ((i₀ + (m + 1)) % k)) := by
      change M.head _ = _
      rw [CombMap.head, ← M.tail_next, hf.next _ hq]
      congr 2
      rw [← add_assoc, Nat.add_mod (i₀ + m) 1, Nat.mod_eq_of_lt (a := 1) (by have := hf.two_le; omega)]
    rw [← h2]
    exact ih.concat h1

section Setting

variable {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ} (H : Hyp M k g S ℓ)
include H

local notation "G" => pieceGraph M S ℓ

lemma Hyp.pos' : ∀ a : {d // d ∈ S}, 0 < (G).len a := fun a => H.pos a.1 a.2

lemma Hyp.nn : ∀ a : {d // d ∈ S}, 0 ≤ (G).len a := fun a => (H.pos' a).le

lemma Hyp.not_root_dst (a : {d // d ∈ S}) : ¬ IsRoot M k g ((G).dst a) := H.noIn a.1 a.2

/-- A root reached from a vertex is the vertex itself: no arc enters a root. -/
lemma Hyp.eq_of_reach_root {r y : V} (h : Reach G r y) (hy : IsRoot M k g y) : y = r := by
  by_contra hne
  obtain ⟨a, -, rfl⟩ := exists_tight H.nn h hne
  exact H.not_root_dst a hy

/-- The arcs tight for two sources. -/
inductive TReach2 (r₁ r₂ : V) : V → V → Prop
  | refl (y : V) : TReach2 r₁ r₂ y y
  | tail {y : V} {a : {d // d ∈ S}} : TReach2 r₁ r₂ y ((G).src a) → Tight G r₁ a → Tight G r₂ a →
      TReach2 r₁ r₂ y ((G).dst a)

omit H in
lemma TReach2.left {r₁ r₂ y w : V} (h : TReach2 (M := M) (S := S) (ℓ := ℓ) r₁ r₂ y w) :
    TReach G r₁ y w := by
  induction h with
  | refl => exact .refl _
  | tail _ h1 _ ih => exact .tail ih h1

omit H in
lemma TReach2.right {r₁ r₂ y w : V} (h : TReach2 (M := M) (S := S) (ℓ := ℓ) r₁ r₂ y w) :
    TReach G r₂ y w := by
  induction h with
  | refl => exact .refl _
  | tail _ _ h2 ih => exact .tail ih h2

end Setting

/-- **`u` hangs from `x` for the sources `r₁`, `r₂`**: the shortest paths from `r₁` and `r₂`
enter `x` by different arcs `p₁ ≠ p₂`, and `u` is reached from `x` by arcs tight for both
sources, the first of which is `e`. -/
structure Hangs (M : CombMap D V F) (S : Finset D) (ℓ : D → ℤ) (r₁ r₂ x u : V)
    (p₁ p₂ e : {d // d ∈ S}) : Prop where
  tight₁ : Tight (pieceGraph M S ℓ) r₁ p₁
  tight₂ : Tight (pieceGraph M S ℓ) r₂ p₂
  dst₁ : M.head p₁.1 = x
  dst₂ : M.head p₂.1 = x
  ne : p₁ ≠ p₂
  e₁ : Tight (pieceGraph M S ℓ) r₁ e
  e₂ : Tight (pieceGraph M S ℓ) r₂ e
  src_e : M.tail e.1 = x
  chain : TReach2 (M := M) (S := S) (ℓ := ℓ) r₁ r₂ (M.head e.1) u

section Main

variable {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ} (H : Hyp M k g S ℓ)
include H

local notation "G" => pieceGraph M S ℓ

/-- The shortest path from a source to `x`, ending with the tight arc `p` into `x`. -/
lemma Hyp.exists_sp {r x : V} {p : {d // d ∈ S}} (hp : Tight G r p) (hx : M.head p.1 = x)
    (hxr : x ≠ r) : ∃ L, IsSP G r ((G).src p) L ∧ IsSP G r x (L ++ [p]) := by
  have hr : Reach G r x := hx ▸ hp.1.arc
  obtain ⟨L, hL⟩ := exists_isSP H.nn hr
  rcases List.eq_nil_or_concat L with rfl | ⟨L', a, rfl⟩
  · exact absurd (LWalk.nil_iff.1 hL.1).symm hxr
  rw [List.concat_eq_append] at hL
  obtain ⟨h1, h2, h3⟩ := hL.concat H.nn
  have : a = p := H.uniq r a p h3 hp (by rw [h2]; exact hx.symm) (by rw [h2]; exact hxr)
  subst this
  exact ⟨L', h1, hL⟩

/-- The tails of the arcs of a shortest path to `x`, ending with `p`, lie on tight chains to the
start of `p`. -/
lemma Hyp.mem_sp_src {r x : V} {p : {d // d ∈ S}} {L : List {d // d ∈ S}}
    (hL : IsSP G r ((G).src p) L) (hfull : IsSP G r x (L ++ [p])) {v : V}
    (hv : v ∈ (L ++ [p]).map (G).src) :
    Reach G r v ∧ TReach G r v ((G).src p) ∧ dist G r v < dist G r x := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hv
  obtain ⟨-, -, e1, -⟩ := hfull.mem_src H.nn ha
  have hpa := H.pos' a
  rcases List.mem_append.1 ha with ha | ha
  · obtain ⟨h1, h2, -, -⟩ := hL.mem_src H.nn ha
    exact ⟨h1, h2, by omega⟩
  · obtain rfl := List.mem_singleton.1 ha
    obtain ⟨h1, -, -⟩ := hfull.mem_src H.nn (List.mem_append_right _ (List.mem_singleton_self _))
    exact ⟨h1, .refl _, by omega⟩

/-- The heads of the arcs of a shortest path from `r` to `x`, except `x`, lie on tight chains to
the start of the last arc. -/
lemma Hyp.mem_sp_dst {r : V} {p : {d // d ∈ S}} {L : List {d // d ∈ S}}
    (hL : IsSP G r ((G).src p) L) {v : V} (hv : v ∈ L.map (G).dst) :
    Reach G r v ∧ TReach G r v ((G).src p) ∧ ¬ IsRoot M k g v := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hv
  obtain ⟨h1, h2, -⟩ := hL.mem_dst H.nn ha
  exact ⟨h1, h2, H.not_root_dst a⟩

omit H in
lemma seg_mod {j₂ i k : ℕ} (hj : j₂ < k) (hi : i < k) :
    (j₂ + i) % k = if j₂ + i < k then j₂ + i else j₂ + i - k := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- **The cycle of the article**: the shortest path from `r j₁` to `x`, the reverse of the
shortest path from `r j₂` to `x`, and the boundary walk of the face from `r j₂` to `r j₁`. -/
theorem exists_cycle {j₁ j₂ : ℕ} (h12 : j₁ < j₂) (hk : j₂ < k) {x : V}
    {p₁ p₂ : {d // d ∈ S}} (hp₁ : Tight G (M.tail (g j₁)) p₁) (hp₂ : Tight G (M.tail (g j₂)) p₂)
    (hx₁ : M.head p₁.1 = x) (hx₂ : M.head p₂.1 = x) (hne : p₁ ≠ p₂) :
    ∃ n c, M.IsSimpleCycle n c ∧
      (∀ v, M.OnCyc n c v → (∃ q < k, M.tail (g q) = v ∧ (j₂ ≤ q ∨ q < j₁)) ∨
        (Reach G (M.tail (g j₁)) v ∧ TReach G (M.tail (g j₁)) v x ∧
          dist G (M.tail (g j₁)) v < dist G (M.tail (g j₁)) x) ∨
        (Reach G (M.tail (g j₂)) v ∧ TReach G (M.tail (g j₂)) v x ∧
          dist G (M.tail (g j₂)) v ≤ dist G (M.tail (g j₂)) x ∧ ¬ IsRoot M k g v)) ∧
      (∃ t < n, c t = g j₂) ∧
      (∃ t, 0 < t ∧ t < n ∧ c t = M.rev p₂.1 ∧ c ((t + n - 1) % n) = p₁.1) := by
  have hf := H.face
  generalize hr₁ : M.tail (g j₁) = r₁ at hp₁
  generalize hr₂ : M.tail (g j₂) = r₂ at hp₂
  have hxroot : ¬ IsRoot M k g x := hx₁ ▸ H.not_root_dst p₁
  have hx1 : x ≠ r₁ := fun h => hxroot ⟨j₁, by omega, by rw [hr₁, h]⟩
  have hx2 : x ≠ r₂ := fun h => hxroot ⟨j₂, hk, by rw [hr₂, h]⟩
  obtain ⟨L₁, hL₁, hF₁⟩ := H.exists_sp hp₁ hx₁ hx1
  obtain ⟨L₂, hL₂, hF₂⟩ := H.exists_sp hp₂ hx₂ hx2
  -- the three parts
  generalize hm : k - j₂ + j₁ = m
  generalize hA : (L₁ ++ [p₁]).map Subtype.val = A
  generalize hB : ((L₂ ++ [p₂]).map Subtype.val).reverse.map M.rev = B
  generalize hC : (List.range m).map (fun i => g ((j₂ + i) % k)) = C
  have hwA : LWalk (mapGraph M) r₁ x A := hA ▸ lwalk_map hF₁.1
  have hwB : LWalk (mapGraph M) x r₂ B := hB ▸ lwalk_reverse (lwalk_map hF₂.1)
  have hwC : LWalk (mapGraph M) r₂ r₁ C := by
    have := hf.lwalk_seg hk m
    have e : (j₂ + m) % k = j₁ := by
      rw [← hm, show j₂ + (k - j₂ + j₁) = k + j₁ by omega, Nat.add_mod_left,
        Nat.mod_eq_of_lt (by omega)]
    rwa [e, hr₁, hr₂, hC] at this
  have hw : LWalk (mapGraph M) r₁ r₁ (A ++ (B ++ C)) := hwA.append (hwB.append hwC)
  -- the vertices of the three parts
  have hAv : ∀ v, v ∈ A.map M.tail → Reach G r₁ v ∧ TReach G r₁ v x ∧ dist G r₁ v < dist G r₁ x := by
    intro v hv
    rw [← hA, List.map_map] at hv
    obtain ⟨h1, h2, h3⟩ := H.mem_sp_src hL₁ hF₁ hv
    exact ⟨h1, h2.trans (.tail (.refl _) hp₁ |> fun h => hx₁ ▸ h), h3⟩
  have hBt : B.map M.tail = x :: (L₂.map (G).dst).reverse := by
    rw [← hB, ← hx₂]
    simp only [List.map_append, List.reverse_append, List.map_cons, List.map_reverse, List.map_map,
      CombMap.tail_rev]
    rfl
  have hBv : ∀ v, v ∈ B.map M.tail → Reach G r₂ v ∧ TReach G r₂ v x ∧
      dist G r₂ v ≤ dist G r₂ x ∧ ¬ IsRoot M k g v := by
    intro v hv
    rw [hBt, List.mem_cons, List.mem_reverse] at hv
    rcases hv with rfl | hv
    · exact ⟨hx₂ ▸ hp₂.1.arc, .refl _, le_rfl, hxroot⟩
    · obtain ⟨h1, h2, h3⟩ := H.mem_sp_dst hL₂ hv
      have e2 := h2.dist_le H.pos'
      have := hp₂.2
      have := H.pos' p₂
      exact ⟨h1, h2.trans (hx₂ ▸ .tail (.refl _) hp₂), by
        rw [← hx₂]; change _ ≤ dist G r₂ ((G).dst p₂); omega, h3⟩
  have hCv : ∀ v, v ∈ C.map M.tail → ∃ q < k, M.tail (g q) = v ∧ (j₂ ≤ q ∨ q < j₁) := by
    intro v hv
    rw [← hC, List.map_map] at hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hv
    rw [List.mem_range] at hi
    refine ⟨(j₂ + i) % k, Nat.mod_lt _ (by omega), rfl, ?_⟩
    rw [seg_mod hk (by omega)]
    split_ifs <;> omega
  -- distinct tails
  have hnd : ((A ++ (B ++ C)).map M.tail).Nodup := by
    rw [List.map_append, List.map_append, List.nodup_append, List.nodup_append]
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [← hA, List.map_map]; exact hF₁.nodup_src H.pos'
    · rw [hBt]
      have := hF₂.nodup_dst H.pos'
      rw [List.map_append, List.nodup_append] at this
      refine List.nodup_cons.2 ⟨?_, List.nodup_reverse.2 this.1⟩
      rw [List.mem_reverse]
      intro hxm
      exact this.2.2 _ hxm _ (List.mem_singleton.2 rfl) hx₂.symm
    · rw [← hC, List.map_map]
      refine List.Nodup.map_on (fun i hi i' hi' h => ?_) List.nodup_range
      rw [List.mem_range] at hi hi'
      have := hf.inj _ (Nat.mod_lt _ (by omega)) _ (Nat.mod_lt _ (by omega)) h
      rw [seg_mod hk (by omega), seg_mod hk (by omega)] at this
      split_ifs at this <;> omega
    · intro v hv v' hv' hvv
      subst hvv
      obtain ⟨-, -, -, h4⟩ := hBv v hv
      obtain ⟨q, hq, rfl, -⟩ := hCv _ hv'
      exact h4 ⟨q, hq, rfl⟩
    · intro v hv v' hv' hvv
      subst hvv
      obtain ⟨h1, h2, h3⟩ := hAv v hv
      rcases List.mem_append.1 hv' with hv' | hv'
      · -- the two shortest paths meet only at `x`
        obtain ⟨b1, b2, b3, -⟩ := hBv v hv'
        apply hne
        -- `p₁` and `p₂` are both tight for the source `v`
        have t1 : Tight G v p₁ := by
          have hAt : A.map M.tail = (L₁ ++ [p₁]).map (G).src := by rw [← hA, List.map_map]; rfl
          obtain ⟨a, ha, hav⟩ := List.mem_map.1 (show v ∈ (L₁ ++ [p₁]).map (G).src from hAt ▸ hv)
          obtain ⟨-, c2, -⟩ := H.mem_sp_src hL₁ hF₁ (List.mem_map.2 ⟨a, ha, hav⟩)
          obtain ⟨d1, d2⟩ := c2.dist_eq H.nn h1
          obtain ⟨d3, d4⟩ := (c2.tail hp₁).dist_eq H.nn h1
          refine ⟨d1, ?_⟩
          have := hp₁.2
          change dist G v ((G).src p₁) + (G).len p₁ = dist G v ((G).dst p₁)
          omega
        have t2 : Tight G v p₂ := by
          have hv2 : v ∈ (L₂.map (G).dst) ∨ v = x := by
            rw [hBt, List.mem_cons, List.mem_reverse] at hv'
            exact hv'.symm
          rcases hv2 with hv2 | rfl
          · obtain ⟨-, c2, -⟩ := H.mem_sp_dst hL₂ hv2
            obtain ⟨d1, d2⟩ := c2.dist_eq H.nn b1
            obtain ⟨d3, d4⟩ := (c2.tail hp₂).dist_eq H.nn b1
            refine ⟨d1, ?_⟩
            have := hp₂.2
            change dist G v ((G).src p₂) + (G).len p₂ = dist G v ((G).dst p₂)
            omega
          · omega
        have hvx : v ≠ x := by rintro rfl; omega
        exact H.uniq v p₁ p₂ t1 t2 (by change M.head _ = M.head _; rw [hx₁, hx₂])
          (by change M.head _ ≠ _; rw [hx₁]; exact hvx.symm)
      · -- a vertex of the first path is a root only if it is `r j₁`
        obtain ⟨q, hq, hqv, hq'⟩ := hCv _ hv'
        have := H.eq_of_reach_root h1 ⟨q, hq, hqv⟩
        rw [← hr₁] at this
        have := hf.inj _ hq _ (by omega) (hqv.trans this)
        omega
  -- the cycle
  have hlen : 3 ≤ (A ++ (B ++ C)).length := by
    have : 1 ≤ A.length := by rw [← hA]; simp
    have : 1 ≤ B.length := by rw [← hB]; simp
    have : 1 ≤ C.length := by rw [← hC]; simp; omega
    simp only [List.length_append]; omega
  refine ⟨_, _, isSimpleCycle_of_list hw hnd hlen (g 0), fun v hv => ?_, ?_, ?_⟩
  · rw [onCyc_list, List.map_append, List.map_append] at hv
    rcases List.mem_append.1 hv with hv | hv
    · exact Or.inr (Or.inl (hr₁ ▸ hAv v hv))
    rcases List.mem_append.1 hv with hv | hv
    · exact Or.inr (Or.inr (hr₂ ▸ hBv v hv))
    · exact Or.inl (hCv v hv)
  · refine ⟨A.length + B.length, by simp only [List.length_append]; rw [← hC]; simp; omega, ?_⟩
    rw [getD_of_lt (by simp only [List.length_append]; rw [← hC]; simp; omega)]
    rw [List.getElem_append_right (by simp), List.getElem_append_right (by simp)]
    simp only [← hC, List.getElem_map, List.getElem_range]
    congr; simp; exact Nat.mod_eq_of_lt hk
  · have hBe : B = M.rev p₂.1 :: (L₂.map Subtype.val).reverse.map M.rev := by
      rw [← hB]; simp
    have hAe : A = L₁.map Subtype.val ++ [p₁.1] := by rw [← hA]; simp
    have hAl : 1 ≤ A.length := by rw [hAe]; simp
    have hBl : 1 ≤ B.length := by rw [hBe]; simp
    have hn : A.length < (A ++ (B ++ C)).length := by simp only [List.length_append]; omega
    refine ⟨A.length, hAl, hn, ?_, ?_⟩
    · rw [getD_of_lt hn, List.getElem_append_right (le_refl _)]
      simp [hBe]
    · have : (A.length + (A ++ (B ++ C)).length - 1) % (A ++ (B ++ C)).length =
          A.length - 1 := by
        rw [pred_mod hn]; split_ifs <;> omega
      rw [this, getD_of_lt (by omega), List.getElem_append_left (by omega)]
      simp [hAe]

end Main


section Lemma

variable {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ} (H : Hyp M k g S ℓ)
include H

local notation "G" => pieceGraph M S ℓ

/-- **Every walk from an inner root to a vertex hanging from `x` meets one of the two shortest
paths to `x`** (the planarity step of the article's Lemma 5.4). -/
theorem hit {j₁ j j₂ : ℕ} (h1 : j₁ < j) (h2 : j < j₂) (hk : j₂ < k) {x u : V}
    {p₁ p₂ e : {d // d ∈ S}} (hh : Hangs M S ℓ (M.tail (g j₁)) (M.tail (g j₂)) x u p₁ p₂ e)
    (hrb : M.RotBetween (M.rev p₂.1) (M.rev p₁.1) e.1) {L : List {d // d ∈ S}}
    (hL : LWalk G (M.tail (g j)) u L) :
    ∃ z L₁ L₂, L = L₁ ++ L₂ ∧ LWalk G (M.tail (g j)) z L₁ ∧ LWalk G z u L₂ ∧
      ((Reach G (M.tail (g j₁)) z ∧ TReach G (M.tail (g j₁)) z x) ∨
        (Reach G (M.tail (g j₂)) z ∧ TReach G (M.tail (g j₂)) z x)) := by
  obtain ⟨n, c, hC, hon, ⟨ts, hts, hcts⟩, ⟨t₀, -, ht₀, hc₀, hc₀'⟩⟩ :=
    exists_cycle H (by omega : j₁ < j₂) hk hh.tight₁ hh.tight₂ hh.dst₁ hh.dst₂ hh.ne
  obtain ⟨φ, hφ⟩ := exists_winding H.plane hC
  generalize hr₁ : M.tail (g j₁) = r₁ at hh hon
  generalize hr₂ : M.tail (g j₂) = r₂ at hh hon
  generalize hw : φ (M.face (c 0)) = w
  -- sides of vertices off the cycle
  have hside : ∀ y s, ¬ M.OnCyc n c y → (∃ d, M.tail d = y ∧ φ (M.face d) = s) →
      ∀ d, M.tail d = y → φ (M.face d) = s := by
    rintro y s hy ⟨d₀, hd₀, hs⟩ d hd
    rw [← hs]
    exact side_eq hC hφ H.rot (hd.trans hd₀.symm) (by rwa [hd])
  -- the inner root is off the cycle, on the side of the face
  have hj_off : ¬ M.OnCyc n c (M.tail (g j)) := by
    intro hon'
    rcases hon _ hon' with ⟨q, hq, hqe, hq'⟩ | ⟨hr, -, -⟩ | ⟨hr, -, -, -⟩
    · have := H.face.inj _ hq _ (by omega) hqe; omega
    · have := H.eq_of_reach_root hr ⟨j, by omega, rfl⟩
      rw [← hr₁] at this
      have := H.face.inj _ (by omega) _ (by omega) this; omega
    · have := H.eq_of_reach_root hr ⟨j, by omega, rfl⟩
      rw [← hr₂] at this
      have := H.face.inj _ (by omega) _ (by omega) this; omega
  have hj_side : ∀ d, M.tail d = M.tail (g j) → φ (M.face d) = w := by
    refine hside _ _ hj_off ⟨g j, rfl, ?_⟩
    rw [H.face.face j (by omega), ← H.face.face j₂ hk, ← hcts, face_cycle hC hφ H.rot hts, hw]
  -- the vertices hanging from `x` are off the cycle, on the other side
  have hx₁ : Reach G r₁ x := hh.dst₁ ▸ hh.tight₁.1.arc
  have hx₂ : Reach G r₂ x := hh.dst₂ ▸ hh.tight₂.1.arc
  have hoff : ∀ y, ¬ IsRoot M k g y → dist G r₁ x < dist G r₁ y → dist G r₂ x < dist G r₂ y →
      ¬ M.OnCyc n c y := by
    intro y hy d1 d2 hon'
    rcases hon y hon' with ⟨q, hq, hqe, -⟩ | ⟨-, -, hlt⟩ | ⟨-, -, hle, -⟩
    · exact hy ⟨q, hq, hqe⟩
    · omega
    · omega
  have he1 : dist G r₁ x < dist G r₁ (M.head e.1) := by
    have h3 := hh.e₁.2; have := H.pos' e
    change dist G r₁ (M.tail e.1) + (G).len e = dist G r₁ (M.head e.1) at h3
    rw [hh.src_e] at h3; omega
  have he2 : dist G r₂ x < dist G r₂ (M.head e.1) := by
    have h3 := hh.e₂.2; have := H.pos' e
    change dist G r₂ (M.tail e.1) + (G).len e = dist G r₂ (M.head e.1) at h3
    rw [hh.src_e] at h3; omega
  have hct : φ (M.face (c t₀)) = w := by rw [face_cycle hC hφ H.rot ht₀, hw]
  have he_side : φ (M.face e.1) = w + 1 := by
    rw [← hct]
    refine rotBetween_side hC hφ H.rot ht₀ ?_
    rw [hc₀, hc₀']; exact hrb
  have hcyc_e : M.cyc n c e.1 = 0 := by
    have hpe : ∀ (r : V) (p : {d // d ∈ S}), Tight G r p → Tight G r e → M.head p.1 = x →
        e.1 ≠ M.rev p.1 := by
      intro r p hp hep hpx hep'
      have a1 := hp.2; have a2 := hep.2; have := H.pos' p; have := H.pos' e
      change dist G r (M.tail p.1) + _ = dist G r (M.head p.1) at a1
      change dist G r (M.tail e.1) + _ = dist G r (M.head e.1) at a2
      rw [hep', CombMap.tail_rev, CombMap.head_rev] at a2
      omega
    refine hC.cyc_at ht₀ ?_ ?_ ?_
    · rw [hc₀, CombMap.tail_rev, hh.dst₂, hh.src_e]
    · rw [hc₀]; exact hpe r₂ p₂ hh.tight₂ hh.e₂ hh.dst₂
    · rw [hc₀']; exact hpe r₁ p₁ hh.tight₁ hh.e₁ hh.dst₁
  have hchain : ∀ y, TReach2 (M := M) (S := S) (ℓ := ℓ) r₁ r₂ (M.head e.1) y →
      ¬ M.OnCyc n c y ∧ (∃ d, M.tail d = y) ∧ ∀ d, M.tail d = y → φ (M.face d) = w + 1 := by
    intro y hy
    induction hy with
    | refl =>
      have h0 := hoff _ (H.not_root_dst e) he1 he2
      refine ⟨h0, ⟨M.rev e.1, by simp⟩, hside _ _ h0 ⟨M.rev e.1, by simp, ?_⟩⟩
      rw [hφ, hcyc_e, add_zero, he_side]
    | @tail a hy' ha1 ha2 ih =>
      obtain ⟨i1, -, i3⟩ := ih
      have hy'' := hy'.tail ha1 ha2
      have h0 := hoff _ (H.not_root_dst a) (lt_of_lt_of_le he1 (hy''.left.dist_le H.pos'))
        (lt_of_lt_of_le he2 (hy''.right.dist_le H.pos'))
      refine ⟨h0, ⟨M.rev a.1, by simp; rfl⟩, hside _ _ h0 ⟨M.rev a.1, by simp; rfl, ?_⟩⟩
      rw [side_arc hC hφ i1]
      exact i3 _ rfl
  -- a walk staying off the cycle stays on one side
  have cross : ∀ s y u' (L' : List {d // d ∈ S}), LWalk G y u' L' → ¬ M.OnCyc n c y →
      (∀ d, M.tail d = y → φ (M.face d) = s) →
      (∃ L₁ a L₂, L' = L₁ ++ a :: L₂ ∧ M.OnCyc n c (M.head a.1)) ∨
        ∀ d, M.tail d = u' → φ (M.face d) = s := by
    intro s y u' L' hL'
    induction hL' with
    | nil => intro _ h; exact Or.inr h
    | @cons a y l hl ih =>
      intro hy hs
      by_cases ha : M.OnCyc n c (M.head a.1)
      · exact Or.inl ⟨[], a, l, rfl, ha⟩
      · have : ∀ d, M.tail d = M.head a.1 → φ (M.face d) = s :=
          hside _ _ ha ⟨M.rev a.1, by simp, by rw [side_arc hC hφ hy]; exact hs _ rfl⟩
        rcases ih ha this with ⟨L₁, b, L₂, rfl, hb⟩ | h
        · exact Or.inl ⟨a :: L₁, b, L₂, rfl, hb⟩
        · exact Or.inr h
  obtain ⟨-, ⟨du, hdu⟩, hu_side⟩ := hchain u hh.chain
  rcases cross w _ _ L hL hj_off hj_side with ⟨L₁, a, L₂, rfl, ha⟩ | h
  · obtain ⟨z, hz1, hz2⟩ := hL.split
    obtain ⟨hza, hz2'⟩ := LWalk.cons_iff.1 hz2
    subst hza
    refine ⟨(G).dst a, L₁ ++ [a], L₂, by simp, hz1.concat rfl, hz2', ?_⟩
    rcases hon _ ha with ⟨q, hq, hqe, -⟩ | ⟨b1, b2, -⟩ | ⟨b1, b2, -, -⟩
    · exact absurd ⟨q, hq, hqe⟩ (H.not_root_dst a)
    · exact Or.inl ⟨b1, b2⟩
    · exact Or.inr ⟨b1, b2⟩
  · have := h du hdu
    rw [hu_side du hdu] at this
    omega

/-- **Non-crossing shortest paths** (the article's Lemma 5.4, distance form): for every root
`r j` between `r j₁` and `r j₂`, the shortest paths from `r j` to a vertex `u` hanging from `x`
(on the side given by the rotation at `x`) pass through `x`. -/
theorem dist_hangs {j₁ j j₂ : ℕ} (h1 : j₁ ≤ j) (h2 : j ≤ j₂) (h12 : j₁ < j₂) (hk : j₂ < k)
    {x u : V} {p₁ p₂ e : {d // d ∈ S}}
    (hh : Hangs M S ℓ (M.tail (g j₁)) (M.tail (g j₂)) x u p₁ p₂ e)
    (hrb : M.RotBetween (M.rev p₂.1) (M.rev p₁.1) e.1) :
    (Reach G (M.tail (g j)) u ↔ Reach G (M.tail (g j)) x) ∧
      (Reach G (M.tail (g j)) x →
        dist G (M.tail (g j)) u = dist G (M.tail (g j)) x + dist G x u) := by
  generalize hr₁ : M.tail (g j₁) = r₁ at hh
  generalize hr₂ : M.tail (g j₂) = r₂ at hh
  have hx₁ : Reach G r₁ x := hh.dst₁ ▸ hh.tight₁.1.arc
  have hx₂ : Reach G r₂ x := hh.dst₂ ▸ hh.tight₂.1.arc
  have hxe : (G).src e = x := hh.src_e
  have t₁ : TReach G r₁ x u := by
    have := TReach.tail ((TReach.refl _ : TReach G r₁ ((G).src e) ((G).src e))) hh.e₁
    rw [hxe] at this; exact this.trans hh.chain.left
  have t₂ : TReach G r₂ x u := by
    have := TReach.tail ((TReach.refl _ : TReach G r₂ ((G).src e) ((G).src e))) hh.e₂
    rw [hxe] at this; exact this.trans hh.chain.right
  obtain ⟨hxu, dxu⟩ := t₁.dist_eq H.nn hx₁
  have hreach : Reach G (M.tail (g j)) x → Reach G (M.tail (g j)) u := fun h => h.trans hxu
  rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
  · rw [hr₁]
    obtain ⟨-, d1⟩ := t₁.dist_eq H.nn hx₁
    exact ⟨⟨fun _ => hx₁, fun h => h.trans hxu⟩, fun _ => by omega⟩
  rcases Nat.eq_or_lt_of_le h2 with rfl | h2'
  · rw [hr₂]
    obtain ⟨-, d2⟩ := t₂.dist_eq H.nn hx₂
    exact ⟨⟨fun _ => hx₂, fun h => h.trans hxu⟩, fun _ => by omega⟩
  -- an inner root
  have key : Reach G (M.tail (g j)) u → Reach G (M.tail (g j)) x ∧
      dist G (M.tail (g j)) x + dist G x u ≤ dist G (M.tail (g j)) u := by
    intro hu
    obtain ⟨L, hL⟩ := exists_isSP H.nn hu
    obtain ⟨z, L₁, L₂, rfl, hL₁, hL₂, hz⟩ := hit H h1' h2' hk (hr₁ ▸ hr₂ ▸ hh) hrb hL.1
    have hlen := hL.2
    rw [wlen_append] at hlen
    have e1 := dist_le H.nn hL₁
    have e2 := dist_le H.nn hL₂
    -- `z` lies on a shortest path to `x`, which continues to `u`
    have hzx : Reach G z x ∧ dist G z u = dist G z x + dist G x u := by
      rcases hz with ⟨hz1, hz2⟩ | ⟨hz1, hz2⟩
      · rw [hr₁] at hz1 hz2
        obtain ⟨a1, a2⟩ := hz2.dist_eq H.nn hz1
        obtain ⟨-, a3⟩ := (hz2.trans t₁).dist_eq H.nn hz1
        obtain ⟨-, a4⟩ := t₁.dist_eq H.nn hx₁
        exact ⟨a1, by omega⟩
      · rw [hr₂] at hz1 hz2
        obtain ⟨a1, a2⟩ := hz2.dist_eq H.nn hz1
        obtain ⟨-, a3⟩ := (hz2.trans t₂).dist_eq H.nn hz1
        obtain ⟨-, a4⟩ := t₂.dist_eq H.nn hx₂
        exact ⟨a1, by omega⟩
    have e3 := dist_triangle H.nn ⟨_, hL₁⟩ hzx.1
    exact ⟨Reach.trans ⟨_, hL₁⟩ hzx.1, by omega⟩
  refine ⟨⟨fun h => (key h).1, hreach⟩, fun h => ?_⟩
  have := (key (hreach h)).2
  have := dist_triangle H.nn h hxu
  omega

/-- **The arcs from `x` to `u` are tight for every root between `r j₁` and `r j₂`**: the tree
hanging from `x` is part of the shortest path tree of each of these roots (the article's Lemma 5.4,
tree form). -/
theorem tight_hangs {j₁ j j₂ : ℕ} (h1 : j₁ ≤ j) (h2 : j ≤ j₂) (h12 : j₁ < j₂) (hk : j₂ < k)
    {x u : V} {p₁ p₂ e : {d // d ∈ S}}
    (hh : Hangs M S ℓ (M.tail (g j₁)) (M.tail (g j₂)) x u p₁ p₂ e)
    (hrb : M.RotBetween (M.rev p₂.1) (M.rev p₁.1) e.1) (hrx : Reach G (M.tail (g j)) x) :
    TReach G (M.tail (g j)) x u := by
  generalize hr₁ : M.tail (g j₁) = r₁ at hh
  generalize hr₂ : M.tail (g j₂) = r₂ at hh
  have hx₁ : Reach G r₁ x := hh.dst₁ ▸ hh.tight₁.1.arc
  have hxe : (G).src e = x := hh.src_e
  -- every vertex `y` of the hanging tree satisfies the distance identity
  have hd : ∀ y, TReach2 (M := M) (S := S) (ℓ := ℓ) r₁ r₂ (M.head e.1) y →
      Reach G (M.tail (g j)) y ∧ TReach G r₁ x y ∧
        dist G (M.tail (g j)) y = dist G (M.tail (g j)) x + dist G x y := by
    intro y hy
    have hh' : Hangs M S ℓ r₁ r₂ x y p₁ p₂ e := { hh with chain := hy }
    have t : TReach G r₁ x y := by
      have := TReach.tail ((TReach.refl _ : TReach G r₁ ((G).src e) ((G).src e))) hh.e₁
      rw [hxe] at this; exact this.trans hy.left
    obtain ⟨d1, d2⟩ := dist_hangs H h1 h2 h12 hk (hr₁ ▸ hr₂ ▸ hh') hrb
    exact ⟨d1.2 hrx, t, d2 hrx⟩
  have he : Tight G (M.tail (g j)) e := by
    obtain ⟨-, t, dd⟩ := hd _ (.refl _)
    obtain ⟨-, d1⟩ := t.dist_eq H.nn hx₁
    have h3 := hh.e₁.2
    refine ⟨hxe ▸ hrx, ?_⟩
    change dist G r₁ (M.tail e.1) + (G).len e = dist G r₁ (M.head e.1) at h3
    change dist G _ (M.tail e.1) + (G).len e = dist G _ (M.head e.1)
    rw [hh.src_e] at h3 ⊢
    omega
  have key : ∀ y, TReach2 (M := M) (S := S) (ℓ := ℓ) r₁ r₂ (M.head e.1) y →
      TReach G (M.tail (g j)) x y := by
    intro y hy
    induction hy with
    | refl =>
      have := TReach.tail ((TReach.refl _ : TReach G (M.tail (g j)) ((G).src e) ((G).src e))) he
      rw [hxe] at this; exact this
    | @tail a hy' ha1 ha2 ih =>
      refine .tail ih ⟨(hd _ hy').1, ?_⟩
      obtain ⟨-, t, dd⟩ := hd _ hy'
      obtain ⟨-, t', dd'⟩ := hd _ (hy'.tail ha1 ha2)
      obtain ⟨-, d1⟩ := t.dist_eq H.nn hx₁
      obtain ⟨-, d2⟩ := t'.dist_eq H.nn hx₁
      have := ha1.2
      omega
  exact key u hh.chain

end Lemma

end MSSP

end PlanarFlow
