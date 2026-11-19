module

public import PlanarSeparator.Stellar
public import PlanarSeparator.Cochain
public import PlanarFlow.Monge.Crossing
public import PlanarFlow.ShortestPath.BellmanFord

/-!
# Interleaved paths on a face meet: the crossing inequality of a face

Let `u₁, u₂, v₁, v₂` be corners of one face of a plane map, in this cyclic order along its
boundary walk. Then **every walk from `u₁` to `v₁` meets every walk from `u₂` to `v₂`**
(`PlanarFlow.Monge.meet_on_face`). This is a discrete form of the Jordan curve theorem, and it
is what makes the distances between the vertices of a face satisfy the crossing inequality, so
that the dense distance graph of a face is covered by Monge blocks
(`PlanarFlow.Monge.crossing_face`).

## The proof

The statement is first proved at a vertex (`PlanarFlow.Monge.meet_at_vertex`): let `e₁, e₂, e₃,
e₄` be darts leaving a vertex `x`, in this order in the rotation at `x`, a walk `P` from the head
of `e₁` to the head of `e₃` and a walk `Q` from the head of `e₄` to the head of `e₂`, both
avoiding `x`. The edges used an odd number of times by `P`, together with the edges of `e₁` and
`e₃`, form a closed cochain modulo `2` (`wc`, `sum_wc`): every vertex has even degree in it. On a
plane map it is a coboundary (`PlanarSeparator.Map.IsPlane.exists_face_cochain`): there is a
`2`-colouring `h` of the faces such that the edges of the cochain are exactly the edges between
faces of different colours. Turning around `x`, the colour changes exactly when crossing `e₁` and
`e₃`, so the faces after `e₂` and after `e₄` have different colours. If `P` and `Q` were disjoint,
no edge at a vertex of `Q` would be in the cochain, so all the faces at the vertices of `Q`, and
along its edges, would have one colour: a contradiction.

For a face `f`, apply this to the stellar subdivision (`PlanarSeparator.Map.stellar`), whose
centre of `f` is joined to every corner of `f` in the order of the boundary walk.

## Main results

* `IsMWalk`, `OnMWalk`: walks of darts of a map and their vertices.
* `meet_at_vertex`, `meet_on_face`: the meeting property.
* `GWalk`, `GDist`: walks of a digraph and the distances from a vertex (a walk of `m` arcs is a
  function `ℕ → A` read below `m`; `GDist G r δ`: `δ y = some ℓ` is the least length of a walk from
  `r` to `y`, `none` when there is none).
* `crossing_face`: for a digraph whose arcs are darts of a plane map (with any lengths, given its
  distances from the corners in the form `GDist`), the distances between the corners
  `t 0 < t 1 < ⋯ < t (b - 1)` of one face satisfy `Crossing`; hence (`isMonge_blk`) the blocks
  of its dense distance graph are Monge.

## References

* J. Fakcharoenphol, S. Rao, *Planar graphs, negative weight edges, shortest paths, and near
  linear time*, J. Comput. Syst. Sci. 72 (2006), 868–889, §3.
* B. Mohar, C. Thomassen, *Graphs on Surfaces*, Johns Hopkins University Press (2001), §4.1.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

open Finset PlanarSeparator

/-! ### Walks and distances in a digraph -/

section GraphWalks

variable {X A : Type*}

/-- A walk of `m` arcs `c 0, …, c (m - 1)` from `x` to `y` (for `m = 0`, the empty walk at
`x = y`). -/
def GWalk (G : Digraph X A) (x y : X) (m : ℕ) (c : ℕ → A) : Prop :=
  (m = 0 ∧ x = y) ∨ (0 < m ∧ G.src (c 0) = x ∧ G.dst (c (m - 1)) = y ∧
    ∀ t, t + 1 < m → G.dst (c t) = G.src (c (t + 1)))

/-- **Distances** from `r`: `δ y = some ℓ` when `ℓ` is the least length of a walk from `r` to
`y`, `δ y = none` when there is no walk from `r` to `y`. -/
structure GDist (G : Digraph X A) (r : X) (δ : X → Option ℤ) : Prop where
  some_walk : ∀ y ℓ, δ y = some ℓ → ∃ m c, GWalk G r y m c ∧ G.walkLen m c = ℓ
  some_le : ∀ y ℓ, δ y = some ℓ → ∀ m c, GWalk G r y m c → ℓ ≤ G.walkLen m c
  none : ∀ y, δ y = none → ∀ m c, ¬ GWalk G r y m c

end GraphWalks

/-! ### Walks of darts -/

section Walks

variable {D P : Type*} (M : PlanarSeparator.Map D P)

/-- A walk of `m` darts `c 0, …, c (m - 1)` of the map from `y` to `z`. -/
def IsMWalk (y z : P) (m : ℕ) (c : ℕ → D) : Prop :=
  (m = 0 ∧ y = z) ∨ (0 < m ∧ M.vert (c 0) = y ∧ M.vert (M.α (c (m - 1))) = z ∧
    ∀ t, t + 1 < m → M.vert (M.α (c t)) = M.vert (c (t + 1)))

/-- `v` is a vertex of the walk starting at `y`: the start, or the end of one of its darts. -/
def OnMWalk (y : P) (m : ℕ) (c : ℕ → D) (v : P) : Prop :=
  v = y ∨ ∃ t < m, M.vert (M.α (c t)) = v

variable {M}

lemma IsMWalk.onStart {y : P} {m : ℕ} {c : ℕ → D} : OnMWalk M y m c y := Or.inl rfl

lemma IsMWalk.onEnd {y z : P} {m : ℕ} {c : ℕ → D} (h : IsMWalk M y z m c) : OnMWalk M y m c z := by
  rcases h with ⟨-, rfl⟩ | ⟨hm, -, hz, -⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨m - 1, by omega, hz⟩

lemma IsMWalk.onTail {y z : P} {m : ℕ} {c : ℕ → D} (h : IsMWalk M y z m c) {t : ℕ} (ht : t < m) :
    OnMWalk M y m c (M.vert (c t)) := by
  rcases h with ⟨rfl, -⟩ | ⟨hm, h0, -, hs⟩
  · omega
  · rcases t with _ | s
    · exact Or.inl h0
    · exact Or.inr ⟨s, by omega, hs s ht⟩

lemma IsMWalk.snoc {y z : P} {m : ℕ} {c : ℕ → D} (h : IsMWalk M y z (m + 1) c) :
    IsMWalk M y (M.vert (c m)) m c ∧ M.vert (M.α (c m)) = z := by
  rcases h with ⟨h, -⟩ | ⟨-, h0, hz, hs⟩
  · omega
  · refine ⟨?_, by simpa using hz⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact Or.inl ⟨rfl, h0.symm⟩
    · exact Or.inr ⟨hm, h0, by rw [hs (m - 1) (by omega)]; congr 2; omega,
        fun t ht => hs t (by omega)⟩

lemma OnMWalk.mono {y : P} {m m' : ℕ} {c : ℕ → D} {v : P} (h : OnMWalk M y m c v) (hm : m ≤ m') :
    OnMWalk M y m' c v := by
  rcases h with h | ⟨t, ht, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨t, by omega, h⟩

end Walks

/-! ### The parity cochain of a walk -/

section Cochain

variable {D P : Type*} (M : PlanarSeparator.Map D P) [Fintype D] [DecidableEq D] [DecidableEq P]

/-- The indicator of a dart. -/
def ind (e : D) (d : D) : ZMod 2 := if d = e then 1 else 0

/-- The indicator of a vertex. -/
def ivx (v w : P) : ZMod 2 := if w = v then 1 else 0

/-- The parity cochain of a walk: on each dart, the parity of the number of times the walk uses
its edge. -/
def wc (m : ℕ) (c : ℕ → D) (d : D) : ZMod 2 := ∑ t ∈ range m, (ind (c t) d + ind (M.α (c t)) d)

lemma ind_α (e d : D) : ind (M.α e) (M.α d) = ind e d := by
  unfold ind
  by_cases h : d = e
  · simp [h]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (M.α_injective h'))]

lemma ind_α' (e d : D) : ind e (M.α d) = ind (M.α e) d := by
  rw [← ind_α M (M.α e) d, M.α_α]

lemma wc_α (m : ℕ) (c : ℕ → D) (d : D) : wc M m c (M.α d) = wc M m c d := by
  unfold wc
  refine sum_congr rfl fun t _ => ?_
  rw [ind_α' M, ind_α M, add_comm]

/-- The fibre sum of the indicator of a dart. -/
lemma sum_ind (v : P) (e : D) : ∑ d with M.vert d = v, ind e d = ivx v (M.vert e) := by
  unfold ind ivx
  rw [sum_ite_eq']
  simp

lemma zmod2_aux (a b c : ZMod 2) : a + b + (b + c) = a + c := by revert a b c; decide

/-- The telescoping of the ends of the darts of a walk. -/
lemma sum_ends {y z : P} (v : P) : ∀ {m : ℕ} {c : ℕ → D}, IsMWalk M y z m c →
    ∑ t ∈ range m, (ivx v (M.vert (c t)) + ivx v (M.vert (M.α (c t)))) = ivx v y + ivx v z := by
  intro m
  induction m generalizing z with
  | zero =>
    intro c h
    rcases h with ⟨-, rfl⟩ | ⟨h, -⟩
    · rw [sum_range_zero]; unfold ivx; split_ifs <;> decide
    · omega
  | succ m ih =>
    intro c h
    obtain ⟨h1, h2⟩ := h.snoc
    rw [sum_range_succ, ih h1, h2, zmod2_aux]

/-- **The parity cochain of a walk is closed except at its ends.** -/
lemma sum_wc {y z : P} {m : ℕ} {c : ℕ → D} (h : IsMWalk M y z m c) (v : P) :
    ∑ d with M.vert d = v, wc M m c d = ivx v y + ivx v z := by
  unfold wc
  rw [sum_comm]
  simp only [sum_add_distrib, sum_ind]
  rw [← sum_add_distrib]
  exact sum_ends M v h

omit [DecidableEq P] in
/-- The parity cochain vanishes away from the edges of the walk. -/
lemma wc_ne_zero {m : ℕ} {c : ℕ → D} {d : D} (h : wc M m c d ≠ 0) :
    ∃ t < m, c t = d ∨ M.α (c t) = d := by
  by_contra hcon
  push Not at hcon
  apply h
  refine sum_eq_zero fun t ht => ?_
  obtain ⟨h1, h2⟩ := hcon t (mem_range.1 ht)
  unfold ind
  rw [ite_eq_right (Ne.symm h1), ite_eq_right (Ne.symm h2), add_zero]

/-- A dart where the parity cochain of a walk is nonzero starts at a vertex of the walk. -/
lemma onMWalk_of_wc {y z : P} {m : ℕ} {c : ℕ → D} (hw : IsMWalk M y z m c) {d : D}
    (h : wc M m c d ≠ 0) : OnMWalk M y m c (M.vert d) := by
  obtain ⟨t, ht, rfl | rfl⟩ := wc_ne_zero M h
  · exact hw.onTail ht
  · exact Or.inr ⟨t, ht, rfl⟩

end Cochain

/-! ### Meeting at a vertex -/

section Vertex

variable {D P : Type*} {M : PlanarSeparator.Map D P} [Fintype D] [DecidableEq D] [Fintype P]
  [DecidableEq P]

lemma zmod2_eq_of_add (a b : ZMod 2) (h : a + b = 0) : b = a :=
  (Kasteleyn.ZMod.two_eq_of_add_eq_zero h).symm

/-- In a face colouring of a cochain vanishing at every dart of a vertex, the faces around the
vertex have one colour. -/
lemma face_const_vert {h : M.Face → ZMod 2} {C : D → ZMod 2}
    (hh : ∀ d, h (M.face d) + h (M.face (M.α d)) = C d) {v : P}
    (hv : ∀ d, M.vert d = v → C d = 0) {d d' : D} (hd : M.vert d = v) (hd' : M.vert d' = v) :
    h (M.face d) = h (M.face d') := by
  obtain ⟨n, rfl⟩ := M.exists_σ_pow_eq (hd.trans hd'.symm)
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, M.face_σ, ih (by rw [M.vert_σ_pow]; exact hd)]
    have := hh ((M.σ ^ n) d)
    rw [hv _ (by rw [M.vert_σ_pow]; exact hd)] at this
    exact (zmod2_eq_of_add _ _ this).symm

/-- In a face colouring of a cochain vanishing at every vertex of a walk, the faces at the two
ends of the walk have the same colour. -/
lemma face_const_walk {h : M.Face → ZMod 2} {C : D → ZMod 2}
    (hh : ∀ d, h (M.face d) + h (M.face (M.α d)) = C d) {y : P} :
    ∀ {z : P} {m : ℕ} {c : ℕ → D}, IsMWalk M y z m c →
      (∀ v, OnMWalk M y m c v → ∀ d, M.vert d = v → C d = 0) →
      ∀ {d d' : D}, M.vert d = y → M.vert d' = z → h (M.face d) = h (M.face d') := by
  intro z m
  induction m generalizing z with
  | zero =>
    intro c hw hon d d' hd hd'
    rcases hw with ⟨-, rfl⟩ | ⟨h, -⟩
    · exact face_const_vert hh (hon _ IsMWalk.onStart) hd hd'
    · omega
  | succ m ih =>
    intro c hw hon d d' hd hd'
    obtain ⟨h1, h2⟩ := hw.snoc
    have hon' : ∀ v, OnMWalk M y m c v → ∀ d, M.vert d = v → C d = 0 :=
      fun v hv => hon v (hv.mono (by omega))
    rw [ih h1 hon' hd rfl]
    have hz : OnMWalk M y (m + 1) c z := Or.inr ⟨m, by omega, h2⟩
    have hcm : OnMWalk M y (m + 1) c (M.vert (c m)) := (h1.onEnd).mono (by omega)
    have := hh (c m)
    rw [hon _ hcm (c m) rfl] at this
    rw [← zmod2_eq_of_add _ _ this]
    exact face_const_vert hh (hon _ hz) h2 hd'

/-- Distinct powers of the rotation, before the first return. -/
lemma pow_inj_of_wrap {e : D} {c' : ℕ} (hwrap : ∀ k, 0 < k → k ≤ c' → (M.σ ^ k) e ≠ e) {k k' : ℕ}
    (hk : k ≤ c') (hk' : k' ≤ c') (h : (M.σ ^ k) e = (M.σ ^ k') e) : k = k' := by
  by_contra hne
  have key : ∀ k k', k < k' → k' ≤ c' → (M.σ ^ k) e = (M.σ ^ k') e → False := by
    intro k k' hlt hk' h
    apply hwrap (k' - k) (by omega) (by omega)
    apply (M.σ ^ k).injective
    rw [← Equiv.Perm.mul_apply, ← pow_add, show k + (k' - k) = k' by omega, h]
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact key k k' hlt hk' h
  · exact key k' k hlt hk h.symm

lemma zmod2_add_one_ne (a : ZMod 2) : a + 1 ≠ a := by revert a; decide

/-- **Interleaved walks around a vertex meet.** Let `e₁ = σ⁰ e`, `e₂ = σᵃ e`, `e₃ = σᵇ e`,
`e₄ = σᶜ e` be darts leaving the vertex `x = vert e`, with `0 < a < b < c` and no return of the
rotation to `e` before `c`. A walk from the head of `e₁` to the head of `e₃` and a walk from the
head of `e₄` to the head of `e₂`, both avoiding `x`, have a common vertex. -/
theorem meet_at_vertex (hM : M.IsPlane) {e : D} {a b c' : ℕ} (ha : 0 < a) (hab : a < b)
    (hbc : b < c') (hwrap : ∀ k, 0 < k → k ≤ c' → (M.σ ^ k) e ≠ e) {m n : ℕ} {p q : ℕ → D}
    (hP : IsMWalk M (M.vert (M.α e)) (M.vert (M.α ((M.σ ^ b) e))) m p)
    (hQ : IsMWalk M (M.vert (M.α ((M.σ ^ c') e))) (M.vert (M.α ((M.σ ^ a) e))) n q)
    (hPx : ¬ OnMWalk M (M.vert (M.α e)) m p (M.vert e))
    (hQx : ¬ OnMWalk M (M.vert (M.α ((M.σ ^ c') e))) n q (M.vert e)) :
    ∃ v, OnMWalk M (M.vert (M.α e)) m p v ∧ OnMWalk M (M.vert (M.α ((M.σ ^ c') e))) n q v := by
  by_contra hdisj
  push Not at hdisj
  generalize hx : M.vert e = x at hPx hQx
  generalize hy : M.vert (M.α e) = y at hP hPx hdisj
  generalize he3 : (M.σ ^ b) e = e3 at hP
  generalize hz : M.vert (M.α e3) = z at hP
  generalize hy2 : M.vert (M.α ((M.σ ^ c') e)) = y2 at hQ hQx hdisj
  have hx3 : M.vert e3 = x := by rw [← he3, M.vert_σ_pow, hx]
  -- the cochain
  let C : D → ZMod 2 := fun d => wc M m p d + ind e d + ind (M.α e) d + ind e3 d + ind (M.α e3) d
  have hCα : ∀ d, C (M.α d) = C d := by
    intro d
    simp only [C, wc_α, ind_α']
    rw [M.α_α, M.α_α]
    ring
  have hCv : ∀ v, ∑ d with M.vert d = v, C d = 0 := by
    intro v
    simp only [C, sum_add_distrib, sum_ind, sum_wc M hP]
    rw [hx, hy, hx3, hz]
    generalize ivx v y = A
    generalize ivx v z = B
    generalize ivx v x = X
    revert A B X; decide
  obtain ⟨h, hh⟩ := hM.exists_face_cochain C hCα hCv
  -- the cochain at the darts of `x`
  have hCx : ∀ d, M.vert d = x → C d = ind e d + ind e3 d := by
    intro d hd
    have h1 : wc M m p d = 0 := by
      by_contra h1
      exact hPx (hd ▸ onMWalk_of_wc M hP h1)
    have h2 : ind (M.α e) d = 0 := by
      unfold ind; rw [ite_eq_right]; rintro rfl; exact hPx (by rw [← hd, hy]; exact IsMWalk.onStart)
    have h3 : ind (M.α e3) d = 0 := by
      unfold ind; rw [ite_eq_right]; rintro rfl; exact hPx (by rw [← hd, hz]; exact hP.onEnd)
    simp only [C, h1, h2, h3]
    ring
  -- the cochain at the vertices of `Q`
  have hCQ : ∀ v, OnMWalk M y2 n q v → ∀ d, M.vert d = v → C d = 0 := by
    intro v hv d hd
    have hvP : ¬ OnMWalk M y m p v := fun h' => hdisj v h' hv
    have h1 : wc M m p d = 0 := by
      by_contra h1
      exact hvP (hd ▸ onMWalk_of_wc M hP h1)
    have h2 : ∀ e', M.vert e' = x → ind e' d = 0 := by
      intro e' he'
      unfold ind; rw [ite_eq_right]; rintro rfl; exact hQx (by rw [← he', hd]; exact hv)
    have h3 : ind (M.α e) d = 0 := by
      unfold ind; rw [ite_eq_right]; rintro rfl; exact hvP (by rw [← hd, hy]; exact IsMWalk.onStart)
    have h4 : ind (M.α e3) d = 0 := by
      unfold ind; rw [ite_eq_right]; rintro rfl; exact hvP (by rw [← hd, hz]; exact hP.onEnd)
    simp only [C, h1, h2 e hx, h2 e3 hx3, h3, h4]
    ring
  -- turning around `x`
  have hrot : ∀ k ≤ c', h (M.face ((M.σ ^ k) e)) =
      h (M.face e) + if 0 < k ∧ k ≤ b then 1 else 0 := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rw [pow_succ', Equiv.Perm.mul_apply, M.face_σ]
      have h1 := hh ((M.σ ^ k) e)
      rw [hCx _ (by rw [M.vert_σ_pow, hx]), ih (by omega)] at h1
      have e1 : ind e ((M.σ ^ k) e) = if k = 0 then 1 else 0 := by
        unfold ind
        by_cases hk0 : k = 0
        · simp [hk0]
        · rw [ite_eq_right hk0, ite_eq_right (hwrap k (by omega) (by omega))]
      have e2 : ind e3 ((M.σ ^ k) e) = if k = b then 1 else 0 := by
        unfold ind
        rw [← he3]
        by_cases hkb : k = b
        · simp [hkb]
        · rw [ite_eq_right hkb, ite_eq_right (fun h' => hkb (pow_inj_of_wrap hwrap (by omega) (by omega) h'))]
      rw [e1, e2] at h1
      generalize h (M.face (M.α ((M.σ ^ k) e))) = H at h1 ⊢
      generalize h (M.face e) = H0 at h1 ⊢
      split_ifs at h1 ⊢ <;> first | omega | (revert H H0; decide)
  have hfe2 := hrot a (by omega)
  have hfe4 := hrot c' le_rfl
  rw [ite_eq_left ⟨ha, hab.le⟩] at hfe2
  rw [ite_eq_right (by omega), add_zero] at hfe4
  -- along `Q`
  have hQc := face_const_walk hh hQ hCQ (d := M.α ((M.σ ^ c') e)) (d' := M.α ((M.σ ^ a) e))
    hy2 rfl
  have hne : ∀ k, 0 < k → k ≤ c' → k ≠ b → C ((M.σ ^ k) e) = 0 := by
    intro k hk hkc hkb
    rw [hCx _ (by rw [M.vert_σ_pow, hx])]
    unfold ind
    rw [ite_eq_right (hwrap k hk hkc), ← he3,
      ite_eq_right (fun h' => hkb (pow_inj_of_wrap hwrap hkc (by omega) h'))]
    ring
  have q4 := hh ((M.σ ^ c') e)
  rw [hne c' (by omega) le_rfl (by omega)] at q4
  have q2 := hh ((M.σ ^ a) e)
  rw [hne a ha (by omega) (by omega)] at q2
  rw [zmod2_eq_of_add _ _ q4, zmod2_eq_of_add _ _ q2, hfe2, hfe4] at hQc
  exact zmod2_add_one_ne _ hQc.symm

end Vertex


/-! ### Meeting on a face -/

section Face

variable {D P : Type*} {M : PlanarSeparator.Map D P} [Fintype D] [DecidableEq D] [Fintype P]
  [DecidableEq P]

open StDart

/-- A walk of the map is a walk of its stellar subdivision. -/
lemma IsMWalk.lift {y z : P} {m : ℕ} {c : ℕ → D} (h : IsMWalk M y z m c) :
    IsMWalk M.stellar (.inl y) (.inl z) m (fun t => old (c t)) := by
  rcases h with ⟨h1, rfl⟩ | ⟨h1, h2, h3, h4⟩
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr ⟨h1, by simp [h2], by simp [h3], fun t ht => by simp [h4 t ht]⟩

lemma onMWalk_lift {y : P} {m : ℕ} {c : ℕ → D} {v : P ⊕ M.Face}
    (h : OnMWalk M.stellar (.inl y) m (fun t => old (c t)) v) :
    ∃ w, v = .inl w ∧ OnMWalk M y m c w := by
  rcases h with rfl | ⟨t, ht, rfl⟩
  · exact ⟨y, rfl, Or.inl rfl⟩
  · exact ⟨M.vert (M.α (c t)), by simp, Or.inr ⟨t, ht, rfl⟩⟩

lemma φ_pow_inv_pow {y z : D} {k : ℕ} (h : (M.φ ^ k) y = z) : (M.φ⁻¹ ^ k) z = y := by
  rw [← h, ← Equiv.Perm.mul_apply, inv_pow, inv_mul_cancel, Equiv.Perm.one_apply]

/-- **Interleaved walks between the corners of a face meet.** Let `g` be a dart of a face whose
boundary walk does not return to `g` within `N` steps, and `0 < a < b < c < N`. Going backwards
along the boundary walk from `g`, the corners `φ⁻ᵃ g`, `φ⁻ᵇ g`, `φ⁻ᶜ g` come in this order. A
walk from the corner of `g` to the corner of `φ⁻ᵇ g` and a walk from the corner of `φ⁻ᶜ g` to
the corner of `φ⁻ᵃ g` have a common vertex. -/
theorem meet_on_face (hM : M.IsPlane) {g : D} {N : ℕ}
    (hN : ∀ k, 0 < k → k < N → (M.φ ^ k) g ≠ g) {a b c' : ℕ} (ha : 0 < a) (hab : a < b)
    (hbc : b < c') (hcN : c' < N) {m n : ℕ} {p q : ℕ → D}
    (hP : IsMWalk M (M.vert g) (M.vert ((M.φ⁻¹ ^ b) g)) m p)
    (hQ : IsMWalk M (M.vert ((M.φ⁻¹ ^ c') g)) (M.vert ((M.φ⁻¹ ^ a) g)) n q) :
    ∃ v, OnMWalk M (M.vert g) m p v ∧ OnMWalk M (M.vert ((M.φ⁻¹ ^ c') g)) n q v := by
  have hS := Map.isPlane_stellar hM
  have hσ : ∀ k d, (M.stellar.σ ^ k) (down d) = down ((M.φ⁻¹ ^ k) d) :=
    fun k d => M.stσ_down_pow k d
  have hv : ∀ d, M.stellar.vert (M.stellar.α (down d)) = Sum.inl (M.vert d) := fun d => rfl
  have hwrap : ∀ k, 0 < k → k ≤ c' → (M.stellar.σ ^ k) (down g) ≠ down g := by
    intro k hk hkc h
    rw [hσ] at h
    apply hN k hk (by omega)
    have h' := StDart.down.inj h
    conv_lhs => rw [← h']
    rw [← Equiv.Perm.mul_apply, inv_pow, mul_inv_cancel, Equiv.Perm.one_apply]
  have hP' : IsMWalk M.stellar (M.stellar.vert (M.stellar.α (down g)))
      (M.stellar.vert (M.stellar.α ((M.stellar.σ ^ b) (down g)))) m (fun t => old (p t)) := by
    rw [hσ, hv, hv]; exact hP.lift
  have hQ' : IsMWalk M.stellar (M.stellar.vert (M.stellar.α ((M.stellar.σ ^ c') (down g))))
      (M.stellar.vert (M.stellar.α ((M.stellar.σ ^ a) (down g)))) n (fun t => old (q t)) := by
    rw [hσ, hσ, hv, hv]; exact hQ.lift
  have hx : M.stellar.vert (down g) = Sum.inr (M.face g) := rfl
  obtain ⟨v, h1, h2⟩ := meet_at_vertex hS ha hab hbc hwrap hP' hQ' (by
      rw [hv, hx]; intro h
      obtain ⟨w, hw, -⟩ := onMWalk_lift h
      cases hw) (by
      rw [hσ, hv, hx]; intro h
      obtain ⟨w, hw, -⟩ := onMWalk_lift h
      cases hw)
  rw [hv] at h1
  rw [hσ, hv] at h2
  obtain ⟨w, rfl, hw1⟩ := onMWalk_lift h1
  obtain ⟨w', hw', hw2⟩ := onMWalk_lift h2
  cases hw'
  exact ⟨w, hw1, hw2⟩

/-- The corners of a face, numbered along its boundary walk from `d₀`, with the period `N`. -/
lemma corner_back {d₀ : D} {N : ℕ} (hN0 : (M.φ ^ N) d₀ = d₀) {s s' k : ℕ}
    (h : k + s' = s ∨ k + s' = N + s) : (M.φ⁻¹ ^ k) ((M.φ ^ s) d₀) = (M.φ ^ s') d₀ := by
  apply φ_pow_inv_pow
  rw [← Equiv.Perm.mul_apply, ← pow_add]
  rcases h with h | h
  · rw [h]
  · rw [h, add_comm, pow_add, Equiv.Perm.mul_apply, hN0]

lemma corner_wrap {d₀ : D} {N : ℕ} (hmin : ∀ k, 0 < k → k < N → (M.φ ^ k) d₀ ≠ d₀) (s : ℕ) :
    ∀ k, 0 < k → k < N → (M.φ ^ k) ((M.φ ^ s) d₀) ≠ (M.φ ^ s) d₀ := by
  intro k hk hkN h
  apply hmin k hk hkN
  apply (M.φ ^ s).injective
  rw [← Equiv.Perm.mul_apply, ← pow_add, add_comm, pow_add, Equiv.Perm.mul_apply, h]

/-- Interleaved walks between corners, in the general position used below. -/
lemma meet_corners (hM : M.IsPlane) {d₀ : D} {N : ℕ} (hN0 : (M.φ ^ N) d₀ = d₀)
    (hmin : ∀ k, 0 < k → k < N → (M.φ ^ k) d₀ ≠ d₀) {s sa sb sc a b c' : ℕ} (ha : 0 < a)
    (hab : a < b) (hbc : b < c') (hcN : c' < N) (h1 : a + sa = s ∨ a + sa = N + s)
    (h2 : b + sb = s ∨ b + sb = N + s) (h3 : c' + sc = s ∨ c' + sc = N + s) {m n : ℕ}
    {p q : ℕ → D} (hP : IsMWalk M (M.vert ((M.φ ^ s) d₀)) (M.vert ((M.φ ^ sb) d₀)) m p)
    (hQ : IsMWalk M (M.vert ((M.φ ^ sc) d₀)) (M.vert ((M.φ ^ sa) d₀)) n q) :
    ∃ v, OnMWalk M (M.vert ((M.φ ^ s) d₀)) m p v ∧ OnMWalk M (M.vert ((M.φ ^ sc) d₀)) n q v := by
  have := meet_on_face hM (corner_wrap hmin s) ha hab hbc hcN (p := p) (q := q) (m := m) (n := n)
    (by rw [corner_back hN0 h2]; exact hP) (by rw [corner_back hN0 h3, corner_back hN0 h1]; exact hQ)
  rwa [corner_back hN0 h3] at this

end Face

/-! ### The crossing inequality -/

section Dist

variable {D P A : Type*} {M : PlanarSeparator.Map D P} [Fintype D] [DecidableEq D] [Fintype P]
  [DecidableEq P] [Fintype A] {G : Digraph P A}

lemma isWalk_congr {x y : P} {m : ℕ} {c c' : ℕ → A} (h : GWalk G x y m c)
    (hc : ∀ t < m, c t = c' t) : GWalk G x y m c' := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
  · exact Or.inl ⟨h1, h2⟩
  · refine Or.inr ⟨h1, by rw [← hc 0 h1]; exact h2, by rw [← hc _ (by omega)]; exact h3,
      fun t ht => ?_⟩
    rw [← hc t (by omega), ← hc (t + 1) ht]; exact h4 t ht

/-- The concatenation of two walks. -/
lemma isWalk_append {x y z : P} {m m' : ℕ} {c c' : ℕ → A} (h1 : GWalk G x y m c)
    (h2 : GWalk G y z m' c') :
    GWalk G x z (m + m') (fun t => if t < m then c t else c' (t - m)) := by
  rcases h1 with ⟨rfl, rfl⟩ | ⟨hm, h10, h1e, h1s⟩
  · rw [Nat.zero_add]
    exact isWalk_congr h2 fun t _ => by simp
  · rcases h2 with ⟨rfl, rfl⟩ | ⟨hm', h20, h2e, h2s⟩
    · rw [Nat.add_zero]
      exact isWalk_congr (Or.inr ⟨hm, h10, h1e, h1s⟩) fun t ht => by simp [ht]
    · refine Or.inr ⟨by omega, by simp [hm, h10], ?_, fun t ht => ?_⟩
      · beta_reduce
        rw [ite_eq_right (by omega), show m + m' - 1 - m = m' - 1 by omega]; exact h2e
      · beta_reduce
        by_cases h : t + 1 < m
        · rw [ite_eq_left (by omega), ite_eq_left h]; exact h1s t h
        · by_cases h' : t + 1 = m
          · rw [ite_eq_left (by omega), ite_eq_right (by omega), show t + 1 - m = 0 by omega,
              h20, ← h1e, show m - 1 = t by omega]
          · rw [ite_eq_right (by omega), ite_eq_right (by omega),
              show t + 1 - m = t - m + 1 by omega]
            exact h2s (t - m) (by omega)

lemma walkLen_append {m m' : ℕ} {c c' : ℕ → A} :
    G.walkLen (m + m') (fun t => if t < m then c t else c' (t - m)) =
      G.walkLen m c + G.walkLen m' c' := by
  unfold Digraph.walkLen
  rw [sum_range_add]
  congr 1
  · exact sum_congr rfl fun t ht => by beta_reduce; rw [ite_eq_left (mem_range.1 ht)]
  · exact sum_congr rfl fun t _ => by
      beta_reduce; rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]

/-- A walk through `v` splits at `v`. -/
lemma isWalk_split {emb : A → D} (hd : ∀ a, G.dst a = M.vert (M.α (emb a))) {x y v : P} {m : ℕ} {c : ℕ → A}
    (h : GWalk G x y m c) (hv : OnMWalk M x m (fun t => emb (c t)) v) :
    ∃ m₁ c₁ m₂ c₂, GWalk G x v m₁ c₁ ∧ GWalk G v y m₂ c₂ ∧
      G.walkLen m₁ c₁ + G.walkLen m₂ c₂ = G.walkLen m c := by
  rcases hv with rfl | ⟨s, hs', rfl⟩
  · exact ⟨0, c, m, c, Or.inl ⟨rfl, rfl⟩, h, by simp [Digraph.walkLen]⟩
  · rcases h with ⟨rfl, -⟩ | ⟨hm, h0, he, hst⟩
    · omega
    refine ⟨s + 1, c, m - (s + 1), fun u => c (s + 1 + u),
      Or.inr ⟨by omega, h0, by rw [Nat.add_sub_cancel, hd], fun t ht => hst t (by omega)⟩, ?_, ?_⟩
    · by_cases hsm : s + 1 = m
      · exact Or.inl ⟨by omega, by rw [← hd, ← he, show m - 1 = s by omega]⟩
      · refine Or.inr ⟨by omega, by rw [Nat.add_zero, ← hd]; exact (hst s (by omega)).symm,
          by beta_reduce; rw [← he, show s + 1 + (m - (s + 1) - 1) = m - 1 by omega],
          fun u hu => ?_⟩
        beta_reduce
        rw [show s + 1 + (u + 1) = s + 1 + u + 1 by omega]
        exact hst (s + 1 + u) (by omega)
    · unfold Digraph.walkLen
      conv_rhs => rw [show m = (s + 1) + (m - (s + 1)) by omega]
      rw [sum_range_add (fun t => G.len (c t)) (s + 1) (m - (s + 1))]

lemma isMWalk_of_isWalk {emb : A → D} (hs : ∀ a, G.src a = M.vert (emb a))
    (hd : ∀ a, G.dst a = M.vert (M.α (emb a))) {x y : P} {m : ℕ} {c : ℕ → A}
    (h : GWalk G x y m c) : IsMWalk M x y m (fun t => emb (c t)) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, by rw [← hs]; exact h2, by rw [← hd]; exact h3,
      fun t ht => by rw [← hd, ← hs]; exact h4 t ht⟩

/-- **The exchange of tails.** If shortest walks from `x` to `y` and from `x'` to `y'` meet, then
`δ x y' + δ x' y ≤ δ x y + δ x' y'`. -/
lemma exchange {emb : A → D} (hd : ∀ a, G.dst a = M.vert (M.α (emb a))) {x x' y y' : P} {δ δ' : P → Option ℤ}
    (hδ : GDist G x δ) (hδ' : GDist G x' δ') {Dxy Dxy' Dx'y Dx'y' : ℤ} (h1 : δ y = some Dxy)
    (h2 : δ y' = some Dxy') (h3 : δ' y = some Dx'y) (h4 : δ' y' = some Dx'y')
    (hmeet : ∀ m p n q, GWalk G x y m p → GWalk G x' y' n q →
      ∃ v, OnMWalk M x m (fun t => emb (p t)) v ∧ OnMWalk M x' n (fun t => emb (q t)) v) :
    Dxy' + Dx'y ≤ Dxy + Dx'y' := by
  obtain ⟨m, p, hp, hpl⟩ := hδ.some_walk y _ h1
  obtain ⟨n, q, hq, hql⟩ := hδ'.some_walk y' _ h4
  obtain ⟨v, hv1, hv2⟩ := hmeet m p n q hp hq
  obtain ⟨m₁, c₁, m₂, c₂, w₁, w₂, e₁⟩ := isWalk_split hd hp hv1
  obtain ⟨n₁, d₁, n₂, d₂, w₃, w₄, e₂⟩ := isWalk_split hd hq hv2
  have k1 := hδ.some_le y' _ h2 _ _ (isWalk_append w₁ w₄)
  have k2 := hδ'.some_le y _ h3 _ _ (isWalk_append w₃ w₂)
  rw [walkLen_append] at k1 k2
  omega

/-- **The crossing inequality of a face.** Let `G` be a digraph whose arcs are darts of a plane
map (`emb`), and `d₀` a dart of a face of the map whose boundary walk has period `N`. Let
`t 0 < t 1 < ⋯ < t (b - 1) < N` be positions along the boundary walk, and suppose that for every
`i < b` the distances in `G` from the corner `v i = vert (φ ^ t i d₀)` are given (`GDist`), with
the distance from `v i` to `v j` equal to `Dm i j`. Then `Dm` satisfies the crossing inequality,
so every block of the dense distance graph is Monge (`isMonge_blk`). -/
theorem crossing_face (hM : M.IsPlane) {emb : A → D} (hs : ∀ a, G.src a = M.vert (emb a))
    (hd : ∀ a, G.dst a = M.vert (M.α (emb a))) {d₀ : D} {N : ℕ} (hN0 : (M.φ ^ N) d₀ = d₀)
    (hmin : ∀ k, 0 < k → k < N → (M.φ ^ k) d₀ ≠ d₀) {b : ℕ} {t : ℕ → ℕ}
    (ht : ∀ i j, i < j → j < b → t i < t j) (htN : ∀ i < b, t i < N) {Dm : ℕ → ℕ → ℤ}
    (hδ : ∀ i < b, ∃ δ, GDist G (M.vert ((M.φ ^ t i) d₀)) δ ∧
      ∀ j < b, δ (M.vert ((M.φ ^ t j) d₀)) = some (Dm i j)) :
    Crossing b Dm := by
  intro i i' j j' hi hj hi' hj' hsep
  obtain ⟨δ, hδ1, hδ2⟩ := hδ i (by omega)
  obtain ⟨δ', hδ1', hδ2'⟩ := hδ i' hi'
  refine exchange hd hδ1 hδ1' (hδ2 j (by omega)) (hδ2 j' hj') (hδ2' j (by omega))
    (hδ2' j' hj') fun m p n q hp hq => ?_
  have hp' := isMWalk_of_isWalk hs hd hp
  have hq' := isMWalk_of_isWalk hs hd hq
  rcases hsep with hsep | hsep
  · -- `i < i' < j < j'`
    have l1 := ht i i' hi hi'
    have l2 := ht i' j hsep (by omega)
    have l3 := ht j j' hj hj'
    have l4 := htN j' hj'
    exact meet_corners hM hN0 hmin (s := t i) (sa := t j') (sb := t j) (sc := t i')
      (a := N + t i - t j') (b := N + t i - t j) (c' := N + t i - t i') (by omega) (by omega)
      (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) hp' hq'
  · -- `j < j' < i < i'`
    have l1 := ht j j' hj (by omega)
    have l2 := ht j' i hsep (by omega)
    have l3 := ht i i' hi hi'
    have l4 := htN i' hi'
    exact meet_corners hM hN0 hmin (s := t i) (sa := t j') (sb := t j) (sc := t i')
      (a := t i - t j') (b := t i - t j) (c' := N + t i - t i') (by omega) (by omega)
      (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega)) hp' hq'

end Dist

end Monge

end PlanarFlow
