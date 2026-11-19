module

public import PlanarFlow.Klein.Run
public import PlanarFlow.STFlow.Cotree
public import PlanarFlow.MSSP.NonCrossing
public import PlanarFlow.NegSSSP.Spec

/-!
# The active arcs are the darts of a path of the dual cotree

Lemma 3.4 of Cabello, Chambers and Erickson (SIAM J. Comput. 42, 2013): for a spanning tree `T`
of a plane graph and an edge `e = uv` of `T`, the edges of the graph between the two components
of `T - e` are exactly the edges whose duals lie on the path of the dual cotree between the two
faces beside `e`. This is what makes `MINPATH` in the dual cotree find the next pivot of Klein's
algorithm.

A spanning tree of the map `M` is a spanning tree of the dual of `M.dual`
(`PlanarFlow.STFlow.DTree M.dual`: a root vertex and, for every other vertex `x`, its parent dart
`T.par x`, with head `x`); its cotree is the set of darts off the tree, a spanning tree of the dual
graph of `M`, and `T.chi f₁ f₂` is the unit flow from the face `f₁` to the face `f₂` in the cotree
(the path of the cotree, `PlanarFlow.STFlow.DTree.chi_spec`).

* `chi_par_eq_cross`: **the fundamental cut of a tree edge is the fundamental cycle of its dual**:
  for `y` other than the root, `e = T.par y` and `U` the subtree of `y`, on every dart other than
  `e` and its reverse the path of the cotree from the face of `e` to the face of its reverse is
  `1` on the darts leaving `U`, `-1` on the darts entering it, and `0` elsewhere.
* `hang_iff_anc`: if the tree extends the forest of the pivot loop (`Compat`: rooted at `u`,
  with the parent dart `e` of `v` from `u` to `v`, and the parent darts of the forest), the blue
  vertices are those of the subtree of `v`.
* `ractive_iff_chi`: **the active arcs are exactly the arcs of the piece leaving a vertex reached
  from `v` whose dart lies on the path of the cotree** from the face of `e` to the face of its
  reverse (with value `1`; the article's Lemma 3.4). With `PlanarFlow.Klein.RInv.step`, the next
  pivot is an arc of least slack on this path: the answer of `MINPATH` (whose values are the
  slacks on the arcs of the piece leaving a vertex reached from `v`, and `+∞` elsewhere).
* `exists_compat`: on a plane map, **every forest satisfying the invariant extends to such a
  spanning tree** (the other vertices hung by a breadth-first search), so the hypotheses of
  `ractive_iff_chi` can always be met.
* `klein_cotree_path`: the two in the setting `PlanarFlow.MSSP.Hyp`, for the move from the root
  `tail (g j)` to the next one, with `e = g j` (the boundary dart, outside the piece).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

/-! ### The fundamental cut and the fundamental cycle -/

section Cut

variable (T : DTree M.dual)

lemma anc_depth_le {b x : V} (h : T.Anc b x) : T.depth b ≤ T.depth x := by
  obtain ⟨n, hn⟩ := h
  induction n generalizing x with
  | zero => rw [← hn]; rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply] at hn
    have := ih hn
    by_cases hx : x = T.root
    · rw [hx, T.up_root] at this; rw [hx]; exact this
    · have := T.depth_up hx; omega

lemma tpar_head {x : V} (hx : x ≠ T.root) : M.head (T.par x) = x := T.head_par x hx

lemma tup_eq {x : V} (hx : x ≠ T.root) : T.up x = M.tail (T.par x) := T.up_of_ne hx

/-- The subtree of `y`: the vertices below `y` in the tree. -/
noncomputable def tsub (y : V) : Finset V :=
  open Classical in univ.filter fun x => T.Anc y x

lemma mem_tsub {y x : V} : x ∈ tsub T y ↔ T.Anc y x := by
  classical
  simp [tsub]

/-- **The fundamental cut of a tree edge is the fundamental cycle of its dual** (the article's
Lemma 3.4): the path of the cotree from the face of `e = T.par y` to the face of its reverse
crosses exactly the darts between the subtree of `y` and the rest, with value `1` on the darts
leaving the subtree. -/
theorem chi_par_eq_cross (hM : M.IsPlane) {y : V} (hy : y ≠ T.root) {d : D}
    (h1 : d ≠ T.par y) (h2 : d ≠ M.rev (T.par y)) :
    T.chi (M.face (T.par y)) (M.face (M.rev (T.par y))) d = cross M (tsub T y) d := by
  set e := T.par y with he
  set U := tsub T y with hU
  have hed : e ≠ M.rev e := (M.rev_ne e).symm
  -- the tail of `e` is not in the subtree of `y`, its head is `y`
  have hey : M.head e = y := tpar_head T hy
  have het : M.tail e ∉ U := by
    rw [hU, (mem_tsub T)]
    intro h
    have := anc_depth_le T h
    rw [← tup_eq T hy] at this
    have := T.depth_up hy
    omega
  have hyU : y ∈ U := (mem_tsub T).2 (T.anc_self y)
  have hcross_e : cross M U e = -1 := by
    simp only [cross, het, hey, hyU]; norm_num
  set δ : D → ℤ := Pi.single e 1 - Pi.single (M.rev e) 1 with hδ
  set κ : D → ℤ := cross M U + δ with hκ
  have hκa : M.dual.IsAntisymm κ := by
    intro x
    have h1 : cross M U (M.rev x) = -cross M U x := cross_antisymm (M := M) U x
    have h2 : δ (M.rev x) = -δ x := isAntisymm_dart (M := M) e x
    change κ (M.rev x) = -κ x
    simp only [hκ, Pi.add_apply]
    rw [h1, h2]; ring
  have hκdiv : ∀ f, M.dual.div κ f =
      (if M.face e = f then 1 else 0) - (if M.face (M.rev e) = f then 1 else 0) := by
    intro f
    rw [hκ, div_add]
    have h0 : M.dual.div (cross M U) f = 0 := sum_face_cross U f
    have h1 := div_dart (M := M.dual) e f
    rw [h0, zero_add]
    exact h1
  have hκoff : T.OffT κ := by
    intro x hx
    by_cases hxe : x = e
    · subst hxe
      simp [hκ, hδ, hcross_e, hed]
    by_cases hxr : x = M.rev e
    · subst hxr
      have := cross_antisymm (M := M) U e
      simp only [hκ, hδ, Pi.add_apply, Pi.sub_apply, Pi.single_apply, hed.symm, ite_false,
        ite_true]
      change cross M U (M.rev e) + _ = 0
      rw [this, hcross_e]; simp
    obtain ⟨z, hz, hzx⟩ := hx
    have hzy : z ≠ y := by
      rintro rfl
      rcases hzx with h | h
      · exact hxe h
      · exact hxr h
    have hzU : z ∈ U ↔ T.up z ∈ U := by
      rw [hU, (mem_tsub T), (mem_tsub T)]; exact T.anc_up_iff hzy
    have hc : cross M U (T.par z) = 0 := by
      have ht : M.tail (T.par z) = T.up z := (tup_eq T hz).symm
      have hh : M.head (T.par z) = z := tpar_head T hz
      simp only [cross, ht, hh]
      by_cases hzu : z ∈ U
      · simp [hzu, hzU.1 hzu]
      · have : T.up z ∉ U := fun h => hzu (hzU.2 h)
        simp [hzu, this]
    have hδx : δ x = 0 := by simp [hδ, hxe, hxr]
    simp only [hκ, Pi.add_apply, hδx, add_zero]
    rcases hzx with rfl | rfl
    · exact hc
    · exact (cross_antisymm (M := M) U (T.par z)).trans (by rw [hc, neg_zero])
  -- `chi - κ` is a circulation off the tree, hence zero
  obtain ⟨hχa, hχdiv, hχoff, -⟩ := T.chi_spec hM.dual (M.face e) (M.face (M.rev e))
  set χ := T.chi (M.face e) (M.face (M.rev e)) with hχ
  have hcirc : M.dual.IsCirc (χ - κ) := by
    refine ⟨fun x => ?_, fun f => ?_⟩
    · change (χ - κ) (M.rev x) = -((χ - κ) x)
      simp only [Pi.sub_apply]
      rw [show χ (M.rev x) = -χ x from hχa x, show κ (M.rev x) = -κ x from hκa x]; ring
    · rw [div_sub, hχdiv, hκdiv]
      ring
  have hoff : T.OffT (χ - κ) := fun x hx => by
    simp only [Pi.sub_apply, hχoff x hx, hκoff x hx, sub_zero]
  have hz := T.circ_eq_zero hM.dual hcirc hoff d
  simp only [Pi.sub_apply] at hz
  have hδd : δ d = 0 := by simp [hδ, h1, h2]
  rw [sub_eq_zero.1 hz]
  simp [hκ, hδd]

end Cut

/-! ### Klein's forest in a spanning tree -/

section Klein

variable {S : Finset D} {ℓ : D → ℤ} {u v : V}

local notation "𝒢" => pieceGraph M S ℓ

/-- **A spanning tree extending the forest of the pivot loop**: rooted at `u`, the parent dart
`e` of `v` (from `u` to `v`), and the parent darts of the forest `P`. -/
structure Compat (T : DTree M.dual) (u v : V) (e : D) (P : V → Option {d // d ∈ S}) :
    Prop where
  root : T.root = u
  par_v : T.par v = e
  tail : M.tail e = u
  par : ∀ x a, P x = some a → T.par x = a.1

variable {T : DTree M.dual} {e : D} {P : V → Option {d // d ∈ S}}

/-- **The blue vertices are those of the subtree of `v`.** -/
theorem hang_iff_anc (H : MoveHyp 𝒢 u v) (hI : RInv 𝒢 u v P) (hC : Compat T u v e P) {x : V}
    (hx : x = u ∨ x = v ∨ x ∈ moveSet 𝒢 u v) : Hang 𝒢 P v x ↔ T.Anc v x := by
  have hmem : ∀ x a, P x = some a → x ∈ moveSet 𝒢 u v := fun x a h => by
    by_contra hm; rw [hI.off x hm] at h; simp at h
  have hup : ∀ x a, P x = some a → T.up x = (𝒢).src a := fun x a h => by
    have hxu : x ≠ T.root := by
      rw [hC.root]; exact (H.mem_moveSet.1 (hmem x a h)).1
    rw [tup_eq T hxu, hC.par x a h]; rfl
  constructor
  · intro h
    clear hx
    induction h with
    | root => exact T.anc_self _
    | @step x a hxa _ ih => exact T.anc_of_up (hup x a hxa ▸ ih)
  · intro h
    by_contra hb
    have hu : Hang 𝒢 P u x := by
      rcases hx with rfl | rfl | hx
      · exact .root
      · exact absurd .root hb
      · exact ((hI.forest H x hx).resolve_right hb)
    clear hx
    induction hu with
    | root =>
      rw [← hC.root, T.anc_root_iff] at h
      exact H.ne (h.trans hC.root).symm
    | @step x a hxa hz ih =>
      have hxv : x ≠ v := (H.mem_moveSet.1 (hmem x a hxa)).2.1
      exact ih (hup x a hxa ▸ (T.anc_up_iff hxv).1 h) fun h' => hb (.step hxa h')

/-- **The active arcs are the arcs on the path of the dual cotree** (the article's Lemma 3.4):
an arc of the piece is active if and only if its tail is reached from `v` and its dart has value
`1` on the path of the cotree from the face of `e` to the face of its reverse. -/
theorem ractive_iff_chi (hM : M.IsPlane) (H : MoveHyp 𝒢 u v) (hI : RInv 𝒢 u v P)
    (hC : Compat T u v e P) (heS : e ∉ S) (hrS : M.rev e ∉ S) (a : {d // d ∈ S}) :
    RActive 𝒢 u v P a ↔
      Reach 𝒢 v ((𝒢).src a) ∧ T.chi (M.face e) (M.face (M.rev e)) a.1 = 1 := by
  have hvr : v ≠ T.root := by rw [hC.root]; exact H.ne.symm
  have h1 : a.1 ≠ T.par v := by rw [hC.par_v]; rintro h; exact heS (h ▸ a.2)
  have h2 : a.1 ≠ M.rev (T.par v) := by rw [hC.par_v]; rintro h; exact hrS (h ▸ a.2)
  rw [← hC.par_v, chi_par_eq_cross T hM hvr h1 h2]
  have hsrc : Reach 𝒢 v ((𝒢).src a) → (𝒢).src a = u ∨ (𝒢).src a = v ∨
      (𝒢).src a ∈ moveSet 𝒢 u v := by
    intro h
    by_cases hs : (𝒢).src a = v
    · exact Or.inr (Or.inl hs)
    obtain ⟨hu, hv⟩ := H.ne_of_reach (Or.inr rfl) h hs
    exact Or.inr (Or.inr (H.mem_moveSet.2 ⟨hu, hv, (H.reach _ hu hv).2 h⟩))
  have hdst : Reach 𝒢 v ((𝒢).src a) → (𝒢).dst a ∈ moveSet 𝒢 u v := fun h =>
    H.mem_moveSet.2 ⟨H.noU a, H.noV a, (H.reach _ (H.noU a) (H.noV a)).2 h.arc⟩
  have ht : M.tail a.1 = (𝒢).src a := rfl
  have hh : M.head a.1 = (𝒢).dst a := rfl
  constructor
  · rintro ⟨hs, hd, hdr⟩
    have hr := hI.reach_v H hs
    refine ⟨hr, ?_⟩
    have hsU : (𝒢).src a ∈ tsub T v :=
      (mem_tsub T).2 ((hang_iff_anc H hI hC (hsrc hr)).1 hs)
    have hdU : (𝒢).dst a ∉ tsub T v := fun h =>
      hdr ((hang_iff_anc H hI hC (Or.inr (Or.inr hd))).2 ((mem_tsub T).1 h))
    simp [cross, ht, hh, hsU, hdU]
  · rintro ⟨hr, hc⟩
    have hsU : (𝒢).src a ∈ tsub T v ∧ (𝒢).dst a ∉ tsub T v := by
      simp only [cross, ht, hh] at hc
      split_ifs at hc with p q <;> first | exact ⟨p, q⟩ | omega
    exact ⟨(hang_iff_anc H hI hC (hsrc hr)).2 ((mem_tsub T).1 hsU.1), hdst hr,
      fun h => hsU.2 ((mem_tsub T).2 ((hang_iff_anc H hI hC (Or.inr (Or.inr (hdst hr)))).1 h))⟩

/-! ### A spanning tree extending the forest -/

variable (M) in
/-- `Near M C n x`: a vertex of `C` reaches `x` by at most `n` darts. -/
inductive Near (C : Finset V) : ℕ → V → Prop
  | base {x : V} : x ∈ C → Near C 0 x
  | mono {n : ℕ} {x : V} : Near C n x → Near C (n + 1) x
  | step {n : ℕ} {d : D} : Near C n (M.tail d) → Near C (n + 1) (M.head d)

lemma near_exists (hM : M.IsPlane) {C : Finset V} {c : V} (hc : c ∈ C) (x : V) :
    ∃ n, Near M C n x := by
  induction hM.conn c x with
  | refl => exact ⟨0, .base hc⟩
  | tail _ hab ih =>
    obtain ⟨d, rfl, rfl⟩ := hab
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .step hn⟩

/-- **The forest of the pivot loop extends to a spanning tree**: on a plane map, with a dart `e`
from `u` to `v`, every forest satisfying the invariant is part of a spanning tree rooted at `u`
in which `e` is the parent dart of `v` (the other vertices are hung by a breadth-first search
from the vertices of the move). -/
theorem exists_compat (hM : M.IsPlane) (H : MoveHyp 𝒢 u v) (hI : RInv 𝒢 u v P)
    (heu : M.tail e = u) (hev : M.head e = v) : ∃ T : DTree M.dual, Compat T u v e P := by
  classical
  set C : Finset V := insert u (insert v (moveSet 𝒢 u v)) with hC
  have huC : u ∈ C := mem_insert_self _ _
  set hop : V → ℕ := fun x => Nat.find (near_exists hM huC x) with hhop
  have hq : ∀ x, x ∉ C → ∃ d, M.head d = x ∧ hop (M.tail d) < hop x := by
    intro x hx
    have hs := Nat.find_spec (near_exists hM huC x)
    rcases hn : Nat.find (near_exists hM huC x) with _ | n
    · rw [hn] at hs; cases hs; contradiction
    · rw [hn] at hs
      have hmin : ¬ Near M C n x := Nat.find_min (near_exists hM huC x) (by omega)
      cases hs with
      | mono h => exact absurd h hmin
      | @step _ d h =>
        refine ⟨d, rfl, ?_⟩
        have : hop (M.tail d) ≤ n := Nat.find_min' _ h
        simp only [hhop] at this ⊢
        omega
  have : Nonempty D := ⟨e⟩
  choose! q hq using hq
  let par : V → D := fun x => if x = v then e else
    match P x with
    | some a => a.1
    | none => q x
  have hpar_v : par v = e := by simp [par]
  have hpar_P : ∀ x a, P x = some a → par x = a.1 := by
    intro x a h
    have hxv : x ≠ v := by
      have : x ∈ moveSet 𝒢 u v := by by_contra hm; rw [hI.off x hm] at h; simp at h
      exact (H.mem_moveSet.1 this).2.1
    simp [par, hxv, h]
  have hpar_q : ∀ x, x ∉ C → par x = q x := by
    intro x hx
    have hxv : x ≠ v := fun h => hx (by rw [h, hC]; simp)
    have hxm : x ∉ moveSet 𝒢 u v := fun h => hx (by rw [hC]; simp [h])
    simp [par, hxv, hI.off x hxm]
  have hhead : ∀ x, x ≠ u → M.head (par x) = x := by
    intro x hxu
    by_cases hxv : x = v
    · rw [hxv, hpar_v, hev]
    by_cases hxm : x ∈ moveSet 𝒢 u v
    · obtain ⟨h1, h2, h3⟩ := H.mem_moveSet.1 hxm
      have hsome : ∃ a, P x = some a := by
        by_cases hb : Hang 𝒢 P v x
        · rw [hI.blue x hxm hb]
          exact tpar_isSome (fun a => (H.pos a).le) ((H.reach x h1 h2).1 h3) h2
        · rw [hI.red x hxm hb]
          exact tpar_isSome (fun a => (H.pos a).le) h3 h1
      obtain ⟨a, ha⟩ := hsome
      rw [hpar_P x a ha]
      have : P x = tpar 𝒢 (if Hang 𝒢 P v x then v else u) x := by
        split_ifs with hb
        · exact hI.blue x hxm hb
        · exact hI.red x hxm hb
      rw [this] at ha
      exact (tpar_spec ha).2.1
    · have hxC : x ∉ C := by rw [hC]; simp [hxu, hxv, hxm]
      rw [hpar_q x hxC]; exact (hq x hxC).1
  set up : V → V := upF M.dual u par with hup
  have hup_ne : ∀ x, x ≠ u → up x = M.tail (par x) := fun x hx => by
    simp [hup, upF, hx]; rfl
  have hback : ∀ x y, up x = y → (∃ n, up^[n] y = u) → ∃ n, up^[n] x = u := by
    rintro x y hxy ⟨n, hn⟩
    exact ⟨n + 1, by rw [Function.iterate_succ_apply, hxy]; exact hn⟩
  have hu0 : ∃ n, up^[n] u = u := ⟨0, rfl⟩
  have hv0 : ∃ n, up^[n] v = u :=
    hback v u (by rw [hup_ne v H.ne.symm, hpar_v, heu]) hu0
  have hhang : ∀ r, (∃ n, up^[n] r = u) → ∀ x, Hang 𝒢 P r x → ∃ n, up^[n] x = u := by
    intro r hr x h
    induction h with
    | root => exact hr
    | @step x a hxa _ ih =>
      have hxm : x ∈ moveSet 𝒢 u v := by
        by_contra hm; rw [hI.off x hm] at hxa; simp at hxa
      refine hback x _ ?_ ih
      rw [hup_ne x (H.mem_moveSet.1 hxm).1, hpar_P x a hxa]; rfl
  have hCreach : ∀ x ∈ C, ∃ n, up^[n] x = u := by
    intro x hx
    rw [hC, mem_insert, mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact hu0
    · exact hv0
    · rcases hI.forest H x hx with h | h
      · exact hhang u hu0 x h
      · exact hhang v hv0 x h
  have hreach : ∀ x, ∃ n, up^[n] x = u := by
    intro x
    induction hn : hop x using Nat.strong_induction_on generalizing x with
    | _ m ih =>
      by_cases hx : x ∈ C
      · exact hCreach x hx
      have hxu : x ≠ u := fun h => hx (h ▸ huC)
      refine hback x _ (by rw [hup_ne x hxu, hpar_q x hx]) ?_
      exact ih _ (hn ▸ (hq x hx).2) _ rfl
  refine ⟨⟨u, par, fun x hx => hhead x hx, hreach⟩, rfl, hpar_v, heu, hpar_P⟩

end Klein

/-! ### Around the face -/

section Face

variable {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

local notation "𝒢" => pieceGraph M S ℓ

/-- **Klein's `MINPATH` in the setting of the face** (the article's Lemma 3.4): for the move from
the root `r j = tail (g j)` to the next root, with the boundary dart `g j` (outside the piece)
joining the two trees, every forest satisfying the invariant extends to a spanning tree with
parent dart `g j` at the next root, and for every such tree the active arcs are exactly the arcs
of the piece leaving a vertex reached from the next root whose dart has value `1` on the path of
the dual cotree from the face of `g j` to the face of its reverse. -/
theorem klein_cotree_path (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) {j : ℕ} (hj : j < k)
    {P : V → Option {d // d ∈ S}}
    (hI : RInv 𝒢 (M.tail (g j)) (M.tail (g ((j + 1) % k))) P) :
    (∃ T : DTree M.dual, Compat T (M.tail (g j)) (M.tail (g ((j + 1) % k))) (g j) P) ∧
      ∀ T : DTree M.dual, Compat T (M.tail (g j)) (M.tail (g ((j + 1) % k))) (g j) P →
        ∀ a, RActive 𝒢 (M.tail (g j)) (M.tail (g ((j + 1) % k))) P a ↔
          Reach 𝒢 (M.tail (g ((j + 1) % k))) ((𝒢).src a) ∧
            T.chi (M.face (g j)) (M.face (M.rev (g j))) a.1 = 1 := by
  have hk : 2 ≤ k := H.face.two_le
  have hj' : (j + 1) % k < k := Nat.mod_lt _ (by omega)
  have hne : j ≠ (j + 1) % k := by
    rcases Nat.lt_or_ge (j + 1) k with h | h
    · rw [Nat.mod_eq_of_lt h]; omega
    · rw [show j + 1 = k by omega, Nat.mod_self]; omega
  have H' := moveHyp_of_hyp H hR hj hj' hne
  have hhead : M.head (g j) = M.tail (g ((j + 1) % k)) := by
    rw [CombMap.head, ← M.tail_next, H.face.next j hj]
  have heS : g j ∉ S := fun h => H.noIn _ h ⟨_, hj', hhead.symm⟩
  have hrS : M.rev (g j) ∉ S := fun h => H.noIn _ h ⟨j, hj, by simp⟩
  exact ⟨exists_compat H.plane H' hI rfl hhead,
    fun T hC a => ractive_iff_chi H.plane H' hI hC heS hrS a⟩

end Face

end Klein

end PlanarFlow
