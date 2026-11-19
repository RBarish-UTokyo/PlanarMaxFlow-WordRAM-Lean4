module

public import PlanarFlow.Klein.Dual

/-!
# The values on the dual cotree, `MINPATH` and the update after a pivot

The data of Klein's algorithm in the form of Cabello, Chambers and Erickson (SIAM J. Comput. 42,
2013, Section 3.2), during the move from `u` to `v`: a spanning tree `T` of the map extending the
forest of the pivot loop (`PlanarFlow.Klein.Compat`), the *labels* `T.psum φ x` (the sum of the
weights `φ` of the parent darts from the root `u` down to `x`, the path sums of the primal tree;
`φ = ℓ` on the piece, and `φ e` an arbitrary offset on the dart `e` from `u` to `v`), and a value
`val d` on every dart `d` off the tree (the darts of the dual cotree). The invariant `VInv` is

  `val d = wt d + label (tail d) - label (head d)` for every dart `d` off the tree,

with `wt = ℓ` on the *eligible* darts (the darts of the piece leaving a vertex reached from `v`)
and `wt ≥ L` on the others (a large constant standing for `+∞`). No distance is stored: the
labels are path sums of the primal tree.

* `psum_red`, `psum_blue`: the labels are the distances from `u` on the red vertices and the
  distances from `v` plus `φ e` on the blue ones.
* `minpath_spec`: **`MINPATH` finds a pivot**: a dart of least value on the path of the dual
  cotree from the face of `e` to the face of its reverse (value `1` of `T.chi`) is an active arc of
  least slack, and its value is its slack plus `φ e` (when some vertex is red and `L` exceeds the
  values of the eligible darts, `ℓ d + 4 B < L` for labels bounded by `B`; `abs_psum_le_mul`
  gives such a `B`).
* `pivot_values`: **the update after a pivot**: with `c` the value of the pivot arc `b`, entering
  `y`, and `a = T.par y` the old parent dart of `y`, the tree with `b` as the parent dart of `y`
  (`DTree.reparent`) extends the new forest, and the invariant holds for the values obtained by
  **adding `c` along the old path of the cotree from the face of `a` to the face of its reverse**
  (`c · T.chi`: `ADDPATH`, `+c` on the darts in the direction of the path, `-c` on their reverses)
  and giving the darts of `a` (which joins the cotree, while `b` leaves it) the values
  `wt a - φ a - c` and `wt (rev a) + φ a + c`. These are the operations of the dynamic tree on the
  dual cotree after a pivot: `ADDPATH`, `CUT` of `b`, `LINK` of `a`.
* `reparent_vinv`: the same update for any reparenting of any tree (`c = val b - wt b + φ b`
  for the new parent dart `b`), used between two moves (`PlanarFlow/Klein/Next.lean`).
* `DataRun`, `dataRun_isRun`: **a run on the data** (select a dart of least value on the path,
  pivot, update the tree and the values so that the invariant holds, stop when the least value on
  the path is at least `L - 2B`) **is a run of the pivot loop** (`PlanarFlow.Klein.IsRun`), so it
  ends with the shortest-path tree of `v` after at most `#(tight v \ tight u)` pivots.
* `exists_init_data`, `exists_dataRun`: the initial data exist, and so do runs on the data (with
  the updates of `pivot_values`), for every bound `W` of the weights and `L` large enough.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {S : Finset D} {ℓ : D → ℤ} {u v : V}

local notation "𝒢" => pieceGraph M S ℓ

/-- **The invariant of the values on the dual cotree**: on every dart off the tree, the value is
the weight plus the label of the tail minus the label of the head. -/
def VInv (T : DTree M.dual) (φ wt val : D → ℤ) : Prop :=
  ∀ d, ¬ T.InT d → val d = wt d + T.psum φ (M.tail d) - T.psum φ (M.head d)

/-- The labels are bounded by the number of vertices times a bound of the weights. -/
lemma abs_psum_le_mul (T : DTree M.dual) {φ : D → ℤ} {W : ℤ} (hW : ∀ d, |φ d| ≤ W) (x : V) :
    |T.psum φ x| ≤ Fintype.card V * W := by
  unfold DTree.psum
  have hW0 : 0 ≤ W := le_trans (abs_nonneg _) (hW (T.par x))
  calc |∑ i ∈ range (T.depth x), φ (T.par (T.up^[i] x))|
      ≤ ∑ i ∈ range (T.depth x), |φ (T.par (T.up^[i] x))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range (T.depth x), W := sum_le_sum fun i _ => hW _
    _ = T.depth x * W := by simp
    _ ≤ Fintype.card V * W := by
      have := T.depth_lt_card x
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast this.le) hW0

section Labels

variable {T : DTree M.dual} {e : D} {P : V → Option {d // d ∈ S}} {φ : D → ℤ}

lemma psum_step (H : MoveHyp 𝒢 u v) (hI : RInv 𝒢 u v P) (hC : Compat T u v e P) {x : V}
    {a : {d // d ∈ S}} (hxa : P x = some a) :
    T.psum φ x = T.psum φ ((𝒢).src a) + φ a.1 := by
  have hxm : x ∈ moveSet 𝒢 u v := by
    by_contra hm; rw [hI.off x hm] at hxa; simp at hxa
  have hxr : x ≠ T.root := by rw [hC.root]; exact (H.mem_moveSet.1 hxm).1
  rw [T.psum_of_ne φ hxr, tup_eq T hxr, hC.par x a hxa]
  rfl

/-- **The labels of the red vertices are their distances from `u`.** -/
theorem psum_red (H : MoveHyp 𝒢 u v) (hI : RInv 𝒢 u v P) (hC : Compat T u v e P)
    (hφ : ∀ d ∈ S, φ d = ℓ d) {x : V} (hu : Hang 𝒢 P u x) (hb : ¬ Hang 𝒢 P v x) :
    T.psum φ x = dist 𝒢 u x := by
  have hnn : ∀ a, 0 ≤ (𝒢).len a := fun a => (H.pos a).le
  induction hu with
  | root => rw [← hC.root, T.psum_root, hC.root, dist_self hnn]
  | @step x a hxa _ ih =>
    have hxm : x ∈ moveSet 𝒢 u v := by
      by_contra hm; rw [hI.off x hm] at hxa; simp at hxa
    rw [psum_step H hI hC hxa, ih fun h => hb (.step hxa h), hφ a.1 a.2]
    have := hI.red x hxm hb
    rw [hxa] at this
    obtain ⟨⟨-, ht⟩, hd, -⟩ := tpar_spec this.symm
    rw [← hd]
    exact ht

/-- **The labels of the blue vertices are their distances from `v`, plus `φ e`.** -/
theorem psum_blue (H : MoveHyp 𝒢 u v) (hI : RInv 𝒢 u v P) (hC : Compat T u v e P)
    (hφ : ∀ d ∈ S, φ d = ℓ d) {x : V} (hb : Hang 𝒢 P v x) :
    T.psum φ x = φ e + dist 𝒢 v x := by
  have hnn : ∀ a, 0 ≤ (𝒢).len a := fun a => (H.pos a).le
  induction hb with
  | root =>
    have hvr : v ≠ T.root := by rw [hC.root]; exact H.ne.symm
    rw [T.psum_of_ne φ hvr, tup_eq T hvr, hC.par_v, dist_self hnn, hC.tail, ← hC.root,
      T.psum_root]
    ring
  | @step x a hxa _ ih =>
    have hxm : x ∈ moveSet 𝒢 u v := by
      by_contra hm; rw [hI.off x hm] at hxa; simp at hxa
    rw [psum_step H hI hC hxa, ih, hφ a.1 a.2]
    have hbl : Hang 𝒢 P v x := .step hxa (by assumption)
    have := hI.blue x hxm hbl
    rw [hxa] at this
    obtain ⟨⟨-, ht⟩, hd, -⟩ := tpar_spec this.symm
    rw [← hd, ← ht]
    simp only [pieceGraph]
    ring

end Labels

/-! ### `MINPATH` -/

section MinPath

variable {T : DTree M.dual} {e : D} {P : V → Option {d // d ∈ S}} {φ wt val : D → ℤ}

/-- On an active arc, the value is the slack plus `φ e`, and the dart is on the path of the
cotree (off the tree). -/
lemma val_active (hM : M.IsPlane) (H : MoveHyp 𝒢 u v) (hI : RInv 𝒢 u v P)
    (hC : Compat T u v e P) (heS : e ∉ S) (hrS : M.rev e ∉ S) (hφ : ∀ d ∈ S, φ d = ℓ d)
    (hV : VInv T φ wt val) (hwt : ∀ d ∈ S, Reach 𝒢 v (M.tail d) → wt d = ℓ d)
    {c : {d // d ∈ S}} (hc : RActive 𝒢 u v P c) :
    T.chi (M.face e) (M.face (M.rev e)) c.1 = 1 ∧ ¬ T.InT c.1 ∧
      val c.1 = slack 𝒢 u v c + φ e := by
  obtain ⟨hr, hchi⟩ := (ractive_iff_chi hM H hI hC heS hrS c).1 hc
  have hnT : ¬ T.InT c.1 := fun h => by
    rw [(T.chi_spec hM.dual _ _).2.2.1 _ h] at hchi; exact absurd hchi (by norm_num)
  refine ⟨hchi, hnT, ?_⟩
  obtain ⟨hs, hd, hdr⟩ := hc
  have hdu : Hang 𝒢 P u ((𝒢).dst c) := (hI.forest H _ hd).resolve_right hdr
  rw [hV _ hnT, hwt _ c.2 hr]
  change ℓ c.1 + T.psum φ ((𝒢).src c) - T.psum φ ((𝒢).dst c) = _
  rw [psum_blue H hI hC hφ hs, psum_red H hI hC hφ hdu hdr, slack]
  simp only [pieceGraph]
  ring

/-- **`MINPATH` finds a pivot**: a dart of least value on the path of the dual cotree from the
face of `e` to the face of its reverse is an active arc of least slack, with value its slack plus
`φ e`, as long as some vertex of the move is red. -/
theorem minpath_spec (hM : M.IsPlane) (H : MoveHyp 𝒢 u v) (hI : RInv 𝒢 u v P)
    (hC : Compat T u v e P) (heS : e ∉ S) (hrS : M.rev e ∉ S) (hφ : ∀ d ∈ S, φ d = ℓ d)
    (hV : VInv T φ wt val) {B L : ℤ} (hB : ∀ x, |T.psum φ x| ≤ B)
    (hwt : ∀ d ∈ S, Reach 𝒢 v (M.tail d) → wt d = ℓ d)
    (hwL : ∀ d, (d ∈ S → ¬ Reach 𝒢 v (M.tail d)) → L ≤ wt d) (hL : ∀ d ∈ S, ℓ d + 4 * B < L)
    {d₀ : D} (hd₀ : T.chi (M.face e) (M.face (M.rev e)) d₀ = 1)
    (hmin : ∀ d, T.chi (M.face e) (M.face (M.rev e)) d = 1 → val d₀ ≤ val d)
    (hred : ∃ x ∈ moveSet 𝒢 u v, ¬ Hang 𝒢 P v x) :
    ∃ h : d₀ ∈ S, RActive 𝒢 u v P ⟨d₀, h⟩ ∧
      (∀ c, RActive 𝒢 u v P c → slack 𝒢 u v ⟨d₀, h⟩ ≤ slack 𝒢 u v c) ∧
      val d₀ = slack 𝒢 u v ⟨d₀, h⟩ + φ e := by
  obtain ⟨x, hx, hxr⟩ := hred
  obtain ⟨a, ha⟩ := exists_active H P hx hxr
  obtain ⟨hca, hTa, hva⟩ := val_active hM H hI hC heS hrS hφ hV hwt ha
  have hnT : ¬ T.InT d₀ := fun h => by
    rw [(T.chi_spec hM.dual _ _).2.2.1 _ h] at hd₀; exact absurd hd₀ (by norm_num)
  have h1 := hmin _ hca
  have hB1 := abs_le.1 (hB (M.tail a.1))
  have hB2 := abs_le.1 (hB (M.head a.1))
  have hB3 := abs_le.1 (hB (M.tail d₀))
  have hB4 := abs_le.1 (hB (M.head d₀))
  have hel : d₀ ∈ S ∧ Reach 𝒢 v (M.tail d₀) := by
    by_contra hne
    have hw := hwL d₀ fun h1 h2 => hne ⟨h1, h2⟩
    have := hL a.1 a.2
    rw [hV _ hnT] at h1
    rw [hV _ hTa, hwt _ a.2 (by
      obtain ⟨hs, -, -⟩ := ha; exact hI.reach_v H hs)] at h1
    omega
  obtain ⟨hS0, hr0⟩ := hel
  have hact : RActive 𝒢 u v P ⟨d₀, hS0⟩ :=
    (ractive_iff_chi hM H hI hC heS hrS ⟨d₀, hS0⟩).2 ⟨hr0, hd₀⟩
  have hv0 := (val_active hM H hI hC heS hrS hφ hV hwt hact).2.2
  refine ⟨hS0, hact, fun c hc => ?_, hv0⟩
  obtain ⟨hcc, -, hvc⟩ := val_active hM H hI hC heS hrS hφ hV hwt hc
  have := hmin _ hcc
  rw [hvc] at this
  change val d₀ ≤ _ at this
  rw [hv0] at this
  omega

end MinPath

/-! ### The update after a pivot -/

section Pivot

variable {T : DTree M.dual} {e : D} {P : V → Option {d // d ∈ S}} {φ wt val : D → ℤ}

/-- A vertex above a blue vertex in the tree, other than the root, is blue. -/
lemma hang_of_anc (H : MoveHyp 𝒢 u v) (hC : Compat T u v e P) {y z : V} (hyu : y ≠ u)
    (hz : Hang 𝒢 P v z) (h : T.Anc y z) : Hang 𝒢 P v y := by
  induction hz with
  | root =>
    by_cases hyv : v = y
    · rw [← hyv]; exact .root
    have hvr : v ≠ T.root := by rw [hC.root]; exact H.ne.symm
    rw [T.anc_up_iff hyv, tup_eq T hvr, hC.par_v, hC.tail, ← hC.root, T.anc_root_iff,
      hC.root] at h
    exact absurd h hyu
  | @step z a hza hs ih =>
    by_cases hzy : z = y
    · rw [← hzy]; exact .step hza hs
    have hzr : z ≠ T.root := by
      rw [hC.root]; rintro rfl
      exact absurd (T.anc_root_iff.1 (hC.root ▸ h)) (hC.root ▸ hyu)
    rw [T.anc_up_iff hzy, tup_eq T hzr, hC.par z a hza] at h
    exact ih h

lemma dual_face_rev (d : D) : M.dual.face (M.dual.rev d) = M.head d := rfl

variable (T) in
/-- **The values after a pivot** on the arc `b` entering `y`, with `a = T.par y` the old parent
dart of `y` and `c` the value of `b`: `c · T.chi` added along the old path of the cotree from the
face of `a` to the face of its reverse, and the new values of the two darts of `a`. -/
noncomputable def pivotVal (φ wt val : D → ℤ) (y : V) (c : ℤ) (d : D) : ℤ :=
  if d = T.par y then wt (T.par y) - φ (T.par y) - c
  else if d = M.rev (T.par y) then wt (M.rev (T.par y)) + φ (T.par y) + c
  else val d + c * T.chi (M.face (T.par y)) (M.face (M.rev (T.par y))) d

/-- **The values after a reparenting** (for any tree): when `y` gets the parent dart `b` (off the
tree, its tail not below `y`), the labels of the subtree of `y` change by
`c = val b - wt b + φ b`, and the values `pivotVal` (`c · T.chi` added along the path of the cotree
between the faces of the old parent dart `a = T.par y`, and the new values of the two darts of
`a`) satisfy the invariant `VInv` for the new tree. -/
theorem reparent_vinv (hM : M.IsPlane) (T : DTree M.dual) {y : V} (hyr' : y ≠ T.root) {b : D}
    (hby : M.dual.face (M.dual.rev b) = y) (hna : ¬ T.Anc y (M.dual.face b)) (hbT : ¬ T.InT b)
    (hV : VInv T φ wt val) :
    VInv (T.reparent y b hyr' hby hna) φ wt (pivotVal T φ wt val y (val b - wt b + φ b)) := by
  classical
  set T' := T.reparent y b hyr' hby hna with hT'
  set a := T.par y with ha
  set c := val b - wt b + φ b with hc
  have hpsum : ∀ x, T'.psum φ x = T.psum φ x + if T.Anc y x then c else 0 := by
    intro x
    have := T.psum_reparent (b := y) (e := b) (hb := hyr') (he := hby) (hna := hna) φ x
    refine this.trans ?_
    congr 1
    split_ifs
    · rw [hc, hV _ hbT, ← hby]
      change T.psum φ (M.tail b) + φ b - T.psum φ (M.head b) = _
      ring
    · rfl
  have hupy : ¬ T.Anc y (T.up y) := fun h => by
    have h1 := anc_depth_le T h
    have h2 := T.depth_up hyr'
    omega
  have hay : M.head a = y := tpar_head T hyr'
  have hat : M.tail a = T.up y := (tup_eq T hyr').symm
  have hpy : T.psum φ y = T.psum φ (T.up y) + φ a := T.psum_of_ne φ hyr'
  intro d hd
  simp only [pivotVal]
  split_ifs with hda hdr
  · rw [hda, hpsum, hpsum, hay, hat, hpy]
    simp only [hupy, T.anc_self y, ↓reduceIte]
    ring
  · rw [hdr, hpsum, hpsum, M.tail_rev, M.head_rev, hay, hat, hpy]
    simp only [hupy, T.anc_self y, ↓reduceIte]
    ring
  have hdT : ¬ T.InT d := by
    rintro ⟨x, hx, hdx⟩
    by_cases hxy : x = y
    · subst hxy
      rcases hdx with h | h
      · exact hda h
      · exact hdr h
    · refine hd ⟨x, hx, ?_⟩
      have : T'.par x = T.par x := by
        show Function.update T.par y b x = T.par x
        rw [Function.update_of_ne hxy]
      rw [this]; exact hdx
  rw [chi_par_eq_cross T hM hyr' hda hdr, hV d hdT, hpsum, hpsum]
  simp only [cross, mem_tsub]
  split_ifs <;> ring

/-- **The update after a pivot** (the article's Section 3.2: `ADDPATH`, then `CUT` and `LINK` in
the dual cotree): for an active arc `b` of least slack entering `y`, the tree in which `b` is the
parent dart of `y` extends the new forest (which satisfies the invariant of the pivot loop), and
the values `pivotVal` (with `c = val b`) satisfy the invariant `VInv` for it. -/
theorem pivot_values (hM : M.IsPlane) (H : MoveHyp 𝒢 u v) (hU : UniqTight 𝒢)
    (hI : RInv 𝒢 u v P) (hC : Compat T u v e P) (heS : e ∉ S) (hrS : M.rev e ∉ S)
    (hφ : ∀ d ∈ S, φ d = ℓ d) (hV : VInv T φ wt val)
    (hwt : ∀ d ∈ S, Reach 𝒢 v (M.tail d) → wt d = ℓ d) {b : {d // d ∈ S}} (hb : RActive 𝒢 u v P b)
    (hmin : ∀ c, RActive 𝒢 u v P c → slack 𝒢 u v b ≤ slack 𝒢 u v c) :
    ∃ (hy : M.head b.1 ≠ T.root) (hna : ¬ T.Anc (M.head b.1) (M.tail b.1)),
      RInv 𝒢 u v (Function.update P (M.head b.1) (some b)) ∧
      Compat (T.reparent (M.head b.1) b.1 hy (dual_face_rev b.1) hna) u v e
        (Function.update P (M.head b.1) (some b)) ∧
      VInv (T.reparent (M.head b.1) b.1 hy (dual_face_rev b.1) hna) φ wt
        (pivotVal T φ wt val (M.head b.1) (val b.1)) := by
  obtain ⟨hbs, hy, hyr⟩ := hb
  set y := M.head b.1 with hydef
  have hyu : y ≠ u := (H.mem_moveSet.1 hy).1
  have hyv : y ≠ v := (H.mem_moveSet.1 hy).2.1
  have hyr' : y ≠ T.root := by rw [hC.root]; exact hyu
  have hna : ¬ T.Anc y (M.tail b.1) := fun h => hyr (hang_of_anc H hC hyu hbs h)
  have hst := RInv.step H hI hU ⟨hbs, hy, hyr⟩ hmin
  refine ⟨hyr', hna, hst.2.2.1, ⟨hC.root, ?_, hC.tail, fun x a' hx => ?_⟩, ?_⟩
  · show Function.update T.par y b.1 v = e
    rw [Function.update_of_ne (Ne.symm hyv)]; exact hC.par_v
  · show Function.update T.par y b.1 x = a'.1
    by_cases hxy : x = y
    · rw [hxy, Function.update_self] at hx ⊢
      obtain rfl := Option.some.inj hx
      rfl
    · rw [Function.update_of_ne hxy] at hx ⊢
      exact hC.par x a' hx
  have hbT : ¬ T.InT b.1 := fun h => by
    obtain ⟨hr, hchi⟩ := (ractive_iff_chi hM H hI hC heS hrS b).1 ⟨hbs, hy, hyr⟩
    rw [(T.chi_spec hM.dual _ _).2.2.1 _ h] at hchi; exact absurd hchi (by norm_num)
  have h := reparent_vinv hM T hyr' (dual_face_rev b.1) hna hbT hV
  rwa [hwt _ b.2 (hI.reach_v H hbs), hφ _ b.2, sub_add_cancel] at h

end Pivot

/-! ### A run on the data -/

section Run

variable {φ wt : D → ℤ} {e : D}

/-- **The initial data**: the forest of the pivot loop extends to a spanning tree, and the
values given by the invariant satisfy it. -/
theorem exists_init_data (hM : M.IsPlane) (H : MoveHyp 𝒢 u v) {P : V → Option {d // d ∈ S}}
    (hI : RInv 𝒢 u v P) (heu : M.tail e = u) (hev : M.head e = v) :
    ∃ (T : DTree M.dual) (val : D → ℤ), Compat T u v e P ∧ VInv T φ wt val := by
  obtain ⟨T, hT⟩ := exists_compat hM H hI heu hev
  exact ⟨T, fun d => wt d + T.psum φ (M.tail d) - T.psum φ (M.head d), hT, fun _ _ => rfl⟩

variable (S ℓ u v) in
/-- **A run on the data** of the move from `u` to `v` with the dart `e` from `u` to `v`: trees
`T i`, values `val i` and forests `P i`; at every step the selected dart `d i` has the least value
on the path of the cotree from the face of `e` to the face of its reverse, the next forest pivots
on it, and the next tree and values satisfy the compatibility and the invariant (as
`pivot_values` provides); the run stops when the least value on the path is at least `L - 2B`
(or the path is empty). -/
structure DataRun (φ wt : D → ℤ) (e : D) (B L : ℤ) (T : ℕ → DTree M.dual) (val : ℕ → D → ℤ)
    (P : ℕ → V → Option {d // d ∈ S}) (d : ℕ → D) (m : ℕ) : Prop where
  init : P 0 = tpar 𝒢 u
  compat : ∀ i ≤ m, Compat (T i) u v e (P i)
  vinv : ∀ i ≤ m, VInv (T i) φ wt (val i)
  bound : ∀ i ≤ m, ∀ x, |(T i).psum φ x| ≤ B
  sel : ∀ i < m, (T i).chi (M.face e) (M.face (M.rev e)) (d i) = 1 ∧
    ∀ d', (T i).chi (M.face e) (M.face (M.rev e)) d' = 1 → val i (d i) ≤ val i d'
  low : ∀ i < m, val i (d i) < L - 2 * B
  next : ∀ i < m, ∃ h : d i ∈ S, P (i + 1) = Function.update (P i) (M.head (d i)) (some ⟨d i, h⟩)
  stop : ∀ d', (T m).chi (M.face e) (M.face (M.rev e)) d' = 1 → L - 2 * B ≤ val m d'

/-- **A run on the data is a run of the pivot loop**: the selected darts are active arcs of least
slack, so the forests are those of a run (`IsRun`), and the run ends with the shortest-path tree of
`v` after at most `#(tight v \ tight u)` pivots (`run_spec`). -/
theorem dataRun_isRun (hM : M.IsPlane) (H : MoveHyp 𝒢 u v) (hU : UniqTight 𝒢) (heS : e ∉ S)
    (hrS : M.rev e ∉ S) (hφ : ∀ d ∈ S, φ d = ℓ d) {B L : ℤ}
    (hwt : ∀ d ∈ S, Reach 𝒢 v (M.tail d) → wt d = ℓ d)
    (hwL : ∀ d, (d ∈ S → ¬ Reach 𝒢 v (M.tail d)) → L ≤ wt d) (hL : ∀ d ∈ S, ℓ d + 4 * B < L)
    {T : ℕ → DTree M.dual} {val : ℕ → D → ℤ} {P : ℕ → V → Option {d // d ∈ S}} {d : ℕ → D}
    {m : ℕ} (hr : DataRun S ℓ u v φ wt e B L T val P d m) (b₀ : {d // d ∈ S}) :
    IsRun 𝒢 u v P (fun i => if h : d i ∈ S then ⟨d i, h⟩ else b₀) m := by
  -- a dart of value below `L - 2B` on the path is eligible, and so active
  have helig : ∀ i ≤ m, ∀ d', (T i).chi (M.face e) (M.face (M.rev e)) d' = 1 →
      val i d' < L - 2 * B → d' ∈ S ∧ Reach 𝒢 v (M.tail d') := by
    intro i hi d' hc hlt
    by_contra hne
    have hnT : ¬ (T i).InT d' := fun h => by
      rw [((T i).chi_spec hM.dual _ _).2.2.1 _ h] at hc; exact absurd hc (by norm_num)
    have hw := hwL d' fun h1 h2 => hne ⟨h1, h2⟩
    have hB3 := abs_le.1 (hr.bound i hi (M.tail d'))
    have hB4 := abs_le.1 (hr.bound i hi (M.head d'))
    rw [hr.vinv i hi _ hnT] at hlt
    omega
  have hsel : ∀ i < m, RInv 𝒢 u v (P i) → ∃ h : d i ∈ S, RActive 𝒢 u v (P i) ⟨d i, h⟩ ∧
      ∀ c, RActive 𝒢 u v (P i) c → slack 𝒢 u v ⟨d i, h⟩ ≤ slack 𝒢 u v c := by
    intro i hi hI
    obtain ⟨hc, hm⟩ := hr.sel i hi
    obtain ⟨hS, hreach⟩ := helig i hi.le (d i) hc (hr.low i hi)
    have hact := (ractive_iff_chi hM H hI (hr.compat i hi.le) heS hrS ⟨d i, hS⟩).2 ⟨hreach, hc⟩
    obtain ⟨h, ha, hmin, -⟩ := minpath_spec hM H hI (hr.compat i hi.le) heS hrS hφ
      (hr.vinv i hi.le) (hr.bound i hi.le) hwt hwL hL hc hm ⟨_, hact.2.1, hact.2.2⟩
    exact ⟨h, ha, hmin⟩
  have hinv : ∀ i ≤ m, RInv 𝒢 u v (P i) := by
    intro i
    induction i with
    | zero => exact fun _ => hr.init ▸ rInv_init H
    | succ i ih =>
      intro hi
      obtain ⟨h, hact, hmin⟩ := hsel i (by omega) (ih (by omega))
      obtain ⟨h', hP⟩ := hr.next i (by omega)
      rw [hP]
      exact (RInv.step H (ih (by omega)) hU hact hmin).2.2.1
  refine ⟨hr.init, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun c hc => ?_⟩
  · obtain ⟨h, hact, -⟩ := hsel i hi (hinv i hi.le)
    simpa [h] using hact
  · obtain ⟨h, -, hmin⟩ := hsel i hi (hinv i hi.le)
    simpa [h] using hmin
  · obtain ⟨h, hP⟩ := hr.next i hi
    simp only [h, ↓reduceDIte, hP]
    rfl
  · obtain ⟨hcc, -, hv⟩ := val_active hM H (hinv m le_rfl) (hr.compat m le_rfl) heS hrS hφ
      (hr.vinv m le_rfl) hwt hc
    have h1 := hr.stop _ hcc
    obtain ⟨hs, -, -⟩ := hc
    have hnT : ¬ (T m).InT c.1 := fun h => by
      rw [((T m).chi_spec hM.dual _ _).2.2.1 _ h] at hcc; exact absurd hcc (by norm_num)
    rw [hr.vinv m le_rfl _ hnT, hwt _ c.2 ((hinv m le_rfl).reach_v H hs)] at h1
    have hB3 := abs_le.1 (hr.bound m le_rfl (M.tail c.1))
    have hB4 := abs_le.1 (hr.bound m le_rfl (M.head c.1))
    have := hL c.1 c.2
    omega

/-- **Runs on the data exist from any initial data** (the pure algorithm on the data: select a
dart of least value on the path, pivot as in `pivot_values`, stop when the least value is at least
`L - 2B`), starting from any tree extending the shortest-path tree of `u` and values satisfying
the invariant, with the bound `B = #V · W` of the labels for weights `|φ| ≤ W`; each pivot
changes one parent dart of the tree (the reparenting of `pivot_values`). -/
theorem exists_dataRun_from (hM : M.IsPlane) (H : MoveHyp 𝒢 u v) (hU : UniqTight 𝒢)
    (heS : e ∉ S) (hrS : M.rev e ∉ S) (hφ : ∀ d ∈ S, φ d = ℓ d) {W L : ℤ} (hW : ∀ d, |φ d| ≤ W)
    (hwt : ∀ d ∈ S, Reach 𝒢 v (M.tail d) → wt d = ℓ d)
    (hwL : ∀ d, (d ∈ S → ¬ Reach 𝒢 v (M.tail d)) → L ≤ wt d)
    (hL : ∀ d ∈ S, ℓ d + 4 * (Fintype.card V * W) < L) {T₀ : DTree M.dual} {val₀ : D → ℤ}
    (hC₀ : Compat T₀ u v e (tpar 𝒢 u)) (hV₀ : VInv T₀ φ wt val₀) :
    ∃ (T : ℕ → DTree M.dual) (val : ℕ → D → ℤ) (P : ℕ → V → Option {d // d ∈ S}) (d : ℕ → D)
      (m : ℕ), T 0 = T₀ ∧ val 0 = val₀ ∧
        DataRun S ℓ u v φ wt e (Fintype.card V * W) L T val P d m ∧
        ∀ i < m, (T (i + 1)).root = (T i).root ∧
          (T (i + 1)).par = Function.update (T i).par (M.head (d i)) (d i) := by
  classical
  set B : ℤ := Fintype.card V * W with hBdef
  have hB : ∀ T : DTree M.dual, ∀ x, |T.psum φ x| ≤ B := fun T x => abs_psum_le_mul T hW x
  -- from any state, a run (all the fields but the start)
  have claim : ∀ n : ℕ, ∀ (T₀ : DTree M.dual) (val₀ : D → ℤ) (P₀ : V → Option {d // d ∈ S}),
      RInv 𝒢 u v P₀ → Compat T₀ u v e P₀ → VInv T₀ φ wt val₀ →
      ((moveSet 𝒢 u v).filter fun x => ¬ Hang 𝒢 P₀ v x).card ≤ n →
      ∃ (T : ℕ → DTree M.dual) (val : ℕ → D → ℤ) (P : ℕ → V → Option {d // d ∈ S})
        (d : ℕ → D) (m : ℕ), T 0 = T₀ ∧ val 0 = val₀ ∧ P 0 = P₀ ∧
        (∀ i ≤ m, Compat (T i) u v e (P i)) ∧ (∀ i ≤ m, VInv (T i) φ wt (val i)) ∧
        (∀ i < m, (T i).chi (M.face e) (M.face (M.rev e)) (d i) = 1 ∧
          ∀ d', (T i).chi (M.face e) (M.face (M.rev e)) d' = 1 → val i (d i) ≤ val i d') ∧
        (∀ i < m, val i (d i) < L - 2 * B) ∧
        (∀ i < m, ∃ h : d i ∈ S,
          P (i + 1) = Function.update (P i) (M.head (d i)) (some ⟨d i, h⟩)) ∧
        (∀ i < m, (T (i + 1)).root = (T i).root ∧
          (T (i + 1)).par = Function.update (T i).par (M.head (d i)) (d i)) ∧
        ∀ d', (T m).chi (M.face e) (M.face (M.rev e)) d' = 1 → L - 2 * B ≤ val m d' := by
    -- the measure: the red vertices
    let red : (V → Option {d // d ∈ S}) → Finset V := fun P₀ =>
      (moveSet 𝒢 u v).filter fun x => ¬ Hang 𝒢 P₀ v x
    -- a dart of the path with value below `L - 2B`: one pivot
    have progress : ∀ (T₀ : DTree M.dual) (val₀ : D → ℤ) (P₀ : V → Option {d // d ∈ S}),
        RInv 𝒢 u v P₀ → Compat T₀ u v e P₀ → VInv T₀ φ wt val₀ → ∀ d₀,
        T₀.chi (M.face e) (M.face (M.rev e)) d₀ = 1 → val₀ d₀ < L - 2 * B →
        (∀ d', T₀.chi (M.face e) (M.face (M.rev e)) d' = 1 → val₀ d₀ ≤ val₀ d') →
        ∃ h : d₀ ∈ S, ∃ (T₁ : DTree M.dual) (val₁ : D → ℤ),
          RInv 𝒢 u v (Function.update P₀ (M.head d₀) (some ⟨d₀, h⟩)) ∧
          Compat T₁ u v e (Function.update P₀ (M.head d₀) (some ⟨d₀, h⟩)) ∧
          VInv T₁ φ wt val₁ ∧
          (T₁.root = T₀.root ∧ T₁.par = Function.update T₀.par (M.head d₀) d₀) ∧
          (red (Function.update P₀ (M.head d₀) (some ⟨d₀, h⟩))).card < (red P₀).card := by
      intro T₀ val₀ P₀ hI hC hV d₀ hd hlow hmin
      have hnT : ¬ T₀.InT d₀ := fun h => by
        rw [(T₀.chi_spec hM.dual _ _).2.2.1 _ h] at hd; exact absurd hd (by norm_num)
      have hel : d₀ ∈ S ∧ Reach 𝒢 v (M.tail d₀) := by
        by_contra hne
        have hw := hwL d₀ fun h1 h2 => hne ⟨h1, h2⟩
        have hB3 := abs_le.1 (hB T₀ (M.tail d₀))
        have hB4 := abs_le.1 (hB T₀ (M.head d₀))
        rw [hV _ hnT] at hlow
        omega
      have hact := (ractive_iff_chi hM H hI hC heS hrS ⟨d₀, hel.1⟩).2 ⟨hel.2, hd⟩
      obtain ⟨h, ha, hm, -⟩ := minpath_spec hM H hI hC heS hrS hφ hV (hB T₀) hwt hwL hL hd hmin
        ⟨_, hact.2.1, hact.2.2⟩
      obtain ⟨hy, hna, hI', hC', hV'⟩ := pivot_values hM H hU hI hC heS hrS hφ hV hwt ha hm
      have hst := RInv.step H hI hU ha hm
      refine ⟨h, _, _, hI', hC', hV', ⟨rfl, rfl⟩, card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩⟩
      · simp only [red, mem_filter] at hx ⊢
        exact ⟨hx.1, fun h' => hx.2 (hst.2.2.2.1 x h')⟩
      · have := hsub (mem_filter.2 ⟨ha.2.1, ha.2.2⟩)
        exact (mem_filter.1 this).2 hst.2.2.2.2
    have hmin_ex : ∀ (T₀ : DTree M.dual) (val₀ : D → ℤ),
        (∃ d', T₀.chi (M.face e) (M.face (M.rev e)) d' = 1 ∧ val₀ d' < L - 2 * B) →
        ∃ d₀, T₀.chi (M.face e) (M.face (M.rev e)) d₀ = 1 ∧ val₀ d₀ < L - 2 * B ∧
          ∀ d', T₀.chi (M.face e) (M.face (M.rev e)) d' = 1 → val₀ d₀ ≤ val₀ d' := by
      rintro T₀ val₀ ⟨d', hd', hlt⟩
      obtain ⟨d₀, hd₀, hmin⟩ := (univ.filter fun d =>
        T₀.chi (M.face e) (M.face (M.rev e)) d = 1).exists_min_image val₀
          ⟨d', by simpa using hd'⟩
      refine ⟨d₀, by simpa using hd₀, lt_of_le_of_lt (hmin d' (by simpa using hd')) hlt,
        fun d'' hd'' => hmin d'' (by simpa using hd'')⟩
    intro n
    induction n with
    | zero =>
      intro T₀ val₀ P₀ hI hC hV hn
      by_cases hex : ∃ d', T₀.chi (M.face e) (M.face (M.rev e)) d' = 1 ∧ val₀ d' < L - 2 * B
      · exfalso
        obtain ⟨d₀, hd₀, hlt, hmin⟩ := hmin_ex T₀ val₀ hex
        obtain ⟨_, _, _, _, _, _, _, hlt'⟩ := progress T₀ val₀ P₀ hI hC hV d₀ hd₀ hlt hmin
        simp only [red] at hlt'
        omega
      · push Not at hex
        exact ⟨fun _ => T₀, fun _ => val₀, fun _ => P₀, fun _ => e, 0, rfl, rfl, rfl,
          fun _ _ => hC, fun _ _ => hV, fun i hi => absurd hi (by omega),
          fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega),
          fun i hi => absurd hi (by omega), hex⟩
    | succ n ih =>
      intro T₀ val₀ P₀ hI hC hV hn
      by_cases hex : ∃ d', T₀.chi (M.face e) (M.face (M.rev e)) d' = 1 ∧ val₀ d' < L - 2 * B
      · obtain ⟨d₀, hd₀, hlt, hmin⟩ := hmin_ex T₀ val₀ hex
        obtain ⟨h, T₁, val₁, hI₁, hC₁, hV₁, hst₁, hlt'⟩ :=
          progress T₀ val₀ P₀ hI hC hV d₀ hd₀ hlt hmin
        obtain ⟨T, val, P, d, m, hT0, hv0, hP0, hCs, hVs, hsel, hlow, hnext, hsteps, hstop⟩ :=
          ih T₁ val₁ _ hI₁ hC₁ hV₁ (by simp only [red] at hlt' hn ⊢; omega)
        refine ⟨fun i => if i = 0 then T₀ else T (i - 1),
          fun i => if i = 0 then val₀ else val (i - 1),
          fun i => if i = 0 then P₀ else P (i - 1),
          fun i => if i = 0 then d₀ else d (i - 1), m + 1, by simp, by simp, by simp,
          fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
          fun i hi => ?_, ?_⟩
        · rcases i with _ | i
          · simpa using hC
          · simpa using hCs i (by omega)
        · rcases i with _ | i
          · simpa using hV
          · simpa using hVs i (by omega)
        · rcases i with _ | i
          · simpa using ⟨hd₀, hmin⟩
          · simpa using hsel i (by omega)
        · rcases i with _ | i
          · simpa using hlt
          · simpa using hlow i (by omega)
        · rcases i with _ | i
          · refine ⟨h, ?_⟩
            simp only [↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel]
            rw [hP0]
          · obtain ⟨h', hP⟩ := hnext i (by omega)
            refine ⟨by simpa using h', ?_⟩
            simpa using hP
        · rcases i with _ | i
          · simpa [hT0] using hst₁
          · simpa using hsteps i (by omega)
        · simpa using hstop
      · push Not at hex
        exact ⟨fun _ => T₀, fun _ => val₀, fun _ => P₀, fun _ => e, 0, rfl, rfl, rfl,
          fun _ _ => hC, fun _ _ => hV, fun i hi => absurd hi (by omega),
          fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega),
          fun i hi => absurd hi (by omega), hex⟩
  obtain ⟨T, val, P, d, m, h0, hv0, hP0, hC', hV', hsel, hlow, hnext, hsteps, hstop⟩ :=
    claim _ T₀ val₀ _ (rInv_init H) hC₀ hV₀ le_rfl
  exact ⟨T, val, P, d, m, h0, hv0,
    ⟨hP0, hC', hV', fun i _ => hB (T i), hsel, hlow, hnext, hstop⟩, hsteps⟩

/-- **Runs on the data exist** (from the initial data of `exists_init_data`), with the bound
`B = #V · W` of the labels for weights `|φ| ≤ W`. -/
theorem exists_dataRun (hM : M.IsPlane) (H : MoveHyp 𝒢 u v) (hU : UniqTight 𝒢) (heS : e ∉ S)
    (hrS : M.rev e ∉ S) (hφ : ∀ d ∈ S, φ d = ℓ d) {W L : ℤ} (hW : ∀ d, |φ d| ≤ W)
    (hwt : ∀ d ∈ S, Reach 𝒢 v (M.tail d) → wt d = ℓ d)
    (hwL : ∀ d, (d ∈ S → ¬ Reach 𝒢 v (M.tail d)) → L ≤ wt d)
    (hL : ∀ d ∈ S, ℓ d + 4 * (Fintype.card V * W) < L) (heu : M.tail e = u)
    (hev : M.head e = v) :
    ∃ (T : ℕ → DTree M.dual) (val : ℕ → D → ℤ) (P : ℕ → V → Option {d // d ∈ S}) (d : ℕ → D)
      (m : ℕ), DataRun S ℓ u v φ wt e (Fintype.card V * W) L T val P d m := by
  obtain ⟨T₀, val₀, hC, hV⟩ := exists_init_data (φ := φ) (wt := wt) hM H (rInv_init H) heu hev
  obtain ⟨T, val, P, d, m, -, -, h, -⟩ :=
    exists_dataRun_from hM H hU heS hrS hφ hW hwt hwL hL hC hV
  exact ⟨T, val, P, d, m, h⟩

end Run

end Klein

end PlanarFlow
