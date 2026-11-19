module

public import PlanarFlow.BKMNW.FaceCross

/-!
# The dense distance graph of FixConservationOnPath satisfies the crossing inequality

FixConservationOnPath (`PlanarFlow.BKMNW.fixPath`) builds the dense distance graph
`⟨P.faces, mssp P.darts (c - f₀)⟩` of `H*`, the dual graph minus the darts of a simple path `P`,
on the faces along `P`, and runs FR-Dijkstra on it. FR-Dijkstra on the machine
(`PlanarFlow.BKMNW.frProg_isDist`) asks for the crossing inequality `Monge.Crossing b D` of the
lengths between the corners `0, …, b - 1` of the dense distance graph, in the cyclic order of a
face. The faces along `P` lie on one face of `H*`, whose boundary is traced by the walk around the
path (`PlanarFlow.BKMNW.tour`); a face of the dual may occur several times along it (once for every
side of a dart of `P` that it borders), so the corners are the *positions* along the walk, and a
face may have several corners (copies, at distance `0` from each other).

* `fixCorner P j`: the face of the `j`-th dart of the walk around `P` from its first dart;
  `fixPer P`: the period of the walk. Every face along `P` is a corner (`exists_fixCorners`, with
  the corners in increasing order).
* `Cut.crossing`: on any cut of the dual graph minus `L` (`PlanarFlow.BKMNW.Cut`: the plane map in
  which the article runs Klein's algorithm, with a ring of roots), the distances in `H*` between
  the faces of increasing roots satisfy the crossing inequality
  (`PlanarFlow.BKMNW.crossing_faceCycle_pend`: each root is a corner of the face of the ring, with a
  pendant arc of length `0` to its face).
* `fixCorner_reach`: the lengths between corners are finite: around the path, consecutive corners
  are joined by an arc of `H*` or are the same face.
* `crossing_fixDDG`: **for any implementation `mssp` of multiple-source shortest paths meeting
  its specification along `P` (`MSSPSpecAt`) and lengths nonnegative off `P`, the lengths
  `mssp P.darts ℓ (fixCorner P (s i)) (fixCorner P (s j))` between increasing corners satisfy
  `Monge.Crossing`**, the hypothesis of `frProg_isDist`; `crossing_fixPath`: the same for the
  dense distance graph of `fixPath`, with `ℓ = c - f₀` for a pseudoflow `f₀`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-! ### On a cut -/

namespace Cut

variable {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
  [Fintype F'] [DecidableEq F']
variable {M : CombMap D V F} {ℓ : D → ℤ} {L : List D}

/-- **On a cut, the distances in the dual graph minus `L` between the faces of increasing roots
satisfy the crossing inequality.** For roots `s 0 < ⋯ < s (b - 1) < k`, if `δ x` are the
distances in `H*` from the face `x` (for the faces of these roots), and they are finite between
these faces (`Dm i j` from the face of the root `s i` to the face of the root `s j`), then `Dm`
satisfies `Monge.Crossing`. -/
theorem crossing (C : Cut M ℓ L D' V' F') {b : ℕ} {s : ℕ → ℕ}
    (hs : ∀ i j, i < j → j < b → s i < s j) (hsk : ∀ i < b, s i < C.k)
    {δ : F → F → Option ℤ}
    (hδ : ∀ i < b, IsDist ((M.dualGraph ℓ).restrict fun e => e ∉ L) (C.root (s i))
      (δ (C.root (s i))))
    {Dm : ℕ → ℕ → ℤ} (hD : ∀ i < b, ∀ j < b, δ (C.root (s i)) (C.root (s j)) = some (Dm i j)) :
    Monge.Crossing b Dm := by
  classical
  have hpend : ∀ j < C.k, ∃ d, C.map.tail (C.map.rev d) = C.vx (C.root j) ∧
      C.map.head (C.map.rev d) = C.map.tail (C.g j) := by
    intro j hj
    obtain ⟨d, hd, h1⟩ := C.pend j hj
    rcases C.cover d hd with ⟨e, he⟩ | ⟨i, hi, h1', h2, -⟩
    · rw [← he, C.tail_arc] at h1
      exact absurd h1.symm (C.root_ne j hj _)
    · have hij : i = j := C.hyp.face.inj i hi j hj (h1'.symm.trans h1)
      subst hij
      exact ⟨d, by rw [CombMap.tail_rev]; exact h2, by rw [CombMap.head_rev]; exact h1⟩
  have : Nonempty D' := ⟨C.g 0⟩
  choose! pd hpd using fun j (hj : j < b) => hpend (s j) (hsk j hj)
  refine crossing_faceCycle_pend C.hyp.plane C.hyp.rot C.hyp.face (S := C.piece) (ℓ := C.len)
    (fun d hd i hi h => C.hyp.noIn d hd ⟨i, hi, h.symm⟩) hs hsk
    (w := fun j => C.vx (C.root (s j))) (pd := fun j => C.map.rev (pd j)) (fun j hj => (hpd j hj).1)
    (fun j hj => (hpd j hj).2) fun i hi => ?_
  have hnn : ∀ a, 0 ≤ (MSSP.pieceGraph C.map C.piece C.len).len a :=
    fun a => C.hyp.nonneg a.1 a.2
  have hsi := hsk i hi
  refine ⟨MSSP.odist (MSSP.pieceGraph C.map C.piece C.len) (C.map.tail (C.g (s i))),
    isDist_odist hnn _, fun j hj => ?_⟩
  have hemb := isDist_of_embed (G := (M.dualGraph ℓ).restrict fun e => e ∉ L)
    (G' := MSSP.pieceGraph C.map C.piece C.len) (arc := C.arc) (x₀ := C.root (s i)) C.vx_inj
    C.tail_arc C.head_arc C.len_arc (fun b' => ?_) (C.root_ne (s i) hsi) (fun b' hb => ?_) ?_
    (isDist_odist hnn (C.map.tail (C.g (s i))))
  · have e := congrFun ((hδ i hi).unique hemb) (C.root (s j))
    rw [← hD i hi j hj, e]
  · rcases C.cover b'.1 b'.2 with ⟨e, he⟩ | ⟨i', hi', h1, -, -⟩
    · exact Or.inl ⟨e, Subtype.ext he⟩
    · right; intro y; change C.map.tail b'.1 ≠ _; rw [h1]; exact C.root_ne i' hi' y
  · change C.map.tail b'.1 = C.map.tail (C.g (s i)) at hb
    rcases C.cover b'.1 b'.2 with ⟨e, he⟩ | ⟨i', hi', h1, h2, h3⟩
    · rw [← he, C.tail_arc] at hb
      exact absurd hb.symm (C.root_ne (s i) hsi _)
    · have hij : i' = s i := C.hyp.face.inj i' hi' (s i) hsi (h1.symm.trans hb)
      subst hij
      exact ⟨h2, h3⟩
  · obtain ⟨d, hd, h1⟩ := C.pend (s i) hsi
    exact ⟨⟨d, hd⟩, h1⟩

end Cut

/-! ### The corners along a simple path -/

section Corners

variable {M : CombMap D V F}

variable (M) in
/-- The `j`-th corner of the face of `H*` along the path `P`: the face of the `j`-th dart of the
walk around `P` (`tour`) from the first dart of `P`. -/
def fixCorner (P : SPath M) (j : ℕ) : F := M.face ((tour M P.darts)^[j] (P.d 0))

variable (M) in
/-- The number of corners: the period of the walk around `P` at its first dart. -/
noncomputable def fixPer (P : SPath M) : ℕ := minimalPeriod (tour M P.darts) (P.d 0)

/-- The first dart of the path, as a dart leaving the path. -/
def fixT0 (P : SPath M) (hk : 0 < P.k) : CutT M P.darts :=
  ⟨P.d 0, tail_mem_cutS (P.d_mem 0 hk)⟩

lemma fixCorner_eq (P : SPath M) (hk : 0 < P.k) (j : ℕ) :
    fixCorner M P j = M.face ((tourT P.rev_mem_darts')^[j] (fixT0 P hk)).1 := by
  rw [tourT_iterate_val]; rfl

lemma fixPer_eq (P : SPath M) (hk : 0 < P.k) :
    fixPer M P = minimalPeriod (tourT P.rev_mem_darts') (fixT0 P hk) := by
  unfold fixPer
  refine minimalPeriod_eq_minimalPeriod_iff.2 fun n => ?_
  unfold IsPeriodicPt IsFixedPt
  rw [Subtype.ext_iff, tourT_iterate_val]
  rfl

lemma fixPer_pos (P : SPath M) : 0 < fixPer M P :=
  minimalPeriod_pos_of_mem_periodicPts ((tour_injective P.rev_mem_darts').mem_periodicPts _)

lemma fixCorner_mod (P : SPath M) (j : ℕ) : fixCorner M P (j % fixPer M P) = fixCorner M P j := by
  unfold fixCorner fixPer
  rw [iterate_mod_minimalPeriod_eq]

/-- The walk around the path visits every dart leaving the path. -/
lemma fix_horb (hrot : M.RotTrans) (P : SPath M) (hk : 0 < P.k) (t : CutT M P.darts) :
    ItReach (tourT P.rev_mem_darts') (fixT0 P hk) t := by
  obtain ⟨e, he, h⟩ := mem_cutS.1 t.2
  obtain ⟨i, hi, hi'⟩ := P.tail_mem_darts he
  obtain ⟨n, hn⟩ := tour_reach hrot P hk hi (h.symm.trans hi')
  exact ⟨n, Subtype.ext (by rw [tourT_iterate_val]; exact hn)⟩

lemma fix_htwo (P : SPath M) (hk : 0 < P.k) :
    tourT P.rev_mem_darts' (fixT0 P hk) ≠ fixT0 P hk := by
  intro h
  have h1 := congrArg Subtype.val h
  rw [tourT_val, fixT0, tour_of_mem (P.d_mem 0 hk)] at h1
  have h2 := congrArg M.tail h1
  rw [M.tail_next, M.tail_rev, P.head_d 0 hk, P.tail_d 0 hk] at h2
  exact absurd (P.inj 1 hk 0 (Nat.zero_le _) h2) one_ne_zero

lemma fix_hcount (P : SPath M) (hk : 0 < P.k) :
    P.darts.toFinset.card + 2 = 2 * (cutS M P.darts).card := by
  rw [P.card_darts, P.card_cutS hk]
  ring

/-- **The cut of the dual graph minus the path `P`** (`PlanarFlow.BKMNW.cutOf`), with the roots
in the order of the walk around `P` from its first dart. -/
noncomputable def fixCut (hM : M.IsPlane) (hrot : M.RotTrans) (P : SPath M) (hk : 0 < P.k)
    (ℓ : D → ℤ) (hnn : ∀ e, e ∉ P.darts → 0 ≤ ℓ e) :
    Cut M ℓ P.darts (CutD M P.darts) (CutV M P.darts) (CutF M P.darts) :=
  have : Nonempty D := ⟨P.d 0⟩
  cutOf P.rev_mem_darts' (fixT0 P hk) ℓ hnn hM (faceTrans_of_plane hM hrot)
    (fix_horb hrot P hk) (fix_htwo P hk) (fix_hcount P hk)

lemma fixCut_k (hM : M.IsPlane) (hrot : M.RotTrans) (P : SPath M) (hk : 0 < P.k) (ℓ : D → ℤ)
    (hnn : ∀ e, e ∉ P.darts → 0 ≤ ℓ e) : (fixCut hM hrot P hk ℓ hnn).k = fixPer M P :=
  (fixPer_eq P hk).symm

lemma fixCut_root (hM : M.IsPlane) (hrot : M.RotTrans) (P : SPath M) (hk : 0 < P.k)
    (ℓ : D → ℤ) (hnn : ∀ e, e ∉ P.darts → 0 ≤ ℓ e) (j : ℕ) :
    (fixCut hM hrot P hk ℓ hnn).root j = fixCorner M P j :=
  (fixCorner_eq P hk j).symm

/-- There are at least two corners. -/
lemma two_le_fixPer (hM : M.IsPlane) (hrot : M.RotTrans) (P : SPath M) (hk : 0 < P.k) :
    2 ≤ fixPer M P := by
  rw [← fixCut_k hM hrot P hk 0 (fun _ _ => le_rfl)]
  exact (fixCut hM hrot P hk 0 fun _ _ => le_rfl).hyp.face.two_le

/-- **Every face along the path is a corner**, and the corners whose faces lie along the path,
in increasing order, cover them. -/
theorem exists_fixCorners (hrot : M.RotTrans) (P : SPath M) :
    ∃ (b : ℕ) (s : ℕ → ℕ), (∀ i j, i < j → j < b → s i < s j) ∧ (∀ i < b, s i < fixPer M P) ∧
      (∀ i < b, fixCorner M P (s i) ∈ P.faces) ∧
      ∀ x ∈ P.faces, ∃ i < b, fixCorner M P (s i) = x := by
  classical
  let S : Finset ℕ := (range (fixPer M P)).filter fun i => fixCorner M P i ∈ P.faces
  let s : ℕ → ℕ := fun i => if h : i < S.card then S.orderEmbOfFin rfl ⟨i, h⟩ else 0
  have hmem : ∀ i (h : i < S.card), s i ∈ S := fun i h => by
    simp only [s, h, ↓reduceDIte]; exact S.orderEmbOfFin_mem rfl _
  refine ⟨S.card, s, fun i j hij hj => ?_, fun i hi => ?_, fun i hi => ?_, fun x hx => ?_⟩
  · simp only [s, hj, show i < S.card by omega, ↓reduceDIte]
    exact (S.orderEmbOfFin rfl).strictMono (show (⟨i, by omega⟩ : Fin S.card) < ⟨j, hj⟩ from hij)
  · exact mem_range.1 (mem_filter.1 (hmem i hi)).1
  · exact (mem_filter.1 (hmem i hi)).2
  · rcases Nat.eq_zero_or_pos P.k with h0 | hk
    · simp [SPath.faces, SPath.darts, h0] at hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
    obtain ⟨n, hn⟩ := fix_horb hrot P hk ⟨e, tail_mem_cutS he⟩
    have hfe : fixCorner M P n = M.face e := by
      rw [fixCorner_eq P hk, hn]
    have hper := fixPer_pos P
    have hnS : n % fixPer M P ∈ S := mem_filter.2 ⟨mem_range.2 (Nat.mod_lt _ hper),
      by rw [fixCorner_mod, hfe]; exact hx⟩
    have hrange := S.range_orderEmbOfFin rfl
    have : n % fixPer M P ∈ Set.range (S.orderEmbOfFin rfl) := by rw [hrange]; exact hnS
    obtain ⟨⟨i, hi⟩, hi'⟩ := this
    refine ⟨i, hi, ?_⟩
    simp only [s, hi, ↓reduceDIte, hi', fixCorner_mod, hfe]

/-- Consecutive corners are joined in `H*` (by the dart, when it is off the path; otherwise they
are the same face). -/
lemma fixCorner_step (P : SPath M) (ℓ : D → ℤ) (j : ℕ) :
    ∃ l, IsWalk ((M.dualGraph ℓ).restrict fun e => e ∉ P.darts) (fixCorner M P j) l
      (fixCorner M P (j + 1)) := by
  unfold fixCorner
  rw [iterate_succ_apply']
  generalize (tour M P.darts)^[j] (P.d 0) = x
  by_cases hx : x ∈ P.darts
  · refine ⟨[], ?_⟩
    rw [isWalk_nil, tour_of_mem hx, M.face_next]
  · refine ⟨[⟨x, hx⟩], isWalk_singleton.2 ⟨rfl, ?_⟩⟩
    show M.face (M.rev x) = _
    rw [tour_of_not_mem hx, CombMap.rot, M.face_next]

lemma fixCorner_walk (P : SPath M) (ℓ : D → ℤ) (j n : ℕ) :
    ∃ l, IsWalk ((M.dualGraph ℓ).restrict fun e => e ∉ P.darts) (fixCorner M P j) l
      (fixCorner M P (j + n)) := by
  induction n with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
    obtain ⟨l, hl⟩ := ih
    obtain ⟨l', hl'⟩ := fixCorner_step P ℓ (j + n)
    exact ⟨l ++ l', hl.append hl'⟩

/-- **Every corner is reached from every corner in `H*`.** -/
lemma fixCorner_reach (P : SPath M) (ℓ : D → ℤ) (i j : ℕ) :
    ∃ l, IsWalk ((M.dualGraph ℓ).restrict fun e => e ∉ P.darts) (fixCorner M P i) l
      (fixCorner M P j) := by
  have hper := fixPer_pos P
  obtain ⟨l, hl⟩ := fixCorner_walk P ℓ i (fixPer M P * (i + 1) - i + j)
  refine ⟨l, ?_⟩
  have e : i + (fixPer M P * (i + 1) - i + j) = j + fixPer M P * (i + 1) := by
    have : i < fixPer M P * (i + 1) := by nlinarith
    omega
  rw [e, ← fixCorner_mod P (j + _), Nat.add_mul_mod_self_left, fixCorner_mod] at hl
  exact hl

/-- **The lengths of `H*` between corners are finite**: the distances from a corner, given as
`IsDist`, are defined at every corner. -/
lemma fixCorner_some (P : SPath M) {ℓ : D → ℤ} {i : ℕ} {δ : F → Option ℤ}
    (hδ : IsDist ((M.dualGraph ℓ).restrict fun e => e ∉ P.darts) (fixCorner M P i) δ) (j : ℕ) :
    ∃ a, δ (fixCorner M P j) = some a := by
  obtain ⟨l, hl⟩ := fixCorner_reach P ℓ i j
  obtain ⟨a, ha, -⟩ := hδ.exists_le hl
  exact ⟨a, ha⟩

/-! ### The dense distance graph of FixConservationOnPath -/

/-- **The crossing inequality of the dense distance graph of `H*` between the corners along the
path.** For a plane map with transitive rotations, a simple path `P`, lengths `ℓ` nonnegative off
`P`, any implementation `mssp` of multiple-source shortest paths meeting its specification along
`P` (`MSSPSpecAt`), and corners `s 0 < ⋯ < s (b - 1) < fixPer M P` whose faces lie along `P`, the
lengths `D i j = mssp P.darts ℓ (fixCorner M P (s i)) (fixCorner M P (s j))` (all finite,
`fixDDG_some`) satisfy `Monge.Crossing b D`: the hypothesis `hDc` of FR-Dijkstra on the machine
(`PlanarFlow.BKMNW.frProg_isDist`). -/
theorem crossing_fixDDG (hM : M.IsPlane) (hrot : M.RotTrans) (P : SPath M)
    {mssp : List D → (D → ℤ) → F → F → Option ℤ} (hmssp : MSSPSpecAt M mssp P) {ℓ : D → ℤ}
    (hnn : ∀ e, e ∉ P.darts → 0 ≤ ℓ e) {b : ℕ} {s : ℕ → ℕ}
    (hs : ∀ i j, i < j → j < b → s i < s j) (hsk : ∀ i < b, s i < fixPer M P)
    (hX : ∀ i < b, fixCorner M P (s i) ∈ P.faces) :
    Monge.Crossing b
      (fun i j => (mssp P.darts ℓ (fixCorner M P (s i)) (fixCorner M P (s j))).getD 0) := by
  rcases Nat.eq_zero_or_pos P.k with h0 | hk
  · intro i i' j j' hi hj hi' hj' _
    have := hX i (by omega)
    simp [SPath.faces, SPath.darts, h0] at this
  set C := fixCut hM hrot P hk ℓ hnn
  have hroot : ∀ j, C.root j = fixCorner M P j := fixCut_root hM hrot P hk ℓ hnn
  have hδ : ∀ i < b, IsDist ((M.dualGraph ℓ).restrict fun e => e ∉ P.darts) (C.root (s i))
      (mssp P.darts ℓ (C.root (s i))) := fun i hi => by
    rw [hroot]; exact hmssp ℓ hnn _ (hX i hi)
  refine C.crossing hs (fun i hi => by rw [fixCut_k]; exact hsk i hi) hδ fun i hi j hj => ?_
  obtain ⟨a, ha⟩ := fixCorner_some P (hδ i hi |> fun h => by rw [hroot] at h; exact h) (s j)
  simp only [hroot, ha, Option.getD_some]

/-- The lengths of the dense distance graph between corners are finite. -/
theorem fixDDG_some (P : SPath M) {mssp : List D → (D → ℤ) → F → F → Option ℤ}
    (hmssp : MSSPSpecAt M mssp P) {ℓ : D → ℤ} (hnn : ∀ e, e ∉ P.darts → 0 ≤ ℓ e) {i : ℕ}
    (hi : fixCorner M P i ∈ P.faces) (j : ℕ) :
    ∃ a, mssp P.darts ℓ (fixCorner M P i) (fixCorner M P j) = some a :=
  fixCorner_some P (hmssp ℓ hnn _ hi) j

/-- **The dense distance graph of FixConservationOnPath satisfies the crossing inequality**
between increasing corners along the path: the lengths
`(⟨P.faces, mssp P.darts (c - f₀)⟩ : DDG F).len` of `fixPath`, for a pseudoflow `f₀`. -/
theorem crossing_fixPath (hM : M.IsPlane) (hrot : M.RotTrans) (P : SPath M)
    {mssp : List D → (D → ℤ) → F → F → Option ℤ} (hmssp : MSSPSpecAt M mssp P) {c f₀ : D → ℤ}
    (hf₀ : IsPseudo M c f₀) {b : ℕ} {s : ℕ → ℕ} (hs : ∀ i j, i < j → j < b → s i < s j)
    (hsk : ∀ i < b, s i < fixPer M P) (hX : ∀ i < b, fixCorner M P (s i) ∈ P.faces) :
    Monge.Crossing b (fun i j => ((⟨P.faces, mssp P.darts (c - f₀)⟩ : DDG F).len
      (fixCorner M P (s i)) (fixCorner M P (s j))).getD 0) :=
  crossing_fixDDG hM hrot P hmssp (fun e _ => by
    simp only [Pi.sub_apply]; linarith [hf₀.le_cap e]) hs hsk hX

end Corners

end BKMNW

end PlanarFlow
