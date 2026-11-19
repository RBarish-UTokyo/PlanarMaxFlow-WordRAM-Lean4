module

public import PlanarFlow.Klein.Next

/-!
# The full trip around the face, on the data

Klein's algorithm in the form of Cabello, Chambers and Erickson (SIAM J. Comput. 42, 2013,
Section 3.2) moves the source around the face: the move `j` goes from the root
`tripSrc j = tail (g (j % k))` to the next root `tripDst j = tail (g ((j + 1) % k))`, with the
boundary dart `g (j % k)` from the first to the second. The data of a move are those of
`PlanarFlow.Klein.DataRun`: trees `T i` extending the forests of the pivot loop, labels (the
path sums `T.psum tripφ`, with the weights `tripφ = ℓ` on the piece and `0` elsewhere) and values
`val i` on the darts off the tree (the dual cotree), with

* the weights `tripWt j` of the values: `ℓ` on the darts of the piece leaving a vertex reached
  from the target `tripDst j`, and the large constant `tripL` elsewhere (they change between two
  moves only on the darts of the piece leaving the two roots involved);
* the bound `tripB = #V · tripW` of the labels, `tripW = ∑_{d ∈ S} |ℓ d|`.

* `IsTrip`: **the specification of a trip**: every move is a run on the data
  (`DataRun`), every pivot changes one parent dart of the tree, and the tree at the start of the
  move `j + 1` is obtained from the tree at the end of the move `j` by re-rooting it at the new
  source and giving the new target its boundary dart as parent dart (`next_move`).
* `exists_trip`: **trips exist** (chaining `exists_dataRun_from` with `next_compat`), and
  `kleinTrip` is one (chosen; a description of the data, not an implementation).
* `IsTrip.labels`: **the labels at the start of every move are the distances from its source**
  (on the vertices it reaches, `psum_red`).
* `IsTrip.pivots`: **the trip makes at most `#S` pivots in total** over the `k` moves
  (`klein_run_pivots`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

/-! ### The parameters of the trip -/

section Params

variable (S ℓ) in
/-- The weights of the labels: `ℓ` on the piece, `0` elsewhere. -/
def tripφ (d : D) : ℤ := if d ∈ S then ℓ d else 0

variable (S ℓ) in
/-- A bound of the weights. -/
def tripW : ℤ := ∑ d ∈ S, |ℓ d|

variable (V S ℓ) in
/-- The bound `#V · tripW` of the labels. -/
def tripB : ℤ := Fintype.card V * tripW S ℓ

variable (V S ℓ) in
/-- The large constant standing for `+∞` on the darts that are not eligible. -/
def tripL : ℤ := 4 * tripB V S ℓ + tripW S ℓ + 1

variable (M k g) in
/-- The source of the move `j`. -/
def tripSrc (j : ℕ) : V := M.tail (g (j % k))

variable (M k g) in
/-- The target of the move `j`. -/
def tripDst (j : ℕ) : V := M.tail (g ((j + 1) % k))

variable (M k g S ℓ) in
open Classical in
/-- The weights of the values during the move `j`: `ℓ` on the darts of the piece leaving a
vertex reached from the target, `tripL` elsewhere. -/
noncomputable def tripWt (j : ℕ) (d : D) : ℤ :=
  if d ∈ S ∧ Reach (pieceGraph M S ℓ) (tripDst M k g j) (M.tail d) then ℓ d else tripL V S ℓ

lemma tripφ_of_mem {d : D} (hd : d ∈ S) : tripφ S ℓ d = ℓ d := by
  simp [tripφ, hd]

lemma tripφ_of_not_mem {d : D} (hd : d ∉ S) : tripφ S ℓ d = 0 := by
  simp [tripφ, hd]

lemma abs_le_tripW {d : D} (hd : d ∈ S) : |ℓ d| ≤ tripW S ℓ :=
  single_le_sum (f := fun d => |ℓ d|) (fun _ _ => abs_nonneg _) hd

lemma tripW_nonneg : 0 ≤ tripW S ℓ := sum_nonneg fun _ _ => abs_nonneg _

lemma abs_tripφ_le (d : D) : |tripφ S ℓ d| ≤ tripW S ℓ := by
  by_cases hd : d ∈ S
  · rw [tripφ_of_mem hd]; exact abs_le_tripW hd
  · rw [tripφ_of_not_mem hd, abs_zero]; exact tripW_nonneg

lemma tripL_gt {d : D} (hd : d ∈ S) : ℓ d + 4 * (Fintype.card V * tripW S ℓ) < tripL V S ℓ := by
  have := le_abs_self (ℓ d)
  have := abs_le_tripW (ℓ := ℓ) hd
  unfold tripL tripB
  omega

lemma tripWt_elig (j : ℕ) {d : D} (hd : d ∈ S)
    (hr : Reach (pieceGraph M S ℓ) (tripDst M k g j) (M.tail d)) : tripWt M k g S ℓ j d = ℓ d := by
  simp [tripWt, hd, hr]

lemma tripWt_inelig (j : ℕ) {d : D}
    (h : d ∈ S → ¬ Reach (pieceGraph M S ℓ) (tripDst M k g j) (M.tail d)) :
    tripL V S ℓ ≤ tripWt M k g S ℓ j d := by
  unfold tripWt
  split_ifs with h'
  · exact absurd h'.2 (h h'.1)
  · exact le_rfl

end Params

/-! ### The moves -/

section Moves

variable (H : Hyp M k g S ℓ)
include H

lemma _root_.PlanarFlow.MSSP.Hyp.two_le_k : 2 ≤ k := H.face.two_le

lemma _root_.PlanarFlow.MSSP.Hyp.mod_lt (j : ℕ) : j % k < k :=
  Nat.mod_lt _ (by have := H.two_le_k; omega)

lemma _root_.PlanarFlow.MSSP.Hyp.mod_ne (j : ℕ) : j % k ≠ (j + 1) % k := by
  have hk := H.two_le_k
  rw [← Nat.mod_add_mod j k 1]
  have := H.mod_lt j
  rcases Nat.lt_or_ge (j % k + 1) k with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [show j % k + 1 = k by omega, Nat.mod_self]; omega

lemma _root_.PlanarFlow.MSSP.Hyp.head_g (i : ℕ) (hi : i < k) :
    M.head (g i) = M.tail (g ((i + 1) % k)) := by
  rw [CombMap.head, ← M.tail_next, H.face.next i hi]

lemma _root_.PlanarFlow.MSSP.Hyp.g_not_mem (j : ℕ) : g (j % k) ∉ S := fun h =>
  H.noIn _ h ⟨(j % k + 1) % k, Nat.mod_lt _ (by have := H.two_le_k; omega),
    (H.head_g _ (H.mod_lt j)).symm⟩

lemma _root_.PlanarFlow.MSSP.Hyp.rev_g_not_mem (j : ℕ) : M.rev (g (j % k)) ∉ S := fun h =>
  H.noIn _ h ⟨j % k, H.mod_lt j, by rw [M.head_rev]⟩

lemma _root_.PlanarFlow.MSSP.Hyp.tripφ_g (j : ℕ) : tripφ S ℓ (g (j % k)) = 0 :=
  tripφ_of_not_mem (H.g_not_mem j)

lemma _root_.PlanarFlow.MSSP.Hyp.tripφ_rev_g (j : ℕ) : tripφ S ℓ (M.rev (g (j % k))) = 0 :=
  tripφ_of_not_mem (H.rev_g_not_mem j)

lemma _root_.PlanarFlow.MSSP.Hyp.head_g_mod (j : ℕ) : M.head (g (j % k)) = tripDst M k g j := by
  rw [H.head_g _ (H.mod_lt j), Nat.mod_add_mod]; rfl

/-- **The move `j` meets the hypotheses of a move.** -/
lemma _root_.PlanarFlow.MSSP.Hyp.tripMoveHyp (hR : SameReach M k g S ℓ) (j : ℕ) :
    MoveHyp (pieceGraph M S ℓ) (tripSrc M k g j) (tripDst M k g j) :=
  moveHyp_of_hyp H hR (H.mod_lt j) (H.mod_lt (j + 1)) (H.mod_ne j)

end Moves

/-! ### The specification of a trip -/

/-- The data of one move: trees, values, forests of the pivot loop, selected darts, and the
number of pivots. -/
structure MoveData (M : CombMap D V F) (S : Finset D) where
  /-- The trees. -/
  T : ℕ → DTree M.dual
  /-- The values on the darts. -/
  val : ℕ → D → ℤ
  /-- The forests of the pivot loop. -/
  P : ℕ → V → Option {d // d ∈ S}
  /-- The selected darts. -/
  d : ℕ → D
  /-- The number of pivots. -/
  m : ℕ

variable (M k g S ℓ) in
/-- **The specification of the move `j`**: a run on the data from the source to the target
(`DataRun`, with the weights `tripφ`, `tripWt j`, the bounds `tripB`, `tripL`), in which every
pivot gives the head of the selected dart that dart as its parent dart. -/
def MoveSpec (j : ℕ) (R : MoveData M S) : Prop :=
  DataRun S ℓ (tripSrc M k g j) (tripDst M k g j) (tripφ S ℓ) (tripWt M k g S ℓ j) (g (j % k))
      (tripB V S ℓ) (tripL V S ℓ) R.T R.val R.P R.d R.m ∧
    ∀ i < R.m, (R.T (i + 1)).root = (R.T i).root ∧
      (R.T (i + 1)).par = Function.update (R.T i).par (M.head (R.d i)) (R.d i)

variable (M k g S ℓ) in
/-- **The specification of a trip around the face**: every move meets `MoveSpec`, and the tree
at the start of the move `j + 1` is the tree at the end of the move `j` re-rooted at the new
source, with the boundary dart `g ((j + 1) % k)` as the parent dart of the new target and the
reverse of `g (j % k)` as the parent dart of the old source (when the old source is not the new
target), every other parent dart unchanged. -/
structure IsTrip (R : ℕ → MoveData M S) : Prop where
  move : ∀ j, MoveSpec M k g S ℓ j (R j)
  root : ∀ j, ((R (j + 1)).T 0).root = tripDst M k g j
  par_dst : ∀ j, ((R (j + 1)).T 0).par (tripDst M k g (j + 1)) = g ((j + 1) % k)
  par_src : ∀ j, tripDst M k g (j + 1) ≠ tripSrc M k g j →
    ((R (j + 1)).T 0).par (tripSrc M k g j) = M.rev (g (j % k))
  par_other : ∀ j x, x ≠ tripSrc M k g j → x ≠ tripDst M k g (j + 1) →
    ((R (j + 1)).T 0).par x = ((R j).T (R j).m).par x

variable (M k g S ℓ) in
/-- The data at the start of the move `j`. -/
def StartOK (j : ℕ) (T : DTree M.dual) (val : D → ℤ) : Prop :=
  Compat T (tripSrc M k g j) (tripDst M k g j) (g (j % k))
      (tpar (pieceGraph M S ℓ) (tripSrc M k g j)) ∧
    VInv T (tripφ S ℓ) (tripWt M k g S ℓ j) val

section Exists

variable (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ)
include H hR

omit hR in
/-- The forest at the end of a run is the shortest-path tree of the target. -/
lemma end_tpar {j : ℕ} {R : MoveData M S} (hR' : SameReach M k g S ℓ)
    (h : MoveSpec M k g S ℓ j R) :
    R.P R.m = tpar (pieceGraph M S ℓ) (tripDst M k g j) := by
  by_cases hS : S.Nonempty
  · have hrun := dataRun_isRun H.plane (H.tripMoveHyp hR' j) H.uniq (H.g_not_mem j)
      (H.rev_g_not_mem j) (fun d hd => tripφ_of_mem hd) (fun d hd hr => tripWt_elig j hd hr)
      (fun d hd => tripWt_inelig j hd) (fun d hd => tripL_gt hd) h.1 ⟨_, hS.choose_spec⟩
    exact (run_spec (H.tripMoveHyp hR' j) H.uniq hrun).2.2.1
  · funext x
    rcases h1 : R.P R.m x with _ | ⟨a, ha⟩
    · rcases h2 : tpar (pieceGraph M S ℓ) (tripDst M k g j) x with _ | ⟨b, hb⟩
      · rfl
      · exact absurd ⟨b, hb⟩ hS
    · exact absurd ⟨a, ha⟩ hS

/-- **A move from data at its start**: a run meeting `MoveSpec`. -/
lemma exists_move {j : ℕ} {T₀ : DTree M.dual} {val₀ : D → ℤ} (hs : StartOK M k g S ℓ j T₀ val₀) :
    ∃ R : MoveData M S, R.T 0 = T₀ ∧ R.val 0 = val₀ ∧ MoveSpec M k g S ℓ j R := by
  obtain ⟨T, val, P, d, m, h0, hv0, hd, hst⟩ := exists_dataRun_from H.plane
    (H.tripMoveHyp hR j) H.uniq (H.g_not_mem j) (H.rev_g_not_mem j)
    (fun d hd => tripφ_of_mem hd) (W := tripW S ℓ) abs_tripφ_le
    (fun d hd hr => tripWt_elig j hd hr) (fun d hd => tripWt_inelig j hd)
    (fun d hd => tripL_gt hd) hs.1 hs.2
  exact ⟨⟨T, val, P, d, m⟩, h0, hv0, hd, hst⟩

/-- **From the end of the move `j` to the start of the move `j + 1`** (`next_move`, and the change
of the weights of the values on the darts leaving the two roots). -/
lemma exists_next {j : ℕ} {R : MoveData M S} (h : MoveSpec M k g S ℓ j R) :
    ∃ (T' : DTree M.dual) (val' : D → ℤ), StartOK M k g S ℓ (j + 1) T' val' ∧
      T'.root = tripDst M k g j ∧ T'.par (tripDst M k g (j + 1)) = g ((j + 1) % k) ∧
      (tripDst M k g (j + 1) ≠ tripSrc M k g j → T'.par (tripSrc M k g j) = M.rev (g (j % k))) ∧
      ∀ x, x ≠ tripSrc M k g j → x ≠ tripDst M k g (j + 1) → T'.par x = (R.T R.m).par x := by
  have hC := h.1.compat R.m le_rfl
  rw [end_tpar H hR h] at hC
  have hV := h.1.vinv R.m le_rfl
  have hk := H.two_le_k
  have e1 : (j + 1 + 1) % k = ((j + 1) % k + 1) % k := (Nat.mod_add_mod _ _ _).symm
  have hwv : tripDst M k g (j + 1) ≠ tripDst M k g j := by
    intro h'
    exact H.mod_ne (j + 1) (H.face.inj _ (H.mod_lt (j + 1 + 1)) _ (H.mod_lt (j + 1)) h').symm
  have hvu : tripDst M k g j ≠ tripSrc M k g j := fun h' =>
    H.mod_ne j (H.face.inj _ (H.mod_lt j) _ (H.mod_lt (j + 1)) h'.symm)
  obtain ⟨T', val', hr, hpw, hpu, hpx, hV'⟩ := next_move H.plane hC.root hC.par_v hC.tail hvu
    (H.tripφ_g j) (H.tripφ_rev_g j) hV (e' := g ((j + 1) % k)) rfl
    (by rw [H.head_g _ (H.mod_lt _)]; unfold tripDst; rw [e1]) hwv
  refine ⟨T', fun d => val' d + tripWt M k g S ℓ (j + 1) d - tripWt M k g S ℓ j d,
    ⟨⟨hr, hpw, rfl, fun x a hx => ?_⟩, fun d hd => ?_⟩, hr, hpw, hpu, hpx⟩
  · obtain ⟨-, hd, -⟩ := tpar_spec hx
    have hnr : ∀ i < k, x ≠ M.tail (g i) := fun i hi h' =>
      H.noIn a.1 a.2 ⟨i, hi, by rw [← h', ← hd]; rfl⟩
    rw [hpx x (hnr _ (H.mod_lt j)) (hnr _ (H.mod_lt (j + 1 + 1)))]
    exact hC.par x a hx
  · show val' d + _ - _ = _
    rw [hV' d hd]; ring

/-- The initial data of the trip. -/
lemma exists_start0 : ∃ (T : DTree M.dual) (val : D → ℤ), StartOK M k g S ℓ 0 T val := by
  obtain ⟨T, val, hC, hV⟩ := exists_init_data (φ := tripφ S ℓ) (wt := tripWt M k g S ℓ 0)
    H.plane (H.tripMoveHyp hR 0) (rInv_init (H.tripMoveHyp hR 0)) (e := g (0 % k)) rfl
    (H.head_g_mod 0)
  exact ⟨T, val, hC, hV⟩

/-- The data at the start of every move, chained. -/
noncomputable def tripStart : (j : ℕ) → {p : DTree M.dual × (D → ℤ) // StartOK M k g S ℓ j p.1 p.2}
  | 0 => ⟨((exists_start0 H hR).choose, (exists_start0 H hR).choose_spec.choose),
      (exists_start0 H hR).choose_spec.choose_spec⟩
  | j + 1 =>
    let s := tripStart j
    let hm := (exists_move H hR s.2).choose_spec
    ⟨((exists_next H hR hm.2.2).choose, (exists_next H hR hm.2.2).choose_spec.choose),
      (exists_next H hR hm.2.2).choose_spec.choose_spec.1⟩

/-- **The trip of Klein's algorithm on the data** (chosen; a description of the data, not an
implementation): the move `j` starts from `tripStart j`. -/
noncomputable def kleinTrip (j : ℕ) : MoveData M S :=
  (exists_move H hR (tripStart H hR j).2).choose

/-- **Trips exist**: `kleinTrip` is a trip. -/
theorem kleinTrip_isTrip : IsTrip M k g S ℓ (kleinTrip H hR) := by
  have hspec : ∀ j, (kleinTrip H hR j).T 0 = (tripStart H hR j).1.1 ∧
      (kleinTrip H hR j).val 0 = (tripStart H hR j).1.2 ∧
      MoveSpec M k g S ℓ j (kleinTrip H hR j) :=
    fun j => (exists_move H hR (tripStart H hR j).2).choose_spec
  have hnext : ∀ j, ∃ T' val', (tripStart H hR (j + 1)).1 = (T', val') ∧
      StartOK M k g S ℓ (j + 1) T' val' ∧
      T'.root = tripDst M k g j ∧ T'.par (tripDst M k g (j + 1)) = g ((j + 1) % k) ∧
      (tripDst M k g (j + 1) ≠ tripSrc M k g j →
        T'.par (tripSrc M k g j) = M.rev (g (j % k))) ∧
      ∀ x, x ≠ tripSrc M k g j → x ≠ tripDst M k g (j + 1) →
        T'.par x = ((kleinTrip H hR j).T (kleinTrip H hR j).m).par x := fun j =>
    ⟨_, _, rfl, (exists_next H hR (hspec j).2.2).choose_spec.choose_spec⟩
  refine ⟨fun j => (hspec j).2.2, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · obtain ⟨T', val', he, -, h, -⟩ := hnext j
    rw [(hspec (j + 1)).1, he]; exact h
  · obtain ⟨T', val', he, -, -, h, -⟩ := hnext j
    rw [(hspec (j + 1)).1, he]; exact h
  · obtain ⟨T', val', he, -, -, -, h, -⟩ := hnext j
    rw [(hspec (j + 1)).1, he]; exact h
  · obtain ⟨T', val', he, -, -, -, -, h⟩ := hnext j
    rw [(hspec (j + 1)).1, he]; exact h

/-- **Trips exist.** -/
theorem exists_trip : ∃ R : ℕ → MoveData M S, IsTrip M k g S ℓ R :=
  ⟨_, kleinTrip_isTrip H hR⟩

end Exists

/-! ### What a trip computes -/

section Spec

variable (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) {R : ℕ → MoveData M S}
include H hR

/-- **The labels at the start of every move are the distances from its source**: for every
vertex `x` reached from the source of the move `j`, the label `(T 0).psum tripφ x` of the tree at
the start of the move is the distance from the source to `x` in the piece. -/
theorem IsTrip.labels (hT : IsTrip M k g S ℓ R) (j : ℕ) {x : V}
    (hx : Reach (pieceGraph M S ℓ) (tripSrc M k g j) x) :
    ((R j).T 0).psum (tripφ S ℓ) x = dist (pieceGraph M S ℓ) (tripSrc M k g j) x := by
  have Hm := H.tripMoveHyp hR j
  have hd := (hT.move j).1
  have hC := hd.compat 0 (Nat.zero_le _)
  rw [hd.init] at hC
  have hI : RInv (pieceGraph M S ℓ) _ _ (tpar (pieceGraph M S ℓ) (tripSrc M k g j)) :=
    rInv_init Hm
  have hb : ∀ y, Hang (pieceGraph M S ℓ) (tpar (pieceGraph M S ℓ) (tripSrc M k g j))
      (tripDst M k g j) y → y = tripDst M k g j := by
    intro y h
    induction h with
    | root => rfl
    | step ha _ ih =>
      obtain ⟨⟨hz, -⟩, -, -⟩ := tpar_spec ha
      rw [ih] at hz
      exact absurd hz Hm.not_reach_uv
  have hxv : x ≠ tripDst M k g j := fun h => Hm.not_reach_uv (h ▸ hx)
  refine psum_red Hm hI hC (fun d hd => tripφ_of_mem hd) ?_ (fun h => hxv (hb x h))
  by_cases hxu : x = tripSrc M k g j
  · rw [hxu]; exact .root
  · rcases hI.forest Hm x (Hm.mem_moveSet.2 ⟨hxu, hxv, hx⟩) with h | h
    · exact h
    · exact absurd (hb x h) hxv

/-- **The trip makes at most `#S` pivots in total** over the `k` moves around the face. -/
theorem IsTrip.pivots (hT : IsTrip M k g S ℓ R) : ∑ j ∈ range k, (R j).m ≤ S.card := by
  by_cases hS : S.Nonempty
  · refine klein_run_pivots H hR (fun j => (R j).m) fun j hj => ?_
    have hjk : j % k = j := Nat.mod_eq_of_lt hj
    have hrun := dataRun_isRun H.plane (H.tripMoveHyp hR j) H.uniq (H.g_not_mem j)
      (H.rev_g_not_mem j) (fun d hd => tripφ_of_mem hd) (fun d hd hr => tripWt_elig j hd hr)
      (fun d hd => tripWt_inelig j hd) (fun d hd => tripL_gt hd) (hT.move j).1
      ⟨_, hS.choose_spec⟩
    unfold tripSrc tripDst at hrun
    rw [hjk] at hrun
    exact ⟨_, _, hrun⟩
  · -- no arc: no pivot
    have hm : ∀ j, (R j).m = 0 := fun j => by
      by_contra h0
      obtain ⟨h, -⟩ := (hT.move j).1.next 0 (by omega)
      exact hS ⟨_, h⟩
    simp [hm]

end Spec

end Klein

end PlanarFlow
