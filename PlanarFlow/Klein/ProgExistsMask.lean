module

public import PlanarFlow.Klein.ProgExists
public import PlanarFlow.Klein.ProgTripMask

/-!
# Klein's algorithm with the masked queries: the preconditions can be met, and the cuts

* `kleinM_exec_exists`: **for every map, boundary, piece and lengths meeting the hypotheses of
  the trip, `t` targets (none of them a root) and flags `fl` of the moves**, there are an input
  and a starting configuration (those of `klein_exec_pre`, with a larger word bound and the
  flags written into the natural memory) from which `kleinProgM` runs within
  `36500000 (N lg N + f t lg N)` steps, `f = kRank fl k` the number of flagged moves, ending
  with the answers of the flagged moves in its output.
* `cutFlag`: on a cut of the dual graph minus `L` (`PlanarFlow.BKMNW.Cut`), the move flagged
  for each face `x` along `L` is the first move `Nat.find` whose root stands for `x` (the move
  read by `msspCutK`); `kRank_cutFlag_le`: there are at most `#(faces of L)` flagged moves.
* `msspCutK_eq_outM`: **the answers of `msspPlaneK` on the chosen cut are read from the output
  of the masked program**: from a face `x` along `L`, at the copy of a face `y` as the target
  `X i`, the answer is `kOutM` in the slot `kRank fl j` of the flagged move `j` of `x`.
* `msspPlaneK_masked`: **for the cut along a simple path `P` of `p` darts in a plane map with
  `N = #V + #F + #D`, the masked program on the chosen cut, with one flagged move per face along
  the path and the faces along the path as targets, runs within
  `1642500000 (N lg N + p² lg N)` steps** (the form `K (m lg m + k² lg m)` of
  `PlanarFlow.BKMNW.SubCosts.Bounds.mssp`, with `k` the length of the path) **and its output
  holds `msspPlaneK` at every pair of faces along the path.** The unmasked program `kleinProg`
  on the same cut answers all its roots, one per dart leaving the path, which can be of the
  order of `N` of them, at `O(N log N + N p log N)` steps.

Computing the flags (one pass over the `k` roots, marking the first root of each face) is an
`O(k)` precondition, like the other preconditions of `klein_exec`, not counted here.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-! ### The preconditions of the masked program can be met -/

/-- The natural memory of `c` with the flags of the `k` moves at `aMK n`. -/
def withFlags (n k : ℕ) (fl : ℕ → Bool) (c : Config) : Config :=
  { c with nmem := fun a => if n ≤ a ∧ a < n + k then (if fl (a - n) then 1 else 0)
      else c.nmem a }

lemma withFlags_wb {W n k : ℕ} {fl : ℕ → Bool} {c : Config} (hc : WordsBounded W c)
    (hW : 1 ≤ W) : WordsBounded W (withFlags n k fl c) := by
  refine ⟨hc.1, fun a => ?_⟩
  simp only [withFlags]
  split_ifs
  · exact hW
  · exact Nat.zero_le _
  · exact hc.2 a

lemma withFlags_mk {n k : ℕ} {fl : ℕ → Bool} {c : Config} {j : ℕ} (hj : j < k) :
    (withFlags n k fl c).nmem (aMK n + j) = if fl j then 1 else 0 := by
  have h : n ≤ n + j ∧ n + j < n + k := ⟨by omega, by omega⟩
  simp only [withFlags, aMK, h, and_self, ↓reduceIte, Nat.add_sub_cancel_left]

variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

local notation "𝒢" => pieceGraph M S ℓ

/-- **Klein's algorithm with the masked queries on the machine, end to end** (`kleinM_exec`
with the preconditions of `klein_exec_pre`, the word bound raised by `k` and the flags written
into the natural memory): for every map, boundary, piece and lengths meeting the hypotheses of
the trip, `t` targets `X i` (none of them a root) and flags `fl` of the moves, with
`N = #V + #F + #D`, there are an input and a starting configuration from which `kleinProgM`
runs within `36500000 (N lg N + f t lg N)` steps (`f = kRank fl k`), makes the `k` moves of a
trip, prints nothing and ends with the answers of the flagged moves in its output: `kOutM` in
the slot `kRank fl j` of a flagged move `j` is the distance in the piece from `tail (g j)` to
`X i`, none when `X i` is not reached (`odist`). -/
theorem kleinM_exec_exists (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (t : ℕ) (X : ℕ → V)
    (hX : ∀ i < t, ¬ IsRoot M k g (X i)) (fl : ℕ → Bool) :
    ∃ (n B : ℕ) (P : Input) (c₀ c' : Config) (steps : ℕ),
      n = 2 * (Fintype.card V + Fintype.card F + Fintype.card D) ∧
      Exec P (B + 16 * (n + 1)) (kleinProgM B (Fintype.card D) n k t) c₀ c' steps ∧
      steps ≤ 36500000 * ((Fintype.card V + Fintype.card F + Fintype.card D) *
          BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D) +
        kRank fl k * t * BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D)) ∧
      (∃ R : ℕ → MoveData M S, IsTripUpTo M k g S ℓ k R) ∧
      (∀ j < k, fl j = true → ∀ i < t, kOutM (Fintype.card D) n k t c' (kRank fl j) i =
        (odist 𝒢 (tripSrc M k g j) (X i)).map ((↑) : ℤ → ℝ)) ∧
      c'.output = c₀.output := by
  obtain ⟨n, ιv, ιg, ιf, ιe, σ, P, B, T, C, vs, ts, fs, cs, c₀, hn, hWa, hB, hOUT, hRB, hP, hL,
    hK, hG, hO, hXT, hI, hoff, hCr, hT, hc₀, hwt, hph, htl, hth, hh0, -⟩ :=
    klein_exec_pre H hR t X hX
  have hf : kRank fl k * t ≤ k * t := Nat.mul_le_mul_right _ (kRank_le fl k)
  have hc₀' : WordsBounded (B + k + 16 * (n + 1)) (withFlags n k fl c₀) :=
    withFlags_wb ⟨fun r => (hc₀.1 r).trans (by omega), fun a => (hc₀.2 a).trans (by omega)⟩
      (by omega)
  obtain ⟨c', steps, e, hsteps, htrip, hd, hout⟩ := kleinM_exec (B := B + k) (fl := fl)
    (by omega) (by omega) (by omega) (by unfold aRBM; unfold aRB at hRB; omega)
    (fun i => (hP i).trans (by omega)) H hR hL hK hG hO hXT hI hoff hCr hT hc₀' hwt hph htl hth
    hh0 (fun j hj => withFlags_mk hj)
  refine ⟨n, B + k, P, withFlags n k fl c₀, c', steps, hn, e, hsteps.trans ?_, htrip, hd, hout⟩
  have hk := H.k_le_card
  have h2 := H.face.two_le
  have hS : S.card ≤ Fintype.card D := card_le_univ S
  rw [hn]
  exact kleinM_steps_le (by omega) hS hk

/-! ### The flagged moves on a cut -/

section Cuts

variable {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
  [Fintype F'] [DecidableEq F']
variable {ℓ : D → ℤ} {L : List D}

open Classical in
/-- **The flagged moves on a cut**: the move `j` is flagged when it is the first move whose root
stands for some face `x` along `L` (the move from which `msspCutK` answers the queries from
`x`). -/
def cutFlag (C : Cut M ℓ L D' V' F') (j : ℕ) : Bool :=
  decide (∃ x ∈ (L.map M.face).toFinset, ∃ h : ∃ j', j' < C.k ∧ C.root j' = x, Nat.find h = j)

lemma cutFlag_find (C : Cut M ℓ L D' V' F') {x : F} (hxL : x ∈ (L.map M.face).toFinset)
    (hx : ∃ j, j < C.k ∧ C.root j = x) : cutFlag C (Nat.find hx) = true := by
  classical
  unfold cutFlag
  exact decide_eq_true ⟨x, hxL, hx, rfl⟩

/-- **At most one flagged move per face along `L`.** -/
lemma kRank_cutFlag_le (C : Cut M ℓ L D' V' F') (J : ℕ) :
    kRank (cutFlag C) J ≤ (L.map M.face).toFinset.card := by
  classical
  unfold kRank
  refine le_trans (card_le_card ?_) (card_image_le (s := (L.map M.face).toFinset)
    (f := fun x => if h : ∃ j', j' < C.k ∧ C.root j' = x then Nat.find h else 0))
  intro j hj
  rw [mem_filter] at hj
  have h := hj.2
  unfold cutFlag at h
  obtain ⟨x, hxL, hx, hj'⟩ := of_decide_eq_true h
  exact mem_image.2 ⟨x, hxL, by simp only [hx, ↓reduceDIte, hj']⟩

/-- **The answers of `msspPlaneK` on the chosen cut are read from the output of the masked
program**: for an output meeting the conclusion of `kleinM_exec` on that cut (with the perturbed
lengths), flags under which the move `Nat.find hx` of the face `x` is flagged (as `cutFlag`
does), and a target `X i` the copy of the face `y`, the answer from `x` at `y` is the answer in
the slot `kRank fl (Nat.find hx)` at `X i`, its integer part divided by `2^|D'|` (`outNN`). -/
theorem msspCutK_eq_outM
    (h : ∃ C : BKMNW.Cut M ℓ L D' V' F', SameReach C.map C.k C.g C.piece (pert C.len))
    {x : F} (hx : ∃ j, j < h.choose.k ∧ h.choose.root j = x) (y : F) {t : ℕ} {X : ℕ → V'}
    {fl : ℕ → Bool} {out : ℕ → ℕ → Option ℝ}
    (hd : ∀ j < h.choose.k, fl j = true → ∀ i < t, out (kRank fl j) i =
      (odist (pieceGraph h.choose.map h.choose.piece (pert h.choose.len))
        (tripSrc h.choose.map h.choose.k h.choose.g j) (X i)).map ((↑) : ℤ → ℝ))
    (hfl : fl (Nat.find hx) = true) {i : ℕ} (hi : i < t) (hXi : X i = h.choose.vx y) :
    msspCutK M D' V' F' L ℓ x y = outNN (Fintype.card D') (out (kRank fl (Nat.find hx)) i) := by
  rw [msspCutK_eq_ans h hx y, kleinAns_eq, ← hXi, hd _ (Nat.find_spec hx).1 hfl i hi]
  unfold outNN
  rw [Option.map_map]
  congr 1
  funext z
  simp

end Cuts

/-! ### The masked program on the cuts of the maximum-flow algorithm -/

section PathCut

variable {M : CombMap D V F}

/-- **The size of the cut along `L`**: its vertices, faces and darts are at most
`8 (#V + #F + #D) + 1`. -/
lemma card_cut_le (L : List D) :
    Fintype.card (CutV M L) + Fintype.card (CutF M L) + Fintype.card (CutD M L) ≤
      8 * (Fintype.card V + Fintype.card F + Fintype.card D) + 1 := by
  simp only [CutV, CutF, CutD, Fintype.card_sum, Fintype.card_unit]
  have h1 : Fintype.card (CutT M L) ≤ Fintype.card D := Fintype.card_subtype_le _
  have h2 : Fintype.card {e : D // e ∉ L} ≤ Fintype.card D := Fintype.card_subtype_le _
  have h3 : Fintype.card {v : V // v ∉ cutS M L} ≤ Fintype.card V := Fintype.card_subtype_le _
  omega

/-- A simple path of `p` darts has at most `2 p` faces along it. -/
lemma SPath.card_faces_le (P : SPath M) : P.faces.card ≤ 2 * P.k := by
  unfold SPath.faces
  refine (List.toFinset_card_le _).trans ?_
  rw [List.length_map, P.length_darts]

lemma lg_16_mul {N : ℕ} (hN : 1 ≤ N) : BKMNW.lg (16 * N) = BKMNW.lg N + 4 := by
  unfold BKMNW.lg
  have e : 16 * N = N * 2 * 2 * 2 * 2 := by ring
  rw [e, Nat.log_mul_base (by norm_num) (by omega), Nat.log_mul_base (by norm_num) (by omega),
    Nat.log_mul_base (by norm_num) (by omega), Nat.log_mul_base (by norm_num) (by omega)]

/-- **Multiple-source shortest paths in the dual graph minus a simple path by the masked
program, within the allowance of the maximum-flow algorithm**: for a plane map with transitive
rotations and faces, `N = #V + #F + #D`, a simple path `P` of `p ≥ 1` darts and lengths
nonnegative off the path, there are an input, a starting configuration, flags of the moves of
the chosen cut of `msspPlaneK` (at most `2 p` flagged moves: the first move of each face along
the path, `cutFlag`) and a slot for each face, such that `kleinProgM` on that cut, with the
`#(faces of P) ≤ 2 p` faces along the path as targets (`P.faces.toList`), runs within
`1642500000 (N lg N + p² lg N)` steps and ends with **`msspPlaneK` at every pair of faces along
the path in its output**: from `x` at `y`, the answer `kOutM` in the slot of `x` at the index
of `y`, its integer part divided by `2^|D'|` (`outNN`), `D'` the darts of the cut. -/
theorem msspPlaneK_masked (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (P : SPath M) (ℓ : D → ℤ) (hnn : ∀ e, e ∉ P.darts → 0 ≤ ℓ e) (hk : 0 < P.k) :
    ∃ (n B kk : ℕ) (Pin : Input) (c₀ c' : Config) (steps : ℕ) (fl : ℕ → Bool)
      (slot : F → ℕ),
      Exec Pin (B + 16 * (n + 1))
        (kleinProgM B (Fintype.card (CutD M P.darts)) n kk P.faces.card) c₀ c' steps ∧
      kRank fl kk ≤ 2 * P.k ∧
      steps ≤ 1642500000 * ((Fintype.card V + Fintype.card F + Fintype.card D) *
          BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D) +
        P.k ^ 2 * BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D)) ∧
      (∀ x ∈ P.faces, ∀ y ∈ P.faces, msspPlaneK M P.darts ℓ x y =
        outNN (Fintype.card (CutD M P.darts))
          (kOutM (Fintype.card (CutD M P.darts)) n kk P.faces.card c' (slot x)
            (P.faces.toList.idxOf y))) ∧
      c'.output = c₀.output := by
  classical
  obtain ⟨C, -, hRe⟩ := cut_hyp_sameReach hM hrot hface P ℓ hnn hk
  have h : ∃ C : Cut M ℓ P.darts (CutD M P.darts) (CutV M P.darts) (CutF M P.darts),
      SameReach C.map C.k C.g C.piece (pert C.len) := ⟨C, hRe⟩
  set C' := h.choose with hC'
  set ys := P.faces.toList with hys
  have hyl : ys.length = P.faces.card := Finset.length_toList _
  set X : ℕ → CutV M P.darts := fun i => C'.vx (ys.getD i (M.face (P.d 0))) with hXdef
  have hX : ∀ i < ys.length, ¬ IsRoot C'.map C'.k C'.g (X i) :=
    fun i _ ⟨j, hj, he⟩ => C'.root_ne j hj _ he
  obtain ⟨n, B, Pin, c₀, c', steps, -, e, hsteps, -, hd, hout⟩ :=
    kleinM_exec_exists C'.hyp.hyp h.choose_spec ys.length X hX (cutFlag C')
  rw [hyl] at e hsteps hd
  have hf : kRank (cutFlag C') C'.k ≤ 2 * P.k :=
    (kRank_cutFlag_le C' C'.k).trans P.card_faces_le
  refine ⟨n, B, C'.k, Pin, c₀, c', steps, cutFlag C', fun x =>
    if hx : ∃ j, j < C'.k ∧ C'.root j = x then kRank (cutFlag C') (Nat.find hx) else 0, e, hf,
    hsteps.trans ?_, fun x hx y hy => ?_, hout⟩
  · -- the cost
    set N := Fintype.card V + Fintype.card F + Fintype.card D with hN
    set N' := Fintype.card (CutV M P.darts) + Fintype.card (CutF M P.darts) +
      Fintype.card (CutD M P.darts) with hN'
    have hN1 : 1 ≤ N := by
      have : 0 < Fintype.card D := Fintype.card_pos_iff.2 ⟨P.d 0⟩
      omega
    have hNN : N' ≤ 9 * N := by have := card_cut_le (M := M) P.darts; omega
    have hl : BKMNW.lg N' ≤ 5 * BKMNW.lg N := by
      have h1 := BKMNW.lg_mono (show N' ≤ 16 * N by omega)
      rw [lg_16_mul hN1] at h1
      have := BKMNW.one_le_lg N
      omega
    have ht : P.faces.card ≤ 2 * P.k := P.card_faces_le
    have hft : kRank (cutFlag C') C'.k * P.faces.card ≤ 4 * P.k ^ 2 := by
      have := Nat.mul_le_mul hf ht
      nlinarith
    have a1 : N' * BKMNW.lg N' ≤ 45 * (N * BKMNW.lg N) := by
      have := Nat.mul_le_mul hNN hl
      nlinarith
    have a2 : kRank (cutFlag C') C'.k * P.faces.card * BKMNW.lg N' ≤
        20 * (P.k ^ 2 * BKMNW.lg N) := by
      have := Nat.mul_le_mul hft hl
      nlinarith
    omega
  · -- the answers
    have hxL : x ∈ (P.darts.map M.face).toFinset := hx
    obtain ⟨j, hj, hjx⟩ := C'.srcs x hxL
    have hx' : ∃ j, j < C'.k ∧ C'.root j = x := ⟨j, hj, hjx⟩
    have hyl' : ys.idxOf y < ys.length := List.idxOf_lt_length_iff.2 (Finset.mem_toList.2 hy)
    have hXi : X (ys.idxOf y) = C'.vx y := by
      simp only [hXdef]
      rw [List.getD_eq_getElem?_getD, List.getElem?_idxOf (Finset.mem_toList.2 hy)]
      rfl
    simp only [hx', ↓reduceDIte]
    exact msspCutK_eq_outM h hx' y hd (cutFlag_find C' hxL hx') (by rw [← hyl]; exact hyl') hXi

end PathCut

end Klein

end PlanarFlow
