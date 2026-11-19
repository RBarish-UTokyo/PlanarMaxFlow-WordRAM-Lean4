module

public import PlanarFlow.BKMNW.MsRunD
public import PlanarFlow.BKMNW.MsCutJ
public import PlanarFlow.BKMNW.StTreeM
public import PlanarFlow.Klein.CutReach

/-!
# The Klein start of an MSSP call, part A: the map, the cut, the initial tree (math)

* **`enumOK_dual_of`**: for a plane map with transitive rotations, `EnumOK M en m` gives
  `EnumOK M.dual en m` (every vertex is the tail of a dart, `M.dual.FaceTrans = M.RotTrans`);
* **`Cut.remap`**: a cut with its map replaced by an equal map; **`ccut`**: the cut `fixCut` of the
  path with the map `(cutMap hL).dual.dual` (the map on which the encoders of the s-t flow work:
  `Q.dual` for `Q = (cutMap hL).dual`), `ccut_sameReach`;
* the walks of a piece with lengths `ℓ` and of all the darts with lengths `ℓD` (equal to `ℓ` on
  the piece, at least `H` elsewhere): `lift_walk`, `restrict_walk`, **`dist_eq_of_reach`**,
  **`reach_of_dist_lt`** — below `H` the two graphs have the same distances;
* **`ms_tree`**: Dijkstra's tight parents for `ℓD` (positive; `ℓD = H` on a dart `e₀` leaving the
  root `u`, `≥ 2H` on the other darts off the piece, no dart of the piece entering the head `v` of
  `e₀`) give a dual tree `T₀ : DTree Q` rooted at `u` whose parents are the words, and
  **`Klein.Compat (STFlow.toDD T₀) u v e₀ (Klein.tpar (pieceGraph Q.dual S ℓ) u)`** when the piece lengths have
  unique tight arcs and all piece distances are below `H` (Klein's `hT` of `KStart`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset Function MSSP NsStep

universe w

/-! ### `EnumOK` of the dual -/

theorem enumOK_dual_of {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {M : CombMap D V F} (hM : M.IsPlane) (hrot : M.RotTrans)
    {en : ℕ → D} {m : ℕ} (h : EnumOK M en m) (d₀ : D) : EnumOK M.dual en m where
  inj := h.inj
  surj := h.surj
  fsurj v := by
    induction hM.conn (M.tail d₀) v with
    | refl => exact ⟨d₀, rfl⟩
    | @tail b c _ hbc _ =>
      obtain ⟨d, -, hd⟩ := hbc
      exact ⟨M.rev d, hd⟩
  ft := hrot

/-! ### The cut on the map `(cutMap hL).dual.dual` -/

section Remap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {ℓ : D → ℤ} {L : List D}
variable {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
  [Fintype F'] [DecidableEq F']

/-- **A cut with its map replaced by an equal map.** -/
noncomputable def _root_.PlanarFlow.BKMNW.Cut.remap (C : Cut M ℓ L D' V' F') (N : CombMap D' V' F') (h : N = C.map) :
    Cut M ℓ L D' V' F' where
  map := N
  k := C.k
  g := C.g
  piece := C.piece
  len := C.len
  hyp := by subst h; exact C.hyp
  vx := C.vx
  vx_inj := C.vx_inj
  arc := C.arc
  tail_arc := by subst h; exact C.tail_arc
  head_arc := by subst h; exact C.head_arc
  len_arc := C.len_arc
  root := C.root
  root_ne := by subst h; exact C.root_ne
  pend := by subst h; exact C.pend
  cover := by subst h; exact C.cover
  srcs := C.srcs

end Remap

section CCut

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-- **The cut of an MSSP call**: `fixCut` with the map `(cutMap hL).dual.dual`. -/
noncomputable def ccut (hM : M.IsPlane) (hrot : M.RotTrans) (P : SPath M) (hk : 0 < P.k)
    (ℓ : D → ℤ) (hnn : ∀ e, e ∉ P.darts → 0 ≤ ℓ e) :
    Cut M ℓ P.darts (CutD M P.darts) (CutV M P.darts) (CutF M P.darts) :=
  (fixCut hM hrot P hk ℓ hnn).remap (cutMap P.rev_mem_darts').dual.dual (dual_dual' _)

variable (hM : M.IsPlane) (hrot : M.RotTrans) (P : SPath M) (hk : 0 < P.k) (ℓ : D → ℤ)
  (hnn : ∀ e, e ∉ P.darts → 0 ≤ ℓ e)

@[simp] lemma ccut_map : (ccut hM hrot P hk ℓ hnn).map = (cutMap P.rev_mem_darts').dual.dual :=
  rfl
@[simp] lemma ccut_k : (ccut hM hrot P hk ℓ hnn).k = fixPer M P :=
  fixCut_k hM hrot P hk ℓ hnn
@[simp] lemma ccut_g : (ccut hM hrot P hk ℓ hnn).g = cutG P.rev_mem_darts' (fixT0 P hk) := rfl
@[simp] lemma ccut_piece : (ccut hM hrot P hk ℓ hnn).piece = cutPiece M P.darts := rfl
@[simp] lemma ccut_len : (ccut hM hrot P hk ℓ hnn).len = cutLen M P.darts ℓ := rfl
@[simp] lemma ccut_vx : (ccut hM hrot P hk ℓ hnn).vx = Sum.inl := rfl
lemma ccut_root (j : ℕ) : (ccut hM hrot P hk ℓ hnn).root j = fixCorner M P j :=
  fixCut_root hM hrot P hk ℓ hnn j

/-- `SameReach` on the cut of the call (any lengths). -/
theorem ccut_sameReach (ℓ' : CutD M P.darts → ℤ) :
    Klein.SameReach (ccut hM hrot P hk ℓ hnn).map (ccut hM hrot P hk ℓ hnn).k
      (ccut hM hrot P hk ℓ hnn).g (ccut hM hrot P hk ℓ hnn).piece ℓ' := by
  have h := Klein.cutOf_sameReach P.rev_mem_darts' ℓ' (fixT0 P hk)
  have hk' : (ccut hM hrot P hk ℓ hnn).k = minimalPeriod (tourT P.rev_mem_darts') (fixT0 P hk) :=
    rfl
  rw [hk', ccut_map, dual_dual', ccut_g, ccut_piece]
  exact h

end CCut

/-! ### Walks below `H` -/

section Walks

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {N : CombMap D V F} {S : Finset D} {ℓ ℓD : D → ℤ} {H : ℤ}

/-- An arc of the piece as an arc of the graph of all the darts. -/
def upA (a : {d // d ∈ S}) : {d // d ∈ (univ : Finset D)} := ⟨a.1, mem_univ _⟩

lemma lift_walk (hS : ∀ d ∈ S, ℓD d = ℓ d) {x y : V} {l : List {d // d ∈ S}}
    (h : LWalk (pieceGraph N S ℓ) x y l) :
    LWalk (pieceGraph N univ ℓD) x y (l.map upA) ∧
      MSSP.wlen (pieceGraph N univ ℓD) (l.map upA) = MSSP.wlen (pieceGraph N S ℓ) l := by
  induction h with
  | nil x => exact ⟨.nil x, rfl⟩
  | @cons a y l h ih =>
    refine ⟨LWalk.cons (G := pieceGraph N univ ℓD) (a := upA a) ih.1, ?_⟩
    rw [List.map_cons, MSSP.wlen_cons, MSSP.wlen_cons, ih.2]
    show ℓD a.1 + _ = ℓ a.1 + _
    rw [hS a.1 a.2]

lemma restrict_walk (hnn : ∀ d, 0 ≤ ℓD d) (hS : ∀ d ∈ S, ℓD d = ℓ d)
    (hH : ∀ d ∉ S, H ≤ ℓD d) {x y : V} {l : List {d // d ∈ (univ : Finset D)}}
    (h : LWalk (pieceGraph N univ ℓD) x y l) (hl : MSSP.wlen (pieceGraph N univ ℓD) l < H) :
    ∃ l', LWalk (pieceGraph N S ℓ) x y l' ∧
      MSSP.wlen (pieceGraph N S ℓ) l' = MSSP.wlen (pieceGraph N univ ℓD) l := by
  induction h with
  | nil x => exact ⟨[], .nil x, rfl⟩
  | @cons a y l h ih =>
    rw [MSSP.wlen_cons] at hl
    have h0 := MSSP.wlen_nonneg (G := pieceGraph N univ ℓD) (fun b => hnn b.1) l
    have ha0 := hnn a.1
    change ℓD a.1 + _ < H at hl
    have ha : a.1 ∈ S := by
      by_contra hn
      have := hH a.1 hn
      omega
    obtain ⟨l', h', e'⟩ := ih (by omega)
    refine ⟨⟨a.1, ha⟩ :: l', LWalk.cons (G := pieceGraph N S ℓ) (a := ⟨a.1, ha⟩) h', ?_⟩
    rw [MSSP.wlen_cons, MSSP.wlen_cons, e']
    show ℓ a.1 + _ = ℓD a.1 + _
    rw [hS a.1 ha]

/-- **Below `H` the distances agree**: a vertex reached in the piece, at distance below `H`
there, is at the same distance with all the darts. -/
lemma dist_eq_of_reach (hnn : ∀ d, 0 ≤ ℓD d) (hS : ∀ d ∈ S, ℓD d = ℓ d)
    (hH : ∀ d ∉ S, H ≤ ℓD d) {u x : V} (h : Reach (pieceGraph N S ℓ) u x)
    (hlt : dist (pieceGraph N S ℓ) u x < H) :
    dist (pieceGraph N univ ℓD) u x = dist (pieceGraph N S ℓ) u x := by
  have hnn1 : ∀ a : {d // d ∈ S}, 0 ≤ (pieceGraph N S ℓ).len a := fun a => by
    show 0 ≤ ℓ a.1; rw [← hS a.1 a.2]; exact hnn a.1
  have hnn2 : ∀ a : {d // d ∈ (univ : Finset D)}, 0 ≤ (pieceGraph N univ ℓD).len a :=
    fun a => hnn a.1
  obtain ⟨l, hl, he⟩ := exists_walk_dist hnn1 h
  obtain ⟨h2, e2⟩ := lift_walk (N := N) hS hl
  have d1 := dist_le hnn2 h2
  obtain ⟨l₂, hl₂, he₂⟩ := exists_walk_dist hnn2 ⟨_, h2⟩
  obtain ⟨l', hl', e'⟩ := restrict_walk hnn hS hH hl₂ (by omega)
  have d2 := dist_le hnn1 hl'
  omega

/-- **A vertex at distance below `H` with all the darts is reached in the piece**, at the same
distance. -/
lemma reach_of_dist_lt (hnn : ∀ d, 0 ≤ ℓD d) (hS : ∀ d ∈ S, ℓD d = ℓ d)
    (hH : ∀ d ∉ S, H ≤ ℓD d) {u y : V} (h : Reach (pieceGraph N univ ℓD) u y)
    (hlt : dist (pieceGraph N univ ℓD) u y < H) :
    Reach (pieceGraph N S ℓ) u y ∧
      dist (pieceGraph N S ℓ) u y = dist (pieceGraph N univ ℓD) u y := by
  have hnn2 : ∀ a : {d // d ∈ (univ : Finset D)}, 0 ≤ (pieceGraph N univ ℓD).len a :=
    fun a => hnn a.1
  obtain ⟨l₂, hl₂, he₂⟩ := exists_walk_dist hnn2 h
  obtain ⟨l', hl', e'⟩ := restrict_walk hnn hS hH hl₂ (by omega)
  have hnn1 : ∀ a : {d // d ∈ S}, 0 ≤ (pieceGraph N S ℓ).len a := fun a => by
    show 0 ≤ ℓ a.1; rw [← hS a.1 a.2]; exact hnn a.1
  have hR : Reach (pieceGraph N S ℓ) u y := ⟨l', hl'⟩
  have d1 := dist_le hnn1 hl'
  refine ⟨hR, ?_⟩
  have := dist_eq_of_reach hnn hS hH hR (by omega)
  omega

end Walks

/-! ### The initial tree of Klein's run -/

section Tree

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {Q : CombMap D V F} {S : Finset D} {ℓ ℓD : D → ℤ} {H : ℤ}

/-- **The initial tree of Klein's run from Dijkstra's tight parents** (see the module
docstring). -/
theorem ms_tree (hQ : Q.IsPlane) (hU : UniqTight (pieceGraph Q.dual S ℓ))
    (hpos : ∀ d, 0 < ℓD d) (hS : ∀ d ∈ S, ℓD d = ℓ d) (hH : ∀ d ∉ S, H ≤ ℓD d)
    (u : F) (hlt : ∀ x, Reach (pieceGraph Q.dual S ℓ) u x → dist (pieceGraph Q.dual S ℓ) u x < H)
    (e₀ : D) (he₀S : e₀ ∉ S) (hu : Q.face e₀ = u) (hv : Q.face (Q.rev e₀) ≠ u)
    (he₀ : ℓD e₀ = H) (hge : ∀ d, d ∉ S → d ≠ e₀ → 2 * H ≤ ℓD d) (hH0 : 0 < H)
    (hnoIn : ∀ d ∈ S, Q.face (Q.rev d) ≠ Q.face (Q.rev e₀))
    {nD : ℕ} (σ : D ≃ Fin nD) {ιF : F → ℕ} {mem : ℕ → ℕ} {Pb : ℕ}
    (hpar : ∀ x, x ≠ u → ∃ d, mem (Pb + ιF x) = σ d ∧ Q.face (Q.rev d) = x ∧
      dist (pieceGraph Q.dual univ ℓD) u (Q.face d) + ℓD d = dist (pieceGraph Q.dual univ ℓD) u x) :
    ∃ T₀ : STFlow.DTree Q, T₀.root = u ∧ (∀ x, x ≠ u → mem (Pb + ιF x) = σ (T₀.par x)) ∧
      Klein.Compat (STFlow.toDD T₀) u (Q.face (Q.rev e₀)) e₀ (Klein.tpar (pieceGraph Q.dual S ℓ) u) := by
  classical
  have hnn : ∀ d, 0 ≤ ℓD d := fun d => (hpos d).le
  have hnn2 : ∀ a, 0 ≤ (pieceGraph Q.dual univ ℓD).len a := fun a => hnn a.1
  let par : F → D := fun x => if h : x = u then e₀ else (hpar x h).choose
  have hspec : ∀ x (h : x ≠ u), mem (Pb + ιF x) = σ (par x) ∧ Q.face (Q.rev (par x)) = x ∧
      dist (pieceGraph Q.dual univ ℓD) u (Q.face (par x)) + ℓD (par x) = dist (pieceGraph Q.dual univ ℓD) u x := fun x h => by
    simp only [par, h, ↓reduceDIte]
    exact (hpar x h).choose_spec
  have hhp : ∀ x, x ≠ u → Q.face (Q.rev (par x)) = x := fun x h => (hspec x h).2.1
  have hdec : ∀ x, x ≠ u → dist (pieceGraph Q.dual univ ℓD) u (Q.face (par x)) < dist (pieceGraph Q.dual univ ℓD) u x :=
    fun x h => by have := (hspec x h).2.2; have := hpos (par x); omega
  refine ⟨STFlow.treeOf Q u par hhp (fun x => dist (pieceGraph Q.dual univ ℓD) u x) hdec, rfl,
    fun x h => (hspec x h).1, ?_⟩
  refine ⟨rfl, ?_, hu, ?_⟩
  · -- the parent of the head of `e₀` is `e₀`
    show par (Q.face (Q.rev e₀)) = e₀
    obtain ⟨-, -, ht⟩ := hspec _ hv
    by_contra hne
    have hR : Reach (pieceGraph Q.dual univ ℓD) u (Q.face e₀) := STFlow.reach_dual hQ ℓD u _
    have ha := dist_arc hnn2 (G := pieceGraph Q.dual univ ℓD) (a := ⟨e₀, mem_univ _⟩) hR
    simp only [STFlow.dG_src, STFlow.dG_dst, STFlow.dG_len] at ha
    rw [hu, dist_self hnn2] at ha
    have h0 := dist_nonneg hnn2 (STFlow.reach_dual hQ ℓD u (Q.face (par (Q.face (Q.rev e₀)))))
    by_cases hS' : par (Q.face (Q.rev e₀)) ∈ S
    · exact hnoIn _ hS' ((hspec _ hv).2.1)
    · have := hge _ hS' hne
      omega
  · -- the tight parents of the piece
    intro x a hxa
    obtain ⟨⟨hRa, hTa⟩, hdst, hxu⟩ := Klein.tpar_spec hxa
    show par x = a.1
    have hRx : Reach (pieceGraph Q.dual S ℓ) u x := hdst ▸ hRa.arc
    obtain ⟨-, hpx, htx⟩ := hspec x hxu
    have hlx := hlt x hRx
    have e2 := dist_eq_of_reach hnn hS hH hRx hlx
    have h0 := dist_nonneg hnn2 (STFlow.reach_dual hQ ℓD u (Q.face (par x)))
    have hpS : par x ∈ S := by
      by_contra hn
      have := hH _ hn
      have : dist (pieceGraph Q.dual univ ℓD) u x < H := by rw [show pieceGraph Q.dual univ ℓD = pieceGraph Q.dual univ ℓD from rfl, e2]; exact hlx
      omega
    obtain ⟨hR1, e1⟩ := reach_of_dist_lt hnn hS hH (STFlow.reach_dual hQ ℓD u (Q.face (par x)))
      (by
        have : dist (pieceGraph Q.dual univ ℓD) u x < H := by
          rw [show pieceGraph Q.dual univ ℓD = pieceGraph Q.dual univ ℓD from rfl, e2]; exact hlx
        have := hpos (par x)
        omega)
    have hT : MSSP.Tight (pieceGraph Q.dual S ℓ) u ⟨par x, hpS⟩ := by
      refine ⟨hR1, ?_⟩
      show dist (pieceGraph Q.dual S ℓ) u (Q.face (par x)) + ℓ (par x) =
        dist (pieceGraph Q.dual S ℓ) u (Q.face (Q.rev (par x)))
      rw [hpx, e1, ← hS _ hpS, ← e2]
      exact htx
    have := hU u ⟨par x, hpS⟩ a hT ⟨hRa, hTa⟩
      (by show Q.face (Q.rev (par x)) = _; rw [hpx, ← hdst])
      (by show Q.face (Q.rev (par x)) ≠ u; rw [hpx]; exact hxu)
    rw [← this]

end Tree

end MsEnc

end BKMNW

end PlanarFlow
