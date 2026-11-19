module

public import PlanarFlow.STFlow.TreePath
public import PlanarFlow.Plane.CoverPath
public import PlanarFlow.Klein.CutReach

/-!
# The cut of the cyclic cover: `K` sheets of the infinite cyclic cover as a plane map

For a simple path `π` from `s` to `t` with unit flow `P = pflow π`, the cyclic cover
`cover (pathCov hrot π) K` (`PlanarFlow/Plane/Cover.lean`) cut along the lift of `π`
(`liftPath`, deleting the darts `(d j, -1)` and `(rev (d j), 0)`) is the cut map of
`PlanarFlow/BKMNW/CutBuild.lean` (`cutMap`): a plane map whose piece is a copy of the dual of the
cover minus the lift of `π`, with a ring of roots, one for every dart leaving the lift of `π`.
Its piece is `K` consecutive sheets `0, …, K - 1` of the infinite cyclic cover of the dual: a dart
of the piece goes from the sheet `i` to the sheet `i + P d` **as integers** (`sheet_val`), since
the darts from the sheet `K - 1` to the sheet `0` are deleted.

* `val_add_int`, `sheet_val`: the integer sheets.
* `copyWalk`: a walk of the piece from a copy of a face uses only copies of darts of the cover;
  its darts project to a dual walk of `M` along which the sum of `P` is the change of sheet
  (`copyWalk_proj`).
* `rootWalk`: a walk of the piece from a root starts with its pendant arc.
* `liftList`: the lift of a dual walk of `M` from a given sheet; `dWalk_liftList`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option quotPrecheck false

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW MSSP Klein

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

/-! ### Integer sheets -/

lemma val_add_int {K : ℕ} [NeZero K] (a : ZMod K) {n : ℤ} (h0 : 0 ≤ (a.val : ℤ) + n)
    (h1 : (a.val : ℤ) + n < K) : (((a + (n : ZMod K)) : ZMod K).val : ℤ) = a.val + n := by
  have e : a + (n : ZMod K) = (((a.val : ℤ) + n : ℤ) : ZMod K) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [e, ZMod.val_intCast, Int.emod_eq_of_lt h0 h1]

lemma val_lt_pred_of_ne {K : ℕ} [NeZero K] {a : ZMod K} (h : a ≠ -1) : a.val + 1 < K := by
  have := ZMod.val_lt a
  by_contra h'
  have hK : a.val + 1 = K := by omega
  apply h
  have : a + 1 = 0 := by
    rw [← ZMod.natCast_zmod_val a]
    exact_mod_cast (show ((a.val + 1 : ℕ) : ZMod K) = 0 by rw [hK, ZMod.natCast_self])
  linear_combination this

lemma one_le_val_of_ne {K : ℕ} [NeZero K] {a : ZMod K} (h : a ≠ 0) : 1 ≤ a.val := by
  by_contra h'
  exact h ((ZMod.val_eq_zero a).1 (by omega))

variable (hrot : M.RotTrans) (π : SPath M) (hk : 0 < π.k) (K : ℕ) [NeZero K]

local notation "𝓜" => cover (pathCov hrot π) K
local notation "𝓛" => (liftPath hrot π K hk).darts

/-- **The sheets of the cut are integers**: off the lift of `π`, the dart `(d, i)` goes from the
sheet `i` to the sheet `i + P d` with `0 ≤ i + P d < K`. -/
lemma sheet_val {x : D × ZMod K} (hx : x ∉ 𝓛) :
    (((x.2 + (pflow π x.1 : ZMod K)) : ZMod K).val : ℤ) = x.2.val + pflow π x.1 := by
  have hlt := ZMod.val_lt x.2
  by_cases hd : x.1 ∈ π.darts
  · obtain ⟨j, hj, h | h⟩ := π.mem_darts.1 hd
    · rw [h, pflow_d π hj]
      have : x.2 ≠ -1 := fun e => hx ((mem_liftPath_darts hrot π K hk).2
        ⟨j, hj, Or.inl (Prod.ext h e)⟩)
      have := val_lt_pred_of_ne this
      exact val_add_int _ (by omega) (by omega)
    · rw [h, pflow_rev_d π hj]
      have : x.2 ≠ 0 := fun e => hx ((mem_liftPath_darts hrot π K hk).2
        ⟨j, hj, Or.inr (Prod.ext h e)⟩)
      have := one_le_val_of_ne this
      exact val_add_int _ (by omega) (by omega)
  · rw [pflow_of_not_mem π hd]; simp

/-! ### Walks in the cut -/

variable (ℓ' : CutD (cover (pathCov hrot π) K) (liftPath hrot π K hk).darts → ℤ)

local notation "𝒢" =>
  pieceGraph (cutMap (liftPath hrot π K hk).rev_mem_darts') (cutPiece 𝓜 𝓛) ℓ'

/-- The dart of the cover below an arc of the cut (for a copy, the dart it copies). -/
def arcProj : CutD 𝓜 𝓛 → D × ZMod K
  | .inl e => e.1
  | .inr (.inl t) => t.1
  | .inr (.inr (.inl t)) => t.1
  | .inr (.inr (.inr (.inl t))) => t.1
  | .inr (.inr (.inr (.inr t))) => t.1

/-- The copy of a dart of the cover off the lift of `π`. -/
def copyA {x : D × ZMod K} (hx : x ∉ 𝓛) : {d // d ∈ cutPiece 𝓜 𝓛} :=
  ⟨.inl ⟨x, hx⟩, by simp [mem_cutPiece, inPiece]⟩

lemma copyA_src {x : D × ZMod K} (hx : x ∉ 𝓛) :
    (𝒢).src (copyA hrot π hk K hx) = .inl (M.face x.1, x.2) := rfl

lemma copyA_dst {x : D × ZMod K} (hx : x ∉ 𝓛) :
    (𝒢).dst (copyA hrot π hk K hx) =
      .inl (M.face (M.rev x.1), x.2 + (pflow π x.1 : ZMod K)) := rfl

/-- **A walk of the cut from a copy of a face uses only copies of darts**, and their darts form a
dual walk of the cover. -/
lemma copyWalk {y : F × ZMod K} {z : CutV 𝓜 𝓛} {l : List {d // d ∈ cutPiece 𝓜 𝓛}}
    (h : LWalk 𝒢 (.inl y) z l) :
    (∀ a ∈ l, ∃ x hx, a = copyA hrot π hk K (x := x) hx) ∧
      ∃ z', z = .inl z' ∧ DWalk 𝓜 y (l.map fun a => arcProj hrot π hk K a.1) z' := by
  induction l generalizing y with
  | nil =>
    obtain rfl := LWalk.nil_iff.1 h
    exact ⟨by simp, y, rfl, rfl⟩
  | cons a l ih =>
    obtain ⟨hsrc, hl⟩ := LWalk.cons_iff.1 h
    obtain ⟨d, hd⟩ := a
    rcases d with ⟨x, hx⟩ | t | t | t | t <;> simp [mem_cutPiece, inPiece] at hd
    · have hy : (M.face x.1, x.2) = y := by
        simpa [pieceGraph, cutMap, cutTail] using hsrc
      obtain ⟨h1, z', rfl, h2⟩ := ih hl
      refine ⟨fun a ha => ?_, z', rfl, ?_⟩
      · rcases List.mem_cons.1 ha with rfl | ha
        · exact ⟨x, hx, rfl⟩
        · exact h1 a ha
      · exact ⟨hy, h2⟩
    · exact absurd hsrc (by simp [pieceGraph, cutMap, cutTail])

/-- **A walk of the cut from a root to a copy of a face starts with the pendant arc.** -/
lemma rootWalk {t : CutT 𝓜 𝓛} {z : F × ZMod K} {l : List {d // d ∈ cutPiece 𝓜 𝓛}}
    (h : LWalk 𝒢 (.inr t) (.inl z) l) :
    ∃ l', l = ⟨.inr (.inl t), by simp [mem_cutPiece, inPiece]⟩ :: l' ∧
      LWalk 𝒢 (.inl (M.face t.1.1, t.1.2)) (.inl z) l' := by
  rcases l with _ | ⟨a, l⟩
  · exact absurd (LWalk.nil_iff.1 h) (by simp)
  obtain ⟨hsrc, hl⟩ := LWalk.cons_iff.1 h
  obtain ⟨d, hd⟩ := a
  rcases d with ⟨x, hx⟩ | t' | t' | t' | t' <;> simp [mem_cutPiece, inPiece] at hd
  · exact absurd hsrc (by simp [pieceGraph, cutMap, cutTail])
  · have : t' = t := by simpa [pieceGraph, cutMap, cutTail] using hsrc
    subst this
    exact ⟨l, rfl, hl⟩

/-! ### Projecting and lifting walks -/

/-- A dual walk of the cover projects to a dual walk of `M`. -/
lemma dWalk_proj {y z : F × ZMod K} {l : List (D × ZMod K)} (h : DWalk 𝓜 y l z) :
    DWalk M y.1 (l.map Prod.fst) z.1 := by
  induction l generalizing y with
  | nil => obtain rfl := dWalk_nil.1 h; exact rfl
  | cons x l ih =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ih h2⟩
    have := congrArg Prod.fst h1
    exact this

/-- **Off the lift of `π`, the sum of `P` along a dual walk of the cover is the change of
sheet.** -/
lemma dWalk_sheet {y z : F × ZMod K} {l : List (D × ZMod K)} (h : DWalk 𝓜 y l z)
    (hl : ∀ x ∈ l, x ∉ 𝓛) : (z.2.val : ℤ) = y.2.val + dsum (pflow π) (l.map Prod.fst) := by
  induction l generalizing y with
  | nil => obtain rfl := dWalk_nil.1 h; simp
  | cons x l ih =>
    obtain ⟨h1, h2⟩ := h
    have hx := hl x (by simp)
    rw [ih h2 (fun x' hx' => hl x' (List.mem_cons_of_mem _ hx'))]
    have e1 : ((𝓜).dualGraph fun _ => 0).dst x = (M.face (M.rev x.1),
        x.2 + (pflow π x.1 : ZMod K)) := rfl
    have e2 : x.2 = y.2 := congrArg Prod.snd h1
    rw [e1]
    simp only [List.map_cons, dsum_cons]
    rw [sheet_val hrot π hk K hx, e2]
    ring

/-- The lift of a list of darts of `M` from the sheet `σ`. -/
def liftList : ZMod K → List D → List (D × ZMod K)
  | _, [] => []
  | σ, d :: l => (d, σ) :: liftList (σ + (pflow π d : ZMod K)) l

lemma liftList_append (σ : ZMod K) (l l' : List D) :
    liftList π K σ (l ++ l') =
      liftList π K σ l ++ liftList π K (σ + (dsum (pflow π) l : ZMod K)) l' := by
  induction l generalizing σ with
  | nil => simp [liftList]
  | cons d l ih =>
    simp only [List.cons_append, liftList, ih, dsum_cons]
    congr 3
    push_cast; ring

lemma map_fst_liftList (σ : ZMod K) (l : List D) : (liftList π K σ l).map Prod.fst = l := by
  induction l generalizing σ with
  | nil => rfl
  | cons d l ih => simp [liftList, ih]

/-- **Dual walks of `M` lift to dual walks of the cover.** -/
lemma dWalk_liftList {x y : F} {l : List D} (h : DWalk M x l y) (σ : ZMod K) :
    DWalk 𝓜 (x, σ) (liftList π K σ l) (y, σ + (dsum (pflow π) l : ZMod K)) := by
  induction l generalizing x σ with
  | nil => obtain rfl := dWalk_nil.1 h; simp [liftList]; rfl
  | cons d l ih =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨show ((M.face d, σ) : F × ZMod K) = (x, σ) by rw [← h1]; rfl, ?_⟩
    have := ih h2 (σ + (pflow π d : ZMod K))
    simp only [dsum_cons]
    push_cast at this ⊢
    rw [show σ + ((pflow π d : ℤ) + (dsum (pflow π) l : ℤ) : ZMod K) =
      σ + (pflow π d : ZMod K) + (dsum (pflow π) l : ZMod K) by ring]
    exact this

/-- **A dual walk of the cover is the lift of its projection** from its first sheet. -/
lemma eq_liftList {y z : F × ZMod K} {l : List (D × ZMod K)} (h : DWalk 𝓜 y l z) :
    l = liftList π K y.2 (l.map Prod.fst) := by
  induction l generalizing y with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨h1, h2⟩ := h
    have e : x.2 = y.2 := congrArg Prod.snd h1
    simp only [List.map_cons, liftList]
    have h3 := ih h2
    have e2 : ((𝓜).dualGraph fun _ => 0).dst x = (M.face (M.rev x.1),
        x.2 + (pflow π x.1 : ZMod K)) := rfl
    rw [e2, e] at h3
    rw [← h3]
    congr 1
    exact Prod.ext rfl e

end STFlow

end PlanarFlow
