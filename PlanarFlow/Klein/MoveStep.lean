module

public import PlanarFlow.Klein.PivotOps

/-!
# One step of the pivot loop of a move

`move_stored` proves a move by induction on the number of red vertices, its list of operations
given by existence. A program runs the loop forwards; this file states one step of it.

* `move_step`: **one pivot of the loop**: on a dart of least value on the path of the cotree,
  below the threshold `L - 2B`, the dart is in the piece, its head is not the root nor above its
  tail, the dart is off the tree, and the reparented tree with the values `pivotVal` keeps the
  invariants (`RInv`, `Compat`, `VInv`); the number of red vertices drops, and the value of the
  dart is at most the drift bound `driftK` (the step inside `move_stored`).
* `selForest_update`, `selForest_succ`: the forests of the loop along the selected darts.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {S : Finset D} {ℓ : D → ℤ} {u v : V} {φ wt : D → ℤ} {e : D}

local notation "𝒢" => pieceGraph M S ℓ

lemma selForest_update (P₀ : V → Option {d // d ∈ S}) (d : ℕ → D) {i : ℕ} (x : D) :
    ∀ j ≤ i, selForest M S P₀ (Function.update d i x) j = selForest M S P₀ d j
  | 0, _ => rfl
  | j + 1, hj => by
    have h := selForest_update P₀ d (i := i) x j (by omega)
    have hne : j ≠ i := by omega
    simp only [selForest, Function.update_of_ne hne, h]

lemma selForest_succ (P₀ : V → Option {d // d ∈ S}) (d : ℕ → D) (i : ℕ) (h : d i ∈ S) :
    selForest M S P₀ d (i + 1) =
      Function.update (selForest M S P₀ d i) (M.head (d i)) (some ⟨d i, h⟩) := by
  simp only [selForest, dite_eq_left h]

/-- **One pivot of the loop of a move** (the step of `move_stored`). -/
theorem move_step (hM : M.IsPlane) (H : MoveHyp 𝒢 u v) (hU : UniqTight 𝒢)
    (heS : e ∉ S) (hrS : M.rev e ∉ S) (hφ : ∀ d ∈ S, φ d = ℓ d) {W L : ℤ}
    (hW : ∀ d, |φ d| ≤ W) (hwt : ∀ d ∈ S, Reach 𝒢 v (M.tail d) → wt d = ℓ d)
    (hwL : ∀ d, (d ∈ S → ¬ Reach 𝒢 v (M.tail d)) → L ≤ wt d)
    (hL : ∀ d ∈ S, ℓ d + 4 * (Fintype.card V * W) < L)
    {T₀ : DTree M.dual} {val₀ : D → ℤ} {P₀ : V → Option {d // d ∈ S}}
    (hI : RInv 𝒢 u v P₀) (hC : Compat T₀ u v e P₀) (hV : VInv T₀ φ wt val₀) {d₀ : D}
    (hd₀ : T₀.chi (M.face e) (M.face (M.rev e)) d₀ = 1)
    (hlt : val₀ d₀ < L - 2 * (Fintype.card V * W))
    (hmin : ∀ d', T₀.chi (M.face e) (M.face (M.rev e)) d' = 1 → val₀ d₀ ≤ val₀ d') :
    ∃ (h : d₀ ∈ S) (hy : M.head d₀ ≠ T₀.root) (hna : ¬ T₀.Anc (M.head d₀) (M.dual.face d₀)),
      ¬ T₀.InT d₀ ∧ RInv 𝒢 u v (Function.update P₀ (M.head d₀) (some ⟨d₀, h⟩)) ∧
      Compat (T₀.reparent (M.head d₀) d₀ hy (dual_face_rev d₀) hna) u v e
        (Function.update P₀ (M.head d₀) (some ⟨d₀, h⟩)) ∧
      VInv (T₀.reparent (M.head d₀) d₀ hy (dual_face_rev d₀) hna) φ wt
        (pivotVal T₀ φ wt val₀ (M.head d₀) (val₀ d₀)) ∧
      (redSet M S ℓ u v (Function.update P₀ (M.head d₀) (some ⟨d₀, h⟩))).card <
        (redSet M S ℓ u v P₀).card ∧
      |val₀ d₀| ≤ driftK L W (Fintype.card V) := by
  classical
  set B : ℤ := Fintype.card V * W with hBdef
  have hB : ∀ (T : DTree M.dual) x, |T.psum φ x| ≤ B := fun T x => abs_psum_le_mul T hW x
  have hnT : ¬ T₀.InT d₀ := fun h => by
    rw [(T₀.chi_spec hM.dual _ _).2.2.1 _ h] at hd₀; exact absurd hd₀ (by norm_num)
  have hel : d₀ ∈ S ∧ Reach 𝒢 v (M.tail d₀) := by
    by_contra hne
    have hw := hwL d₀ fun h1 h2 => hne ⟨h1, h2⟩
    have hB3 := abs_le.1 (hB T₀ (M.tail d₀))
    have hB4 := abs_le.1 (hB T₀ (M.head d₀))
    have hlt' := hlt
    rw [hV _ hnT] at hlt'
    omega
  have hact := (ractive_iff_chi hM H hI hC heS hrS ⟨d₀, hel.1⟩).2 ⟨hel.2, hd₀⟩
  obtain ⟨h, ha, hm, -⟩ := minpath_spec hM H hI hC heS hrS hφ hV (hB T₀) hwt hwL hL hd₀
    hmin ⟨_, hact.2.1, hact.2.2⟩
  obtain ⟨hy, hna, hI', hC', hV'⟩ := pivot_values hM H hU hI hC heS hrS hφ hV hwt ha hm
  have hst := RInv.step H hI hU ha hm
  have hred : (redSet M S ℓ u v (Function.update P₀ (M.head d₀) (some ⟨d₀, h⟩))).card <
      (redSet M S ℓ u v P₀).card := by
    refine card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
    · simp only [redSet, mem_filter] at hx ⊢
      exact ⟨hx.1, fun h' => hx.2 (hst.2.2.2.1 x h')⟩
    · have := hsub (mem_filter.2 ⟨ha.2.1, ha.2.2⟩)
      exact (mem_filter.1 this).2 hst.2.2.2.2
  have hc : |val₀ d₀| ≤ driftK L W (Fintype.card V) := by
    have hwd : wt d₀ = φ d₀ := by rw [hwt _ hel.1 hel.2, hφ _ hel.1]
    have hB3 := abs_le.1 (hB T₀ (M.tail d₀))
    have hB4 := abs_le.1 (hB T₀ (M.head d₀))
    have hWd := abs_le.1 (hW d₀)
    have e1 := hV _ hnT
    have l1 := le_abs_self L
    have l2 := neg_abs_le L
    have l3 := le_abs_self W
    have l4 := neg_abs_le W
    have l5 := le_abs_self B
    have l6 := neg_abs_le B
    simp only [driftK]
    rw [← hBdef]
    exact abs_le.2 ⟨by linarith, by linarith⟩
  exact ⟨h, hy, hna, hnT, hI', hC', hV', hred, hc⟩

end Klein

end PlanarFlow
