module

public import PlanarFlow.Klein.LCTEvert
public import PlanarFlow.DynTree.RunE

/-!
# Exchanging an edge of a stored tree: two cuts and two links

After `evert`, an exchange of edges in a tree of the map takes the following form: the tree `C`
is rooted at `r`, the edge of the parent dart of a face `z ≠ r` leaves the tree, and a new edge
`e` enters the root `r` from a face of the subtree of `z`. The new tree `C.hangRoot` is rooted at
`z`, `r` gets the parent dart `e`, every other face keeps its parent dart.

* `DTree.hangRoot`: this tree.
* `exchange_trep`: **the operations `cut (ιf z)`, `cut (ιe (C.par z))`, the two additions setting
  the values of the isolated node of the edge of `e`, `link (ιe e) (ιf (face e))` and
  `link (ιf r) (ιe e)` are valid, and give the forest storing `C.hangRoot`**, with the values of
  `e` and of its reverse set, the other values kept; the node of the old edge is left isolated.
* `Iso`: the nodes of the edges off the tree are isolated (roots of the forest);
  `evert_iso`, `addBoth_iso`: `evert` and the additions along a root path keep it, and none of
  the operations changes a node outside the tree (so the spanning tree and the cotree can share
  one forest).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap STFlow DynTree

variable {D X Y : Type*} [Fintype D] [DecidableEq D] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]
variable {N : CombMap D X Y} {n : ℕ} {C : DTree N} {ιf : Y → ℕ} {ιe : D → ℕ}

/-! ### Hanging the root -/

lemma anc_iterate_find (C : DTree N) {z x : Y} (h : C.Anc z x) (hz : z ≠ C.root) :
    ∃ m, C.up^[m] x = z ∧ ∀ i < m, C.up^[i] x ≠ z ∧ C.up^[i] x ≠ C.root := by
  classical
  refine ⟨Nat.find h, Nat.find_spec h, fun i hi => ⟨Nat.find_min h hi, fun hr => hz ?_⟩⟩
  have := Nat.find_spec h
  rw [show Nat.find h = (Nat.find h - i) + i by omega, Function.iterate_add_apply, hr,
    C.iterate_root] at this
  exact this.symm

/-- **The tree in which the root `r` hangs from the face of `e`**, in the subtree of `z`, which
becomes the root. -/
noncomputable def _root_.PlanarFlow.STFlow.DTree.hangRoot (C : DTree N) (z : Y) (e : D)
    (hz : z ≠ C.root) (he : N.face (N.rev e) = C.root) (ha : C.Anc z (N.face e)) : DTree N where
  root := z
  par := Function.update C.par C.root e
  head_par x hx := by
    by_cases h : x = C.root
    · subst h; rw [Function.update_self]; exact he
    · rw [Function.update_of_ne h]; exact C.head_par x h
  reach x := by
    have hup : ∀ y, y ≠ z → y ≠ C.root →
        upF N z (Function.update C.par C.root e) y = C.up y := fun y hyz hyr => by
      unfold upF; rw [ite_eq_right hyz, Function.update_of_ne hyr, C.up_of_ne hyr]
    -- the faces of the subtree of `z` climb to `z`
    have hsub : ∀ x, C.Anc z x → ∃ m, (upF N z (Function.update C.par C.root e))^[m] x = z := by
      intro x hx
      obtain ⟨m, hm, hlt⟩ := anc_iterate_find C hx hz
      refine ⟨m, ?_⟩
      have : ∀ i ≤ m, (upF N z (Function.update C.par C.root e))^[i] x = C.up^[i] x := by
        intro i
        induction i with
        | zero => intro _; rfl
        | succ i ih =>
          intro hi
          rw [Function.iterate_succ_apply', ih (by omega), Function.iterate_succ_apply',
            hup _ (hlt i (by omega)).1 (hlt i (by omega)).2]
      rw [this m le_rfl, hm]
    by_cases hx : C.Anc z x
    · exact hsub x hx
    · -- the others climb to the root, then hang below `z`
      have hnot : ∀ i, ¬ C.Anc z (C.up^[i] x) := fun i h => hx (by
        obtain ⟨m, hm⟩ := h
        exact ⟨m + i, by rw [Function.iterate_add_apply, hm]⟩)
      have hne : ∀ i, C.up^[i] x ≠ z := fun i h => hnot i (h ▸ C.anc_self z)
      have : ∀ i ≤ C.depth x, (upF N z (Function.update C.par C.root e))^[i] x = C.up^[i] x := by
        intro i
        induction i with
        | zero => intro _; rfl
        | succ i ih =>
          intro hi
          rw [Function.iterate_succ_apply', ih (by omega), Function.iterate_succ_apply',
            hup _ (hne i) (C.iterate_ne_root (by omega))]
      obtain ⟨m, hm⟩ := hsub _ ha
      refine ⟨m + 1 + C.depth x, ?_⟩
      rw [Function.iterate_add_apply, this _ le_rfl, C.iterate_depth, Function.iterate_succ_apply]
      have hrz : C.root ≠ z := fun h => hz h.symm
      have : upF N z (Function.update C.par C.root e) C.root = N.face e := by
        unfold upF; rw [ite_eq_right hrz, Function.update_self]
      rw [this, hm]

lemma hangRoot_par (C : DTree N) {z : Y} {e : D} (hz : z ≠ C.root)
    (he : N.face (N.rev e) = C.root) (ha : C.Anc z (N.face e)) (x : Y) :
    (C.hangRoot z e hz he ha).par x = Function.update C.par C.root e x := rfl

/-! ### Paths in a forest -/

/-- The root path of the node of `y` in a forest that stores the path from `y` to `up^k y` and
in which the node of `up^k y` is a root. -/
lemma upPath_seg {Fo : Forest} (hf : ∀ y, ιf y < n) (he : ∀ d, ιe d < n) :
    ∀ (k : ℕ) (y : Y), k ≤ C.depth y →
      (∀ i < k, Fo.par (ιf (C.up^[i] y)) = ιe (C.par (C.up^[i] y)) ∧
        Fo.par (ιe (C.par (C.up^[i] y))) = ιf (C.up^[i + 1] y)) →
      Fo.par (ιf (C.up^[k] y)) = n → ∀ fuel, 2 * k + 1 ≤ fuel →
      upPath Fo n fuel (ιf y) = tpath C ιf ιe k y := by
  intro k
  induction k with
  | zero =>
    intro y _ _ hr fuel hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [upPath, hf y, ↓reduceIte, tpath]
    rw [show C.up^[0] y = y from rfl] at hr
    rw [hr, upPath_nil]
  | succ k ih =>
    intro y hk hpath hr fuel hfuel
    have hyr : y ≠ C.root := by intro h; rw [h, C.depth_root] at hk; omega
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by omega⟩
    obtain ⟨h1, h2⟩ := hpath 0 (by omega)
    simp only [Function.iterate_zero, id] at h1 h2
    simp only [upPath, hf y, ↓reduceIte, h1, he, h2, tpath]
    rw [Function.iterate_one]
    refine congrArg _ (congrArg _ (ih _ (by rw [C.depth_up hyr] at hk; omega) (fun i hi => ?_)
      (by rw [← Function.iterate_succ_apply]; exact hr) _ (by omega)))
    obtain ⟨g1, g2⟩ := hpath (i + 1) (by omega)
    rw [Function.iterate_succ_apply] at g1 g2
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at g2
    exact ⟨g1, by rw [g2, Function.iterate_succ_apply]⟩

lemma tpath_getLast (k : ℕ) (y : Y) (q : ℕ) :
    (tpath C ιf ιe k y).getLastD q = ιf (C.up^[k] y) := by
  induction k generalizing y q with
  | zero => rfl
  | succ k ih =>
    rw [tpath_cons_cons, List.getLastD_cons, List.getLastD_cons, ih,
      Function.iterate_succ_apply]

/-! ### The isolated nodes -/

/-- **The nodes of the edges off the tree are isolated**: roots of the forest. -/
def Iso (n : ℕ) (Fo : Forest) (C : DTree N) (ιe : D → ℕ) : Prop :=
  ∀ d, (∀ y, y ≠ C.root → d ≠ C.par y ∧ d ≠ N.rev (C.par y)) → Fo.par (ιe d) = n

/-! ### The exchange -/

/-- The operations of the exchange. -/
def exchangeOps (ιf : Y → ℕ) (ιe : D → ℕ) (C : DTree N) (z : Y) (e : D) (δ₁ δ₂ : ℤ) :
    List EOp :=
  [.cut (ιf z), .cut (ιe (C.par z)), .add (ιe e) δ₁, .add2 (ιe e) δ₂,
    .link (ιe e) (ιf (N.face e)), .link (ιf C.root) (ιe e)]

/-- **The exchange on the stored tree**: the operations are valid, print nothing, store the tree
`C.hangRoot z e` with the values `t₁` on the reverse of `e` and `t₂` on `e` (set by the two
additions from the values `v₁`, `v₂` of the isolated node of the edge of `e`), keep the nodes
of the edges off the new tree isolated, and change no node outside the tree. -/
theorem exchange_trep {κ : D → ℝ} {β β₂ : Y → ℝ} {Fo : Forest}
    (hR : TRep n Fo C ιf ιe κ β β₂) (hI : Iso n Fo C ιe) (hN : Nodes n N ιf ιe)
    (hn : 2 * Fintype.card Y ≤ n) {z : Y} {e : D} (hz : z ≠ C.root)
    (he : N.face (N.rev e) = C.root) (ha : C.Anc z (N.face e))
    (hoffe : ∀ y, y ≠ C.root → e ≠ C.par y ∧ e ≠ N.rev (C.par y)) {v₁ v₂ t₁ t₂ : ℤ}
    (hv₁ : Fo.val (ιe e) = v₁) (hv₂ : Fo.val2 (ιe e) = v₂) :
    ValidOpsE n Fo (exchangeOps ιf ιe C z e (t₁ - v₁) (t₂ - v₂)) ∧
      (runOpsE n Fo (exchangeOps ιf ιe C z e (t₁ - v₁) (t₂ - v₂))).2 = [] ∧
      TRep n (runOpsE n Fo (exchangeOps ιf ιe C z e (t₁ - v₁) (t₂ - v₂))).1
        (C.hangRoot z e hz he ha) ιf ιe
        (fun d => if d = e then (t₂ : ℝ) else if d = N.rev e then (t₁ : ℝ) else κ d) β β₂ ∧
      Iso n (runOpsE n Fo (exchangeOps ιf ιe C z e (t₁ - v₁) (t₂ - v₂))).1
        (C.hangRoot z e hz he ha) ιe ∧
      ∀ u, (∀ y, u ≠ ιf y) → (∀ d, u ≠ ιe d) →
        (runOpsE n Fo (exchangeOps ιf ιe C z e (t₁ - v₁) (t₂ - v₂))).1.par u = Fo.par u ∧
        (runOpsE n Fo (exchangeOps ιf ιe C z e (t₁ - v₁) (t₂ - v₂))).1.val u = Fo.val u ∧
        (runOpsE n Fo (exchangeOps ιf ιe C z e (t₁ - v₁) (t₂ - v₂))).1.val2 u =
          Fo.val2 u := by
  classical
  have hf := hN.f_lt
  have hel := hN.e_lt
  set r := C.root with hr
  set fe := N.face e with hfe
  set pz := C.par z with hpz
  -- distinctness of the nodes involved
  have hez : ιe e ≠ ιe pz := fun h => by
    rcases hN.e_eq _ _ h with h | h
    · exact (hoffe z hz).1 h.symm
    · exact (hoffe z hz).2 (by rw [← hpz, h, N.rev_rev])
  have hrz : ιf r ≠ ιf z := fun h => hz (hN.f_inj h).symm
  have hepar : ∀ y, y ≠ r → ιe e ≠ ιe (C.par y) := fun y hy h => by
    rcases hN.e_eq _ _ h with h | h
    · exact (hoffe y hy).1 h.symm
    · exact (hoffe y hy).2 (by rw [h, N.rev_rev])
  have hpzy : ∀ y, y ≠ r → y ≠ z → ιe (C.par y) ≠ ιe pz := fun y hy hyz h =>
    hyz (C.par_eq_or hz hy (hN.e_eq _ _ h.symm))
  -- the intermediate forests
  set F1 := DynTree.cut Fo n (ιf z) with hF1
  set F2 := DynTree.cut F1 n (ιe pz) with hF2
  have hF2par : ∀ u, F2.par u = if u = ιe pz then n else if u = ιf z then n else Fo.par u := by
    intro u; simp only [hF2, hF1, DynTree.cut]
  have hF2e : F2.par (ιe e) = n := by
    rw [hF2par, ite_eq_right hez, ite_eq_right (Ne.symm (hN.fe _ _))]
    exact hI e hoffe
  have hrp2 : rootPath F2 n (ιe e) = [ιe e] := rootPath_root (hel e) hF2e
  set F3 := addPath F2 n (ιe e) ((t₁ - v₁ : ℤ) : ℝ) with hF3
  have hrp3 : rootPath F3 n (ιe e) = [ιe e] := by
    rw [rootPath_congr (Fo := F2) (Fo' := F3) rfl]; exact hrp2
  set F4 := addPath2 F3 n (ιe e) ((t₂ - v₂ : ℤ) : ℝ) with hF4
  set F5 := DynTree.link F4 (ιe e) (ιf fe) with hF5
  set F6 := DynTree.link F5 (ιf r) (ιe e) with hF6
  -- the path from the face of `e` to `z` in `F2`
  obtain ⟨m, hm, hlt⟩ := anc_iterate_find C ha hz
  have hmd : m ≤ C.depth fe := by
    by_contra h
    exact (hlt (C.depth fe) (by omega)).2 (C.iterate_depth fe)
  have hseg : ∀ G : Forest, (∀ u, u ≠ ιe e → G.par u = F2.par u) →
      ∀ fuel, 2 * m + 1 ≤ fuel → upPath G n fuel (ιf fe) = tpath C ιf ιe m fe := by
    intro G hG fuel hfuel
    refine upPath_seg hf hel m fe hmd (fun i hi => ⟨?_, ?_⟩) ?_ fuel hfuel
    · rw [hG _ (hN.fe _ _), hF2par, ite_eq_right (hN.fe _ _),
        ite_eq_right (fun h => (hlt i hi).1 (hN.f_inj h))]
      exact hR.pf _ (hlt i hi).2
    · have hne : C.up^[i] fe ≠ z := (hlt i hi).1
      rw [hG _ (fun h => hepar _ (hlt i hi).2 h.symm), hF2par,
        ite_eq_right (fun h => hne (C.par_eq_or hz (hlt i hi).2 (hN.e_eq _ _ h.symm))),
        ite_eq_right (Ne.symm (hN.fe _ _)), hR.pe _ (hlt i hi).2, Function.iterate_succ_apply',
        C.up_of_ne (hlt i hi).2]
    · rw [hm, hG _ (hN.fe _ _), hF2par, ite_eq_right (hN.fe _ _), ite_eq_left rfl]
  have hmn : 2 * m + 2 ≤ n := by
    have := C.depth_lt_card fe; omega
  have hroot4 : findRoot F4 n (ιf fe) = ιf z := by
    unfold findRoot rootPath
    rw [hseg F4 (fun u _ => rfl) n (by omega), tpath_getLast, hm]
  have hroot5 : findRoot F5 n (ιe e) = ιf z := by
    unfold findRoot rootPath
    have h5 : F5.par (ιe e) = ιf fe := by simp [hF5, DynTree.link]
    have hcons : upPath F5 n n (ιe e) = ιe e :: upPath F5 n (n - 1) (F5.par (ιe e)) := by
      have e1 : upPath F5 n n (ιe e) = upPath F5 n ((n - 1) + 1) (ιe e) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      rw [e1]
      simp [upPath, hel e]
    rw [hcons, h5,
      hseg F5 (fun u hu => by simp only [hF5, DynTree.link, ite_eq_right hu]; rfl) _ (by omega),
      List.getLastD_cons, tpath_getLast, hm]
  -- validity
  have hval : ValidOpsE n Fo (exchangeOps ιf ιe C z e (t₁ - v₁) (t₂ - v₂)) := by
    refine ⟨⟨hf z, by rw [hR.pf z hz]; exact hel _⟩, ⟨hel _, ?_⟩, hel _, hel _,
      ⟨hel _, hf _, hF2e, ?_⟩, ⟨hf _, hel _, ?_, ?_⟩, trivial⟩
    · show F1.par (ιe pz) < n
      simp only [hF1, DynTree.cut, ite_eq_right (Ne.symm (hN.fe _ _))]
      rw [hR.pe z hz]; exact hf _
    · show findRoot F4 n (ιf fe) ≠ ιe e
      rw [hroot4]; exact hN.fe _ _
    · show F5.par (ιf r) = n
      simp only [hF5, DynTree.link, ite_eq_right (hN.fe _ _)]
      show F2.par (ιf r) = n
      rw [hF2par, ite_eq_right (hN.fe _ _), ite_eq_right hrz]; exact hR.pr
    · show findRoot F5 n (ιe e) ≠ ιf r
      rw [hroot5]; exact Ne.symm hrz
  have hrun : (runOpsE n Fo (exchangeOps ιf ιe C z e (t₁ - v₁) (t₂ - v₂))).1 = F6 := by
    simp only [exchangeOps, runOpsE, EOp.apply]; rfl
  have hout : (runOpsE n Fo (exchangeOps ιf ιe C z e (t₁ - v₁) (t₂ - v₂))).2 = [] := by
    simp [exchangeOps, runOpsE, EOp.answer]
  -- the final forest
  have h6par : ∀ u, F6.par u = if u = ιf r then ιe e else if u = ιe e then ιf fe else
      if u = ιe pz then n else if u = ιf z then n else Fo.par u := by
    intro u
    simp only [hF6, hF5, hF4, hF3, DynTree.link, addPath, addPath2]
    rw [hF2par]
  have h6val : ∀ u, F6.val u = if u = ιe e then (t₁ : ℝ) else Fo.val u := by
    intro u
    simp only [hF6, hF5, hF4, hF3, DynTree.link, addPath2, addPath, hrp2, List.mem_singleton]
    simp only [hF2, hF1, DynTree.cut]
    split_ifs with h
    · rw [h, hv₁]; push_cast; ring
    · rfl
  have h6val2 : ∀ u, F6.val2 u = if u = ιe e then (t₂ : ℝ) else Fo.val2 u := by
    intro u
    simp only [hF6, hF5, hF4, DynTree.link, addPath2, hrp3, List.mem_singleton]
    simp only [hF3, addPath, hF2, hF1, DynTree.cut]
    split_ifs with h
    · rw [h, hv₂]; push_cast; ring
    · rfl
  rw [hrun]
  refine ⟨hval, hout, ⟨fun x hx => ?_, ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_,
    fun y => ?_, fun y => ?_⟩, fun d hd => ?_, fun u hu1 hu2 => ?_⟩
  · -- `pf`
    rw [hangRoot_par, h6par]
    by_cases hxr : x = r
    · rw [hxr, ite_eq_left rfl, Function.update_self]
    · have hxz : x ≠ z := hx
      rw [Function.update_of_ne hxr, ite_eq_right (fun h => hxr (hN.f_inj h)),
        ite_eq_right (hN.fe _ _), ite_eq_right (hN.fe _ _),
        ite_eq_right (fun h => hxz (hN.f_inj h))]
      exact hR.pf x hxr
  · -- `pr`
    show F6.par (ιf z) = n
    rw [h6par, ite_eq_right (Ne.symm hrz), ite_eq_right (hN.fe _ _), ite_eq_right (hN.fe _ _),
      ite_eq_left rfl]
  · -- `pe`
    rw [hangRoot_par, h6par]
    by_cases hxr : x = r
    · rw [hxr, Function.update_self, ite_eq_right (Ne.symm (hN.fe _ _)), ite_eq_left rfl]
    · have hxz : x ≠ z := hx
      rw [Function.update_of_ne hxr, ite_eq_right (Ne.symm (hN.fe _ _)),
        ite_eq_right (fun h => hepar x hxr h.symm), ite_eq_right (hpzy x hxr hxz),
        ite_eq_right (Ne.symm (hN.fe _ _))]
      exact hR.pe x hxr
  · -- `ve`
    rw [hangRoot_par, h6val]
    by_cases hxr : x = r
    · rw [hxr, Function.update_self, ite_eq_left rfl, ite_eq_right (N.rev_ne e), ite_eq_left rfl]
    · rw [Function.update_of_ne hxr, ite_eq_right (fun h => hepar x hxr h.symm), hR.ve x hxr]
      have h1 : N.rev (C.par x) ≠ e := fun h => (hoffe x hxr).2 (by rw [← h])
      have h2 : N.rev (C.par x) ≠ N.rev e := fun h => (hoffe x hxr).1 (by
        rw [← N.rev_rev e, ← h, N.rev_rev])
      rw [ite_eq_right h1, ite_eq_right h2]
  · -- `ve2`
    rw [hangRoot_par, h6val2]
    by_cases hxr : x = r
    · rw [hxr, Function.update_self, ite_eq_left rfl, ite_eq_left rfl]
    · rw [Function.update_of_ne hxr, ite_eq_right (fun h => hepar x hxr h.symm), hR.ve2 x hxr]
      rw [ite_eq_right (fun h => (hoffe x hxr).1 h.symm),
        ite_eq_right (fun h => (hoffe x hxr).2 (by rw [h, N.rev_rev]))]
  · rw [h6val, ite_eq_right (hN.fe _ _)]; exact hR.vf y
  · rw [h6val2, ite_eq_right (hN.fe _ _)]; exact hR.vf2 y
  · -- the isolated nodes
    rw [h6par, ite_eq_right (Ne.symm (hN.fe _ _))]
    have hde : d ≠ e ∧ d ≠ N.rev e := by
      have := hd r hz.symm
      simp only [hangRoot_par, ← hr, Function.update_self] at this
      exact this
    have hne : ιe d ≠ ιe e := fun h => by
      rcases hN.e_eq _ _ h with h | h
      · exact hde.1 h.symm
      · exact hde.2 (by rw [h, N.rev_rev])
    rw [ite_eq_right hne]
    by_cases h1 : ιe d = ιe pz
    · rw [ite_eq_left h1]
    · rw [ite_eq_right h1, ite_eq_right (Ne.symm (hN.fe _ _))]
      refine hI d fun y hy => ?_
      by_cases hyz : y = z
      · subst hyz
        exact ⟨fun h' => h1 (by rw [h']), fun h' => h1 (by rw [h', hN.e_rev])⟩
      · have := hd y hyz
        simp only [hangRoot_par, Function.update_of_ne hy] at this
        exact this
  · -- the nodes outside the tree
    refine ⟨?_, ?_, ?_⟩
    · rw [h6par, ite_eq_right (hu1 r), ite_eq_right (hu2 e), ite_eq_right (hu2 pz),
        ite_eq_right (hu1 z)]
    · rw [h6val, ite_eq_right (hu2 e)]
    · rw [h6val2, ite_eq_right (hu2 e)]

/-! ### The isolated nodes and the other nodes under `evert` and the additions -/

/-- The nodes of the root path of a face are nodes of the tree. -/
lemma mem_tpath_cases {k : ℕ} {y : Y} {u : ℕ} (h : u ∈ tpath C ιf ιe k y) :
    (∃ x, u = ιf x) ∨ ∃ i < k, u = ιe (C.par (C.up^[i] y)) := by
  rcases (mem_tpath k y u).1 h with ⟨i, -, rfl⟩ | h
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr h

/-- **`evert` keeps the nodes of the edges off the tree isolated** (the re-rooted tree has the
same edges), and changes no node outside the tree. -/
theorem evert_iso {κ : D → ℝ} {β β₂ : Y → ℝ} {Fo : Forest}
    (hR : TRep n Fo C ιf ιe κ β β₂) (hI : Iso n Fo C ιe) (hN : Nodes n N ιf ιe)
    (hn : 2 * Fintype.card Y ≤ n) (w : Y) :
    Iso n (evert Fo n (ιf w)) (C.reroot w) ιe ∧
      ∀ u, (∀ y, u ≠ ιf y) → (∀ d, u ≠ ιe d) →
        (evert Fo n (ιf w)).par u = Fo.par u ∧ (evert Fo n (ιf w)).val u = Fo.val u ∧
        (evert Fo n (ιf w)).val2 u = Fo.val2 u := by
  have hrp : rootPath Fo n (ιf w) = tpath C ιf ιe (C.depth w) w :=
    rootPath_rep hR hN.f_lt hN.e_lt hn w
  -- a node off the path keeps everything
  have hkeep : ∀ u, u ∉ tpath C ιf ιe (C.depth w) w →
      (evert Fo n (ιf w)).par u = Fo.par u ∧ (evert Fo n (ιf w)).val u = Fo.val u ∧
        (evert Fo n (ιf w)).val2 u = Fo.val2 u := by
    intro u hu
    refine ⟨?_, ?_, ?_⟩
    · change (revPar n (rootPath Fo n (ιf w)) u).getD (Fo.par u) = Fo.par u
      rw [hrp, revPar_of_not_mem hu]; rfl
    · change (if u ∈ rootPath Fo n (ιf w) then _ else _) = _
      rw [hrp, ite_eq_right hu]
    · change (if u ∈ rootPath Fo n (ιf w) then _ else _) = _
      rw [hrp, ite_eq_right hu]
  refine ⟨fun d hd => ?_, fun u hu1 hu2 => hkeep u fun h => ?_⟩
  · -- the edges of the re-rooted tree are those of the tree
    have hd' : ∀ y, y ≠ C.root → d ≠ C.par y ∧ d ≠ N.rev (C.par y) := by
      intro y hy
      by_cases hs : ∃ i < C.depth w, C.up^[i] w = y
      · obtain ⟨i, hi, rfl⟩ := hs
        have hne : C.up^[i + 1] w ≠ w := fun h => by
          have := C.iterate_inj (show i + 1 ≤ C.depth w by omega) (Nat.zero_le _) h
          omega
        have := hd (C.up^[i + 1] w) hne
        rw [reroot_par, rerootPar_anc C hi, N.rev_rev] at this
        exact ⟨this.2, this.1⟩
      · have hns : ¬ SAnc C w y := by
          rintro ⟨i, hi, rfl⟩
          rcases Nat.lt_or_ge (i + 1) (C.depth w) with h | h
          · exact hs ⟨i + 1, h, rfl⟩
          · exact hy (by rw [show i + 1 = C.depth w by omega, C.iterate_depth])
        have hyw : y ≠ w := by
          rintro rfl
          refine hs ⟨0, ?_, rfl⟩
          rcases Nat.eq_zero_or_pos (C.depth y) with h | h
          · exact absurd (by have := C.iterate_depth y; rw [h] at this; exact this) hy
          · exact h
        have := hd y hyw
        rw [reroot_par, rerootPar_not C hns] at this
        exact this
    have h1 := hI d hd'
    refine (hkeep _ fun hm => ?_).1.trans h1
    rcases mem_tpath_cases hm with ⟨x, hx⟩ | ⟨i, hi, hx⟩
    · exact hN.fe _ _ hx.symm
    · rcases hN.e_eq _ _ hx with h | h
      · exact (hd' _ (C.iterate_ne_root hi)).1 h.symm
      · exact (hd' _ (C.iterate_ne_root hi)).2 (by rw [h, N.rev_rev])
  · rcases mem_tpath_cases h with ⟨x, hx⟩ | ⟨i, -, hx⟩
    · exact hu1 x hx
    · exact hu2 _ hx

/-- **The additions along a root path keep the nodes of the edges off the tree isolated**, and
change no node outside the tree. -/
theorem addBoth_iso {κ : D → ℝ} {β β₂ : Y → ℝ} {Fo : Forest}
    (hR : TRep n Fo C ιf ιe κ β β₂) (hI : Iso n Fo C ιe) (hN : Nodes n N ιf ιe)
    (hn : 2 * Fintype.card Y ≤ n) (p : Y) (c : ℝ) :
    Iso n (addPath2 (addPath Fo n (ιf p) c) n (ιf p) (-c)) C ιe ∧
      ∀ u, (∀ y, u ≠ ιf y) → (∀ d, u ≠ ιe d) →
        (addPath2 (addPath Fo n (ιf p) c) n (ιf p) (-c)).par u = Fo.par u ∧
        (addPath2 (addPath Fo n (ιf p) c) n (ιf p) (-c)).val u = Fo.val u ∧
        (addPath2 (addPath Fo n (ιf p) c) n (ιf p) (-c)).val2 u = Fo.val2 u := by
  have hrp : rootPath Fo n (ιf p) = tpath C ιf ιe (C.depth p) p :=
    rootPath_rep hR hN.f_lt hN.e_lt hn p
  have hrp' : rootPath (addPath Fo n (ιf p) c) n (ιf p) = tpath C ιf ιe (C.depth p) p :=
    (rootPath_congr (Fo := Fo) (Fo' := addPath Fo n (ιf p) c) rfl _).trans hrp
  refine ⟨fun d hd => hI d hd, fun u hu1 hu2 => ⟨rfl, ?_, ?_⟩⟩
  · have hu : u ∉ tpath C ιf ιe (C.depth p) p := fun h => by
      rcases mem_tpath_cases h with ⟨x, hx⟩ | ⟨i, -, hx⟩
      · exact hu1 x hx
      · exact hu2 _ hx
    change (if u ∈ rootPath Fo n (ιf p) then _ else _) = _
    rw [hrp, ite_eq_right hu]
  · have hu : u ∉ tpath C ιf ιe (C.depth p) p := fun h => by
      rcases mem_tpath_cases h with ⟨x, hx⟩ | ⟨i, -, hx⟩
      · exact hu1 x hx
      · exact hu2 _ hx
    change (if u ∈ rootPath (addPath Fo n (ιf p) c) n (ιf p) then _ else _) = _
    rw [hrp', ite_eq_right hu]
    rfl

end Klein

end PlanarFlow
