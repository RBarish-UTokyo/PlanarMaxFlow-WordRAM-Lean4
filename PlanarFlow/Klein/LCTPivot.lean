module

public import PlanarFlow.Klein.LCTHang
public import PlanarFlow.Klein.LCTUpdate

/-!
# A pivot on the stored trees

The update of the two stored trees (`TRep`) after a pivot of Klein's algorithm, as lists of
operations of the evertable dynamic trees (`EOp`), valid end to end:

* `reparent_trep`: **reparenting a face other than the root** of a stored tree (two cuts, the
  two additions setting the values of the isolated node of the new edge, two links) stores the
  reparented tree (`DTree.reparent`): the update of the spanning tree after a pivot.
* `exists_cut_face`: the edge of the pivot arc `b` entering `y` lies on the path of the cotree
  between the faces of the old parent dart `a = T.par y` (from `chi_par_eq_cross`): below a face
  `z` of the cotree re-rooted at the face of `a`, on the path from the face of the reverse of `a`.
* `cotreePivot_trep`: **the pivot on the cotree** (`cotreeOps`: `evert` at the face of `a`, the
  two additions of `ADDPATH`, the exchange of the edge of `b` for the edge of `a`, `evert` back
  at the face `fe`) stores a cotree rooted at `fe` of the reparented tree, with the values
  `pivotVal` of `reparent_vinv`; the values at the nodes of the faces move by at most `|c|`.
* `point_trep`: **changing the values of one edge** of a stored tree (`pointOps`: two additions
  along the root path of the node of the edge, undone along the root path of the node of the
  parent face, for each of the two values): the changes of the weights between two moves.
* `Agree`, `TRep.congr`, `Iso.congr`: the stored trees of disjoint node sets do not interfere.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap STFlow DynTree

section Generic

variable {D X Y : Type*} [Fintype D] [DecidableEq D] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]
variable {N : CombMap D X Y} {n : ℕ} {C : DTree N} {ιf : Y → ℕ} {ιe : D → ℕ}

/-! ### Agreeing forests -/

/-- Two forests agree at the node `u`. -/
def Agree (Fo Fo' : Forest) (u : ℕ) : Prop :=
  Fo'.par u = Fo.par u ∧ Fo'.val u = Fo.val u ∧ Fo'.val2 u = Fo.val2 u

lemma Agree.trans {Fo Fo' Fo'' : Forest} {u : ℕ} (h1 : Agree Fo Fo' u)
    (h2 : Agree Fo' Fo'' u) : Agree Fo Fo'' u :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

/-- A stored tree stays stored in a forest agreeing at its nodes. -/
lemma TRep.congr {κ : D → ℝ} {β β₂ : Y → ℝ} {Fo Fo' : Forest} (hR : TRep n Fo C ιf ιe κ β β₂)
    (hf : ∀ y, Agree Fo Fo' (ιf y)) (he : ∀ d, Agree Fo Fo' (ιe d)) :
    TRep n Fo' C ιf ιe κ β β₂ :=
  ⟨fun y hy => (hf y).1.trans (hR.pf y hy), (hf _).1.trans hR.pr,
    fun y hy => (he _).1.trans (hR.pe y hy), fun y hy => (he _).2.1.trans (hR.ve y hy),
    fun y hy => (he _).2.2.trans (hR.ve2 y hy), fun y => (hf y).2.1.trans (hR.vf y),
    fun y => (hf y).2.2.trans (hR.vf2 y)⟩

/-- The values of the darts can be rewritten. -/
lemma TRep.congrκ {κ κ' : D → ℝ} {β β₂ : Y → ℝ} {Fo : Forest} (hR : TRep n Fo C ιf ιe κ β β₂)
    (h : ∀ d, κ d = κ' d) : TRep n Fo C ιf ιe κ' β β₂ :=
  ⟨hR.pf, hR.pr, hR.pe, fun y hy => (hR.ve y hy).trans (h _),
    fun y hy => (hR.ve2 y hy).trans (h _), hR.vf, hR.vf2⟩

/-- The values at the nodes of the faces can be rewritten. -/
lemma TRep.congrβ {κ : D → ℝ} {β β₂ β' β₂' : Y → ℝ} {Fo : Forest}
    (hR : TRep n Fo C ιf ιe κ β β₂) (h1 : ∀ y, β y = β' y) (h2 : ∀ y, β₂ y = β₂' y) :
    TRep n Fo C ιf ιe κ β' β₂' :=
  ⟨hR.pf, hR.pr, hR.pe, hR.ve, hR.ve2, fun y => (hR.vf y).trans (h1 y),
    fun y => (hR.vf2 y).trans (h2 y)⟩

lemma Iso.congr {Fo Fo' : Forest} (hI : Iso n Fo C ιe) (he : ∀ d, Agree Fo Fo' (ιe d)) :
    Iso n Fo' C ιe := fun d hd => (he d).1.trans (hI d hd)

/-- The nodes off the root path keep everything under `evert`. -/
lemma agree_evert {Fo : Forest} {v u : ℕ} (hu : u ∉ rootPath Fo n v) :
    Agree Fo (evert Fo n v) u := by
  refine ⟨?_, ?_, ?_⟩
  · change (revPar n (rootPath Fo n v) u).getD (Fo.par u) = Fo.par u
    rw [revPar_of_not_mem hu]; rfl
  · change (if u ∈ rootPath Fo n v then _ else _) = _
    rw [ite_eq_right hu]
  · change (if u ∈ rootPath Fo n v then _ else _) = _
    rw [ite_eq_right hu]

lemma agree_addPath {Fo : Forest} {v u : ℕ} (hu : u ∉ rootPath Fo n v) (c : ℝ) :
    Agree Fo (addPath Fo n v c) u :=
  ⟨rfl, by change (if u ∈ rootPath Fo n v then _ else _) = _; rw [ite_eq_right hu], rfl⟩

lemma agree_addPath2 {Fo : Forest} {v u : ℕ} (hu : u ∉ rootPath Fo n v) (c : ℝ) :
    Agree Fo (addPath2 Fo n v c) u :=
  ⟨rfl, rfl, by change (if u ∈ rootPath Fo n v then _ else _) = _; rw [ite_eq_right hu]⟩

/-- The node of an edge off the tree is not on the root path of a face. -/
lemma not_mem_tpath_off (hN : Nodes n N ιf ιe) {d : D}
    (hd : ∀ y, y ≠ C.root → d ≠ C.par y ∧ d ≠ N.rev (C.par y)) {k : ℕ} {y : Y}
    (hk : k ≤ C.depth y) : ιe d ∉ tpath C ιf ιe k y := fun h => by
  rcases mem_tpath_cases h with ⟨x, hx⟩ | ⟨i, hi, hx⟩
  · exact hN.fe _ _ hx.symm
  · have hne := C.iterate_ne_root (show i < C.depth y by omega)
    rcases hN.e_eq _ _ hx with h | h
    · exact (hd _ hne).1 h.symm
    · exact (hd _ hne).2 (by rw [h, N.rev_rev])

/-! ### Lists of operations -/

lemma runOpsE_append (n : ℕ) : ∀ (Fo : Forest) (os os' : List EOp),
    runOpsE n Fo (os ++ os') = ((runOpsE n (runOpsE n Fo os).1 os').1,
      (runOpsE n Fo os).2 ++ (runOpsE n (runOpsE n Fo os).1 os').2)
  | Fo, [], os' => by simp [runOpsE]
  | Fo, o :: os, os' => by
    simp only [List.cons_append, runOpsE, runOpsE_append n _ os os', List.append_assoc]

lemma validOpsE_append (n : ℕ) : ∀ (Fo : Forest) (os os' : List EOp),
    ValidOpsE n Fo (os ++ os') ↔ ValidOpsE n Fo os ∧ ValidOpsE n (runOpsE n Fo os).1 os'
  | Fo, [], os' => by simp [ValidOpsE, runOpsE]
  | Fo, o :: os, os' => by
    simp only [List.cons_append, ValidOpsE, runOpsE, validOpsE_append n _ os os', and_assoc]

/-! ### The edges of the trees -/

lemma off_iff_not_inT {d : D} :
    (∀ y, y ≠ C.root → d ≠ C.par y ∧ d ≠ N.rev (C.par y)) ↔ ¬ C.InT d := by
  constructor
  · rintro h ⟨y, hy, hd | hd⟩
    · exact (h y hy).1 hd
    · exact (h y hy).2 hd
  · intro h y hy
    exact ⟨fun hd => h ⟨y, hy, Or.inl hd⟩, fun hd => h ⟨y, hy, Or.inr hd⟩⟩

/-- Two faces sharing the edge of their parent darts are equal. -/
lemma eq_of_edge {w z : Y} (hw : w ≠ C.root) (hz : z ≠ C.root) {d : D}
    (h1 : d = C.par w ∨ d = N.rev (C.par w)) (h2 : d = C.par z ∨ d = N.rev (C.par z)) :
    w = z := by
  refine C.par_eq_or hz hw ?_
  rcases h1 with rfl | rfl <;> rcases h2 with h2 | h2
  · exact Or.inl h2
  · exact Or.inr h2
  · exact Or.inr (by rw [← h2, N.rev_rev])
  · exact Or.inl (by
      have := congrArg N.rev h2; rwa [N.rev_rev, N.rev_rev] at this)

/-- The edges of a re-rooted tree are those of the tree. -/
lemma reroot_inT {w : Y} {d : D} (h : (C.reroot w).InT d) : C.InT d := by
  obtain ⟨x, hx, hd⟩ := h
  have hxw : x ≠ w := hx
  rw [reroot_par] at hd
  by_cases hs : SAnc C w x
  · obtain ⟨i, hi, rfl⟩ := hs
    rw [rerootPar_anc C hi] at hd
    refine ⟨_, C.iterate_ne_root hi, ?_⟩
    rcases hd with hd | hd
    · exact Or.inr hd
    · exact Or.inl (by rw [hd, N.rev_rev])
  · rw [rerootPar_not C hs] at hd
    refine ⟨x, fun hxr => hs ?_, hd⟩
    have hw : w ≠ C.root := fun h => hxw (by rw [hxr, h])
    exact hxr ▸ root_sAnc C hw

/-- The edges of the tree after hanging the root. -/
lemma hangRoot_inT {z : Y} {e : D} {hz : z ≠ C.root} {he : N.face (N.rev e) = C.root}
    {ha : C.Anc z (N.face e)} {d : D} (h : (C.hangRoot z e hz he ha).InT d) :
    d = e ∨ d = N.rev e ∨ ∃ x, x ≠ C.root ∧ x ≠ z ∧ (d = C.par x ∨ d = N.rev (C.par x)) := by
  obtain ⟨x, hx, hd⟩ := h
  have hxz : x ≠ z := hx
  rw [hangRoot_par] at hd
  by_cases hxr : x = C.root
  · rw [hxr, Function.update_self] at hd
    rcases hd with hd | hd
    · exact Or.inl hd
    · exact Or.inr (Or.inl hd)
  · rw [Function.update_of_ne hxr] at hd
    exact Or.inr (Or.inr ⟨x, hxr, hxz, hd⟩)

/-- The edges of the tree after a reparenting. -/
lemma reparent_inT {x : Y} {e : D} {hx : x ≠ C.root} {he : N.face (N.rev e) = x}
    {hna : ¬ C.Anc x (N.face e)} {d : D} (h : (C.reparent x e hx he hna).InT d) :
    d = e ∨ d = N.rev e ∨ ∃ w, w ≠ C.root ∧ w ≠ x ∧ (d = C.par w ∨ d = N.rev (C.par w)) := by
  obtain ⟨w, hw, hd⟩ := h
  have hw' : w ≠ C.root := hw
  rw [DTree.reparent_par] at hd
  by_cases hwx : w = x
  · rw [ite_eq_left hwx] at hd
    rcases hd with hd | hd
    · exact Or.inl hd
    · exact Or.inr (Or.inl hd)
  · rw [ite_eq_right hwx] at hd
    exact Or.inr (Or.inr ⟨w, hw', hwx, hd⟩)

/-! ### Reparenting a face -/

/-- The operations of a reparenting of the face `x` on the new parent dart `e`. -/
def reparentOps (ιf : Y → ℕ) (ιe : D → ℕ) (C : DTree N) (x : Y) (e : D) (δ₁ δ₂ : ℤ) :
    List EOp :=
  [.cut (ιf x), .cut (ιe (C.par x)), .add (ιe e) δ₁, .add2 (ιe e) δ₂,
    .link (ιe e) (ιf (N.face e)), .link (ιf x) (ιe e)]

/-- **Reparenting a face on the stored tree**: the operations are valid, print nothing, store the
tree `C.reparent x e` with the values `t₁` on the reverse of `e` and `t₂` on `e` (set by the two
additions from the values `v₁`, `v₂` of the isolated node of the edge of `e`), keep the nodes
of the edges off the new tree isolated, and change no node outside the tree. -/
theorem reparent_trep {κ : D → ℝ} {β β₂ : Y → ℝ} {Fo : Forest}
    (hR : TRep n Fo C ιf ιe κ β β₂) (hI : Iso n Fo C ιe) (hN : Nodes n N ιf ιe)
    (hn : 2 * Fintype.card Y ≤ n) {x : Y} {e : D} (hx : x ≠ C.root)
    (he : N.face (N.rev e) = x) (hna : ¬ C.Anc x (N.face e))
    (hoffe : ∀ y, y ≠ C.root → e ≠ C.par y ∧ e ≠ N.rev (C.par y)) {v₁ v₂ t₁ t₂ : ℤ}
    (hv₁ : Fo.val (ιe e) = v₁) (hv₂ : Fo.val2 (ιe e) = v₂) :
    ValidOpsE n Fo (reparentOps ιf ιe C x e (t₁ - v₁) (t₂ - v₂)) ∧
      (runOpsE n Fo (reparentOps ιf ιe C x e (t₁ - v₁) (t₂ - v₂))).2 = [] ∧
      TRep n (runOpsE n Fo (reparentOps ιf ιe C x e (t₁ - v₁) (t₂ - v₂))).1
        (C.reparent x e hx he hna) ιf ιe
        (fun d => if d = e then (t₂ : ℝ) else if d = N.rev e then (t₁ : ℝ) else κ d) β β₂ ∧
      Iso n (runOpsE n Fo (reparentOps ιf ιe C x e (t₁ - v₁) (t₂ - v₂))).1
        (C.reparent x e hx he hna) ιe ∧
      ∀ u, (∀ y, u ≠ ιf y) → (∀ d, u ≠ ιe d) →
        Agree Fo (runOpsE n Fo (reparentOps ιf ιe C x e (t₁ - v₁) (t₂ - v₂))).1 u := by
  classical
  have hf := hN.f_lt
  have hel := hN.e_lt
  set r := C.root with hr
  set fe := N.face e with hfe
  set px := C.par x with hpx
  have hex : ιe e ≠ ιe px := fun h => by
    rcases hN.e_eq _ _ h with h | h
    · exact (hoffe x hx).1 h.symm
    · exact (hoffe x hx).2 (by rw [← hpx, h, N.rev_rev])
  have hrx : ιf r ≠ ιf x := fun h => hx (hN.f_inj h).symm
  have hepar : ∀ y, y ≠ r → ιe e ≠ ιe (C.par y) := fun y hy h => by
    rcases hN.e_eq _ _ h with h | h
    · exact (hoffe y hy).1 h.symm
    · exact (hoffe y hy).2 (by rw [h, N.rev_rev])
  have hpxy : ∀ y, y ≠ r → y ≠ x → ιe (C.par y) ≠ ιe px := fun y hy hyx h =>
    hyx (C.par_eq_or hx hy (hN.e_eq _ _ h.symm))
  -- the intermediate forests
  set F1 := DynTree.cut Fo n (ιf x) with hF1
  set F2 := DynTree.cut F1 n (ιe px) with hF2
  have hF2par : ∀ u, F2.par u = if u = ιe px then n else if u = ιf x then n else Fo.par u := by
    intro u; simp only [hF2, hF1, DynTree.cut]
  have hF2e : F2.par (ιe e) = n := by
    rw [hF2par, ite_eq_right hex, ite_eq_right (Ne.symm (hN.fe _ _))]
    exact hI e hoffe
  have hrp2 : rootPath F2 n (ιe e) = [ιe e] := rootPath_root (hel e) hF2e
  set F3 := addPath F2 n (ιe e) ((t₁ - v₁ : ℤ) : ℝ) with hF3
  have hrp3 : rootPath F3 n (ιe e) = [ιe e] := by
    rw [rootPath_congr (Fo := F2) (Fo' := F3) rfl]; exact hrp2
  set F4 := addPath2 F3 n (ιe e) ((t₂ - v₂ : ℤ) : ℝ) with hF4
  set F5 := DynTree.link F4 (ιe e) (ιf fe) with hF5
  set F6 := DynTree.link F5 (ιf x) (ιe e) with hF6
  -- the path from the face of `e` to the root in `F2`
  have hnot : ∀ i, C.up^[i] fe ≠ x := fun i h => hna ⟨i, h⟩
  have hseg : ∀ G : Forest, (∀ u, u ≠ ιe e → G.par u = F2.par u) →
      ∀ fuel, 2 * C.depth fe + 1 ≤ fuel →
        upPath G n fuel (ιf fe) = tpath C ιf ιe (C.depth fe) fe := by
    intro G hG fuel hfuel
    refine upPath_seg hf hel _ fe le_rfl (fun i hi => ⟨?_, ?_⟩) ?_ fuel hfuel
    · rw [hG _ (hN.fe _ _), hF2par, ite_eq_right (hN.fe _ _),
        ite_eq_right (fun h => hnot i (hN.f_inj h))]
      exact hR.pf _ (C.iterate_ne_root hi)
    · rw [hG _ (fun h => hepar _ (C.iterate_ne_root hi) h.symm), hF2par,
        ite_eq_right (hpxy _ (C.iterate_ne_root hi) (hnot i)),
        ite_eq_right (Ne.symm (hN.fe _ _)), hR.pe _ (C.iterate_ne_root hi),
        Function.iterate_succ_apply', C.up_of_ne (C.iterate_ne_root hi)]
    · rw [C.iterate_depth, hG _ (hN.fe _ _), hF2par, ite_eq_right (hN.fe _ _),
        ite_eq_right hrx]
      exact hR.pr
  have hmn : 2 * C.depth fe + 2 ≤ n := by
    have := C.depth_lt_card fe; omega
  have hroot4 : findRoot F4 n (ιf fe) = ιf r := by
    unfold findRoot rootPath
    rw [hseg F4 (fun u _ => rfl) n (by omega), tpath_getLast, C.iterate_depth]
  have hroot5 : findRoot F5 n (ιe e) = ιf r := by
    unfold findRoot rootPath
    have h5 : F5.par (ιe e) = ιf fe := by simp [hF5, DynTree.link]
    have hcons : upPath F5 n n (ιe e) = ιe e :: upPath F5 n (n - 1) (F5.par (ιe e)) := by
      have e1 : upPath F5 n n (ιe e) = upPath F5 n ((n - 1) + 1) (ιe e) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      rw [e1]
      simp [upPath, hel e]
    rw [hcons, h5,
      hseg F5 (fun u hu => by simp only [hF5, DynTree.link, ite_eq_right hu]; rfl) _ (by omega),
      List.getLastD_cons, tpath_getLast, C.iterate_depth]
  -- validity
  have hval : ValidOpsE n Fo (reparentOps ιf ιe C x e (t₁ - v₁) (t₂ - v₂)) := by
    refine ⟨⟨hf x, by rw [hR.pf x hx]; exact hel _⟩, ⟨hel _, ?_⟩, hel _, hel _,
      ⟨hel _, hf _, hF2e, ?_⟩, ⟨hf _, hel _, ?_, ?_⟩, trivial⟩
    · show F1.par (ιe px) < n
      simp only [hF1, DynTree.cut, ite_eq_right (Ne.symm (hN.fe _ _))]
      rw [hR.pe x hx]; exact hf _
    · show findRoot F4 n (ιf fe) ≠ ιe e
      rw [hroot4]; exact hN.fe _ _
    · show F5.par (ιf x) = n
      simp only [hF5, DynTree.link, ite_eq_right (hN.fe _ _)]
      show F2.par (ιf x) = n
      rw [hF2par, ite_eq_right (hN.fe _ _), ite_eq_left rfl]
    · show findRoot F5 n (ιe e) ≠ ιf x
      rw [hroot5]; exact hrx
  have hrun : (runOpsE n Fo (reparentOps ιf ιe C x e (t₁ - v₁) (t₂ - v₂))).1 = F6 := by
    simp only [reparentOps, runOpsE, EOp.apply]; rfl
  have hout : (runOpsE n Fo (reparentOps ιf ιe C x e (t₁ - v₁) (t₂ - v₂))).2 = [] := by
    simp [reparentOps, runOpsE, EOp.answer]
  -- the final forest
  have h6par : ∀ u, F6.par u = if u = ιf x then ιe e else if u = ιe e then ιf fe else
      if u = ιe px then n else if u = ιf x then n else Fo.par u := by
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
  refine ⟨hval, hout, ⟨fun y hy => ?_, ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_,
    fun y => ?_, fun y => ?_⟩, fun d hd => ?_, fun u hu1 hu2 => ?_⟩
  · -- `pf`
    have hy' : y ≠ r := hy
    rw [DTree.reparent_par, h6par]
    by_cases hyx : y = x
    · rw [ite_eq_left hyx, ite_eq_left (by rw [hyx])]
    · rw [ite_eq_right hyx, ite_eq_right (fun h => hyx (hN.f_inj h)), ite_eq_right (hN.fe _ _),
        ite_eq_right (hN.fe _ _), ite_eq_right (fun h => hyx (hN.f_inj h))]
      exact hR.pf y hy'
  · -- `pr`
    show F6.par (ιf r) = n
    rw [h6par, ite_eq_right hrx, ite_eq_right (hN.fe _ _), ite_eq_right (hN.fe _ _),
      ite_eq_right hrx]
    exact hR.pr
  · -- `pe`
    have hy' : y ≠ r := hy
    rw [DTree.reparent_par]
    by_cases hyx : y = x
    · rw [ite_eq_left hyx, h6par, ite_eq_right (Ne.symm (hN.fe _ _)), ite_eq_left rfl]
    · rw [ite_eq_right hyx, h6par, ite_eq_right (Ne.symm (hN.fe _ _)),
        ite_eq_right (fun h => hepar y hy' h.symm), ite_eq_right (hpxy y hy' hyx),
        ite_eq_right (Ne.symm (hN.fe _ _))]
      exact hR.pe y hy'
  · -- `ve`
    have hy' : y ≠ r := hy
    rw [DTree.reparent_par, h6val]
    by_cases hyx : y = x
    · rw [ite_eq_left hyx, ite_eq_left rfl, ite_eq_right (N.rev_ne e), ite_eq_left rfl]
    · rw [ite_eq_right hyx, ite_eq_right (fun h => hepar y hy' h.symm), hR.ve y hy']
      have h1 : N.rev (C.par y) ≠ e := fun h => (hoffe y hy').2 (by rw [← h])
      have h2 : N.rev (C.par y) ≠ N.rev e := fun h => (hoffe y hy').1 (by
        rw [← N.rev_rev e, ← h, N.rev_rev])
      rw [ite_eq_right h1, ite_eq_right h2]
  · -- `ve2`
    have hy' : y ≠ r := hy
    rw [DTree.reparent_par, h6val2]
    by_cases hyx : y = x
    · rw [ite_eq_left hyx, ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right hyx, ite_eq_right (fun h => hepar y hy' h.symm), hR.ve2 y hy']
      rw [ite_eq_right (fun h => (hoffe y hy').1 h.symm),
        ite_eq_right (fun h => (hoffe y hy').2 (by rw [h, N.rev_rev]))]
  · rw [h6val, ite_eq_right (hN.fe _ _)]; exact hR.vf y
  · rw [h6val2, ite_eq_right (hN.fe _ _)]; exact hR.vf2 y
  · -- the isolated nodes
    rw [h6par, ite_eq_right (Ne.symm (hN.fe _ _))]
    have hde : d ≠ e ∧ d ≠ N.rev e := by
      have := hd x hx
      simp only [DTree.reparent_par] at this
      exact this
    have hne : ιe d ≠ ιe e := fun h => by
      rcases hN.e_eq _ _ h with h | h
      · exact hde.1 h.symm
      · exact hde.2 (by rw [h, N.rev_rev])
    rw [ite_eq_right hne]
    by_cases h1 : ιe d = ιe px
    · rw [ite_eq_left h1]
    · rw [ite_eq_right h1, ite_eq_right (Ne.symm (hN.fe _ _))]
      refine hI d fun y hy => ?_
      by_cases hyx : y = x
      · subst hyx
        exact ⟨fun h' => h1 (by rw [h']), fun h' => h1 (by rw [h', hN.e_rev])⟩
      · have := hd y hy
        simp only [DTree.reparent_par, ite_eq_right hyx] at this
        exact this
  · -- the nodes outside the tree
    refine ⟨?_, ?_, ?_⟩
    · rw [h6par, ite_eq_right (hu1 x), ite_eq_right (hu2 e), ite_eq_right (hu2 px),
        ite_eq_right (hu1 x)]
    · rw [h6val, ite_eq_right (hu2 e)]
    · rw [h6val2, ite_eq_right (hu2 e)]

/-! ### Changing the values of one edge -/

/-- The operations changing the values of the edge of the parent dart `p = C.par z` by `δ₂` on
`p` and `δ₁` on its reverse: the additions along the root path of the node of the edge, undone
along the root path of the node of the parent face. -/
def pointOps (ιf : Y → ℕ) (ιe : D → ℕ) (C : DTree N) (z : Y) (δ₁ δ₂ : ℤ) : List EOp :=
  [.add (ιe (C.par z)) δ₁, .add (ιf (N.face (C.par z))) (-δ₁), .add2 (ιe (C.par z)) δ₂,
    .add2 (ιf (N.face (C.par z))) (-δ₂)]

/-- **Changing the values of one edge of a stored tree**: the four operations of `pointOps` are
valid, print nothing, change the values of the parent dart of `z` by `δ₂` and of its reverse by
`δ₁`, and no other value nor any parent. -/
theorem point_trep {κ : D → ℝ} {β β₂ : Y → ℝ} {Fo : Forest} (hR : TRep n Fo C ιf ιe κ β β₂)
    (hN : Nodes n N ιf ιe) (hn : 2 * Fintype.card Y ≤ n) {z : Y} (hz : z ≠ C.root)
    (δ₁ δ₂ : ℤ) :
    ValidOpsE n Fo (pointOps ιf ιe C z δ₁ δ₂) ∧ (runOpsE n Fo (pointOps ιf ιe C z δ₁ δ₂)).2 = [] ∧
      TRep n (runOpsE n Fo (pointOps ιf ιe C z δ₁ δ₂)).1 C ιf ιe
        (fun d => κ d + (if d = C.par z then (δ₂ : ℝ) else 0) +
          (if d = N.rev (C.par z) then (δ₁ : ℝ) else 0)) β β₂ ∧
      (runOpsE n Fo (pointOps ιf ιe C z δ₁ δ₂)).1.par = Fo.par ∧
      ∀ u, u ≠ ιe (C.par z) → Agree Fo (runOpsE n Fo (pointOps ιf ιe C z δ₁ δ₂)).1 u := by
  classical
  have hfp : N.face (C.par z) = C.up z := (C.up_of_ne hz).symm
  have hdz := C.depth_up hz
  have hdl := C.depth_lt_card z
  set P := tpath C ιf ιe (C.depth (C.up z)) (C.up z) with hP
  -- the root paths
  have hrf : ∀ G : Forest, G.par = Fo.par → rootPath G n (ιf (N.face (C.par z))) = P :=
    fun G hG => by
      rw [rootPath_congr hG, hfp]
      exact rootPath_rep hR hN.f_lt hN.e_lt hn _
  have hpe' : Fo.par (ιe (C.par z)) = ιf (C.up z) := by rw [hR.pe z hz, hfp]
  have hre : ∀ G : Forest, G.par = Fo.par → rootPath G n (ιe (C.par z)) = ιe (C.par z) :: P :=
    fun G hG => by
      rw [rootPath_congr hG]
      unfold rootPath
      have e1 : upPath Fo n n (ιe (C.par z)) = upPath Fo n ((n - 1) + 1) (ιe (C.par z)) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      rw [e1]
      simp only [upPath, hN.e_lt (C.par z), ↓reduceIte]
      rw [hpe', upPath_rep hR hN.f_lt hN.e_lt _ _ rfl _ (by omega)]
  have hnot : ιe (C.par z) ∉ P := fun hu => by
    rcases mem_tpath_cases hu with ⟨x, hx⟩ | ⟨i, hi, hx⟩
    · exact hN.fe _ _ hx.symm
    · have h1 := C.par_eq_or hz (C.iterate_ne_root hi) (hN.e_eq _ _ hx)
      rw [← Function.iterate_succ_apply] at h1
      have := C.iterate_inj (show i + 1 ≤ C.depth z by omega) (show 0 ≤ C.depth z by omega) h1
      omega
  -- the final forest
  set G : Forest := ⟨Fo.par, fun u => Fo.val u + if u = ιe (C.par z) then (δ₁ : ℝ) else 0,
    fun u => Fo.val2 u + if u = ιe (C.par z) then (δ₂ : ℝ) else 0⟩ with hG
  have hrun : (runOpsE n Fo (pointOps ιf ιe C z δ₁ δ₂)).1 = G := by
    simp only [pointOps, runOpsE, EOp.apply, addPath2, addPath, hG, Forest.mk.injEq, true_and,
      hre, hrf]
    refine ⟨funext fun u => ?_, funext fun u => ?_⟩
    · by_cases hu : u = ιe (C.par z)
      · subst hu; simp [hnot]
      · by_cases hu' : u ∈ P <;> simp [hu, hu']
    · by_cases hu : u = ιe (C.par z)
      · subst hu; simp [hnot]
      · by_cases hu' : u ∈ P <;> simp [hu, hu']
  have hout : (runOpsE n Fo (pointOps ιf ιe C z δ₁ δ₂)).2 = [] := by
    simp [pointOps, runOpsE, EOp.answer]
  rw [hrun]
  have hrev : ∀ y, y ≠ C.root → y ≠ z → C.par y ≠ C.par z ∧ C.par y ≠ N.rev (C.par z) ∧
      N.rev (C.par y) ≠ C.par z ∧ N.rev (C.par y) ≠ N.rev (C.par z) := by
    intro y hy hyz
    have h1 : C.par y ≠ C.par z := fun h => hyz (C.par_eq_or hz hy (Or.inl h))
    have h2 : C.par y ≠ N.rev (C.par z) := fun h => hyz (C.par_eq_or hz hy (Or.inr h))
    refine ⟨h1, h2, fun h => h2 (by rw [← h, N.rev_rev]), fun h => h1 ?_⟩
    have := congrArg N.rev h; rwa [N.rev_rev, N.rev_rev] at this
  have hep : ∀ y, y ≠ C.root → y ≠ z → ιe (C.par y) ≠ ιe (C.par z) := fun y hy hyz h =>
    hyz (C.par_eq_or hz hy (hN.e_eq _ _ h.symm))
  refine ⟨⟨hN.e_lt _, hN.f_lt _, hN.e_lt _, hN.f_lt _, trivial⟩, hout,
    ⟨hR.pf, hR.pr, hR.pe, fun y hy => ?_, fun y hy => ?_, fun y => ?_, fun y => ?_⟩, rfl,
    fun u hu => ⟨rfl, by simp [hG, hu], by simp [hG, hu]⟩⟩
  · show Fo.val _ + _ = _
    rw [hR.ve y hy]
    by_cases hyz : y = z
    · subst hyz
      simp [N.rev_ne]
    · obtain ⟨-, -, h3, h4⟩ := hrev y hy hyz
      simp [hep y hy hyz, h3, h4]
  · show Fo.val2 _ + _ = _
    rw [hR.ve2 y hy]
    by_cases hyz : y = z
    · subst hyz
      simp [Ne.symm (N.rev_ne _)]
    · obtain ⟨h1, h2, -, -⟩ := hrev y hy hyz
      simp [hep y hy hyz, h1, h2]
  · show Fo.val _ + _ = _
    rw [hR.vf y, ite_eq_right (hN.fe _ _), add_zero]
  · show Fo.val2 _ + _ = _
    rw [hR.vf2 y, ite_eq_right (hN.fe _ _), add_zero]

end Generic

/-! ### A pivot on the cotree -/

section Cotree

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {n : ℕ} {ιf : F → ℕ} {ιe : D → ℕ}

/-- The parent darts of the cotree are off the tree: so are all the darts of its edges. -/
lemma not_inT_of_inT {T : DTree M.dual} {C : DTree M}
    (hoff : ∀ x, x ≠ C.root → ¬ T.InT (C.par x)) {d : D} (h : C.InT d) : ¬ T.InT d := by
  obtain ⟨x, hx, rfl | rfl⟩ := h
  · exact hoff x hx
  · intro h'
    have := T.inT_rev h'
    exact hoff x hx (by simpa [CombMap.dual, M.rev_rev] using this)

lemma hoff_reroot {T : DTree M.dual} {C : DTree M}
    (hoff : ∀ x, x ≠ C.root → ¬ T.InT (C.par x)) (w : F) :
    ∀ x, x ≠ (C.reroot w).root → ¬ T.InT ((C.reroot w).par x) := fun _ hx =>
  not_inT_of_inT hoff (reroot_inT ((C.reroot w).inT_par hx))

/-- **The edge of the pivot arc lies on the path of the cotree between the faces of the old parent
dart** (the fundamental cut of `a = T.par y` is the fundamental cycle of its dual,
`chi_par_eq_cross`): re-rooted at the face of `a`, the cotree has a face `z` on the path from the
face of the reverse of `a` whose parent dart is `b` or its reverse. -/
theorem exists_cut_face (hM : M.IsPlane) {T : DTree M.dual} {C : DTree M}
    (hoff : ∀ x, x ≠ C.root → ¬ T.InT (C.par x)) {y : V} (hy : y ≠ T.root) {b : D}
    (hby : M.dual.face (M.dual.rev b) = y) (hna : ¬ T.Anc y (M.dual.face b)) (hbT : ¬ T.InT b) :
    ∃ z, z ≠ (C.reroot (M.face (T.par y))).root ∧
      ((C.reroot (M.face (T.par y))).par z = b ∨
        (C.reroot (M.face (T.par y))).par z = M.rev b) ∧
      (C.reroot (M.face (T.par y))).Anc z (M.face (M.rev (T.par y))) := by
  set C1 := C.reroot (M.face (T.par y)) with hC1
  have haT : T.InT (T.par y) := T.inT_par hy
  have hba : b ≠ T.par y := fun h => hbT (h ▸ haT)
  have hbra : b ≠ M.rev (T.par y) := fun h => hbT (h ▸ T.inT_rev haT)
  have hcross := chi_par_eq_cross T hM hy hba hbra
  have hc : cross M (tsub T y) b = -1 := by
    have h1 : M.tail b ∉ tsub T y := fun h => hna ((mem_tsub T).1 h)
    have h2 : M.head b ∈ tsub T y :=
      (mem_tsub T).2 (by rw [← dual_face_rev, hby]; exact T.anc_self y)
    simp [cross, h1, h2]
  have hchi : pflow C1 (M.face (M.rev (T.par y))) =
      T.chi (M.face (T.par y)) (M.face (M.rev (T.par y))) :=
    (chi_eq_pflow hM T C1 (hoff_reroot hoff _) _).symm
  have hp : pflow C1 (M.face (M.rev (T.par y))) b = -1 := by rw [hchi, hcross, hc]
  unfold pflow at hp
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hp]; norm_num)
  have hi' := mem_range.1 hi
  refine ⟨C1.up^[i] (M.face (M.rev (T.par y))), C1.iterate_ne_root hi', ?_, ⟨i, rfl⟩⟩
  by_contra hno
  push Not at hno
  apply hne
  have h1 : b ≠ C1.par (C1.up^[i] (M.face (M.rev (T.par y)))) := fun h => hno.1 h.symm
  have h2 : b ≠ M.rev (C1.par (C1.up^[i] (M.face (M.rev (T.par y))))) := fun h =>
    hno.2 (by rw [h, M.rev_rev])
  simp [h1, h2]

/-- The operations of a pivot on the cotree: `evert` at the face of the old parent dart `a`,
`ADDPATH` (`-c` on the first values, `c` on the second values of the root path of the face of the
reverse of `a`), the exchange of the edge of the pivot arc (the parent edge of the face `z`) for
the edge of `a` (`exchangeOps`), and `evert` back at the face `fe`. -/
noncomputable def cotreeOps (ιf : F → ℕ) (ιe : D → ℕ) (C : DTree M) (a : D) (z fe : F)
    (c δ₁ δ₂ : ℤ) : List EOp :=
  [.evert (ιf (M.face a)), .add (ιf (M.face (M.rev a))) (-c),
      .add2 (ιf (M.face (M.rev a))) c] ++
    exchangeOps ιf ιe (C.reroot (M.face a)) z (M.rev a) δ₁ δ₂ ++ [.evert (ιf fe)]

/-- **A pivot on the stored cotree.** The cotree `C` (its parent darts off the spanning tree `T`)
is stored with the values `val` of the darts; the pivot gives the vertex `y` the parent dart `b`
(off `T`, its tail not below `y`), and `z` is the face of `exists_cut_face`. The operations
`cotreeOps` (with the values `v₁`, `v₂` of the isolated node of the edge of `a = T.par y` read
before) are valid, print nothing, and store a cotree rooted at `fe` whose parent darts are off
the reparented tree `T.reparent y b`, with the values `pivotVal T φ wt val y c` of the update of
`reparent_vinv` (`c · T.chi` along the path between the faces of `a`, and the new values of the
two darts of `a`); the nodes of the edges off the new cotree stay isolated, the nodes outside the
cotree are not changed, and the values at the nodes of the faces move by at most `|c|`. -/
theorem cotreePivot_trep (hM : M.IsPlane) {T : DTree M.dual} {C : DTree M}
    (hoff : ∀ x, x ≠ C.root → ¬ T.InT (C.par x)) (hN : Nodes n M ιf ιe)
    (hn : 2 * Fintype.card F ≤ n) {val : D → ℤ} {β β₂ : F → ℝ} {Fo : Forest}
    (hR : TRep n Fo C ιf ιe (fun d => (val d : ℝ)) β β₂) (hI : Iso n Fo C ιe)
    {y : V} (hy : y ≠ T.root) {b : D} (hby : M.dual.face (M.dual.rev b) = y)
    (hna : ¬ T.Anc y (M.dual.face b)) (hbT : ¬ T.InT b) {z : F}
    (hz : z ≠ (C.reroot (M.face (T.par y))).root)
    (hzb : (C.reroot (M.face (T.par y))).par z = b ∨
      (C.reroot (M.face (T.par y))).par z = M.rev b)
    (hza : (C.reroot (M.face (T.par y))).Anc z (M.face (M.rev (T.par y))))
    (fe : F) (φ wt : D → ℤ) (c : ℤ) {v₁ v₂ : ℤ} (hv₁ : Fo.val (ιe (T.par y)) = v₁)
    (hv₂ : Fo.val2 (ιe (T.par y)) = v₂) {os : List EOp}
    (hos : os = cotreeOps ιf ιe C (T.par y) z fe c (wt (T.par y) - φ (T.par y) - c - v₁)
      (wt (M.rev (T.par y)) + φ (T.par y) + c - v₂)) :
    ValidOpsE n Fo os ∧ (runOpsE n Fo os).2 = [] ∧
      ∃ C' : DTree M, C'.root = fe ∧
        (∀ x, x ≠ C'.root → ¬ (T.reparent y b hy hby hna).InT (C'.par x)) ∧
        Iso n (runOpsE n Fo os).1 C' ιe ∧
        (∀ u, (∀ x, u ≠ ιf x) → (∀ d, u ≠ ιe d) → Agree Fo (runOpsE n Fo os).1 u) ∧
        ∃ β' β₂' : F → ℝ, TRep n (runOpsE n Fo os).1 C' ιf ιe
            (fun d => (pivotVal T φ wt val y c d : ℝ)) β' β₂' ∧
          ∀ Lo : ℝ, (∀ x, Lo ≤ β x ∧ Lo ≤ β₂ x) →
            ∀ x, Lo - |(c : ℝ)| ≤ β' x ∧ Lo - |(c : ℝ)| ≤ β₂' x := by
  classical
  subst hos
  set a := T.par y with ha
  set fa := M.face a with hfa
  set fra := M.face (M.rev a) with hfra
  set C1 := C.reroot fa with hC1
  have haT : T.InT a := T.inT_par hy
  have hoff1 := hoff_reroot hoff fa
  have haC : ∀ x, x ≠ C.root → a ≠ C.par x ∧ a ≠ M.rev (C.par x) :=
    off_iff_not_inT.2 fun h => not_inT_of_inT hoff h haT
  have haC1 : ∀ x, x ≠ C1.root → a ≠ C1.par x ∧ a ≠ M.rev (C1.par x) :=
    off_iff_not_inT.2 fun h => not_inT_of_inT hoff1 h haT
  have hraC1 : ∀ x, x ≠ C1.root → M.rev a ≠ C1.par x ∧ M.rev a ≠ M.rev (C1.par x) :=
    off_iff_not_inT.2 fun h => not_inT_of_inT hoff1 h (T.inT_rev haT)
  -- `evert` at the face of `a`
  have h1 := evert_trep hR hN hn fa
  have i1 := evert_iso hR hI hN hn fa
  set F1 := evert Fo n (ιf fa) with hF1
  -- `ADDPATH`
  have h2 := addBoth_trep h1 hN hn fra (-(c : ℝ))
  have i2 := addBoth_iso h1 i1.1 hN hn fra (-(c : ℝ))
  rw [neg_neg] at h2 i2
  set F2 := addPath2 (addPath F1 n (ιf fra) (-(c : ℝ))) n (ιf fra) (c : ℝ) with hF2
  have hchi : pflow C1 fra = T.chi fa fra := (chi_eq_pflow hM T C1 hoff1 fra).symm
  have h2' := h2.congrκ (κ' := fun d => ((val d + c * T.chi fa fra d : ℤ) : ℝ))
    (fun d => by rw [hchi]; push_cast; ring)
  -- the values of the isolated node of the edge of `a`
  have hu1 : ιe a ∉ rootPath Fo n (ιf fa) := by
    rw [rootPath_rep hR hN.f_lt hN.e_lt hn fa]; exact not_mem_tpath_off hN haC le_rfl
  have hu2 : ιe a ∉ rootPath F1 n (ιf fra) := by
    rw [rootPath_rep h1 hN.f_lt hN.e_lt hn fra]; exact not_mem_tpath_off hN haC1 le_rfl
  have hu3 : ιe a ∉ rootPath (addPath F1 n (ιf fra) (-(c : ℝ))) n (ιf fra) := by
    rwa [rootPath_congr (Fo := F1) (Fo' := addPath F1 n (ιf fra) (-(c : ℝ))) rfl]
  have hag : Agree Fo F2 (ιe a) :=
    (agree_evert hu1).trans ((agree_addPath hu2 _).trans (agree_addPath2 hu3 _))
  have hv₁' : F2.val (ιe (M.rev a)) = v₁ := by rw [hN.e_rev, hag.2.1, hv₁]
  have hv₂' : F2.val2 (ιe (M.rev a)) = v₂ := by rw [hN.e_rev, hag.2.2, hv₂]
  -- the exchange
  have hhe : M.face (M.rev (M.rev a)) = C1.root := by rw [M.rev_rev]; rfl
  obtain ⟨hv3, hout3, h3, i3, a3⟩ := exchange_trep h2' i2.1 hN hn hz hhe hza hraC1
    (t₁ := wt a - φ a - c) (t₂ := wt (M.rev a) + φ a + c) hv₁' hv₂'
  set C3 := C1.hangRoot z (M.rev a) hz hhe hza with hC3
  set F3 := (runOpsE n F2 (exchangeOps ιf ιe C1 z (M.rev a) (wt a - φ a - c - v₁)
    (wt (M.rev a) + φ a + c - v₂))).1 with hF3
  -- `evert` at `fe`
  have h4 := evert_trep h3 hN hn fe
  have i4 := evert_iso h3 i3 hN hn fe
  -- the run
  have hrun3 : (runOpsE n Fo [.evert (ιf fa), .add (ιf fra) (-c), .add2 (ιf fra) c]).1 = F2 := by
    simp only [runOpsE, EOp.apply, hF2, hF1, Int.cast_neg]
  have hout0 : (runOpsE n Fo [.evert (ιf fa), .add (ιf fra) (-c), .add2 (ιf fra) c]).2 = [] := by
    simp [runOpsE, EOp.answer]
  have hrun : runOpsE n Fo (cotreeOps ιf ιe C a z fe c (wt a - φ a - c - v₁)
      (wt (M.rev a) + φ a + c - v₂)) = (evert F3 n (ιf fe), []) := by
    simp only [cotreeOps, runOpsE_append]
    simp only [runOpsE, EOp.apply, EOp.answer, Int.cast_neg, List.append_nil, List.nil_append,
      Prod.mk.injEq]
    exact ⟨rfl, hout3⟩
  rw [hrun]
  refine ⟨?_, rfl, C3.reroot fe, rfl, ?_, i4.1, fun u hu1 hu2 => ?_, ?_⟩
  · -- validity
    refine (validOpsE_append n _ _ _).2 ⟨(validOpsE_append n _ _ _).2
      ⟨⟨hN.f_lt _, hN.f_lt _, hN.f_lt _, trivial⟩, by rw [hrun3]; exact hv3⟩, ?_⟩
    rw [runOpsE_append, hrun3]
    exact ⟨hN.f_lt _, trivial⟩
  · -- the parent darts of the new cotree are off the new tree
    intro x hx hT'
    have hC3' : C3.InT ((C3.reroot fe).par x) := reroot_inT ((C3.reroot fe).inT_par hx)
    rcases reparent_inT hT' with hdb | hdb | ⟨w, hw, hwy, hdw⟩
    · -- the new parent dart `b`
      rcases hangRoot_inT hC3' with hd | hd | ⟨w', hw', hw'z, hd⟩
      · exact hbT (by rw [← hdb, hd]; exact T.inT_rev haT)
      · exact hbT (by rw [← hdb, hd, M.rev_rev]; exact haT)
      · refine hw'z (eq_of_edge hw' hz hd ?_)
        rcases hzb with h | h
        · exact Or.inl (by rw [hdb, h])
        · exact Or.inr (by rw [hdb, h, M.rev_rev])
    · have hb' : b = M.rev ((C3.reroot fe).par x) := by rw [hdb]; exact (M.rev_rev b).symm
      rcases hangRoot_inT hC3' with hd | hd | ⟨w', hw', hw'z, hd⟩
      · rw [hd, M.rev_rev] at hb'
        exact hbT (by rw [hb']; exact haT)
      · rw [hd, M.rev_rev] at hb'
        exact hbT (by rw [hb']; exact T.inT_rev haT)
      · refine hw'z (eq_of_edge hw' hz hd ?_)
        rcases hzb with h | h
        · exact Or.inr (by rw [hdb, h]; rfl)
        · exact Or.inl (by rw [hdb, h]; rfl)
    · rcases hangRoot_inT hC3' with hd | hd | ⟨w', hw', hw'z, hd⟩
      · refine hwy (eq_of_edge (C := T) hw hy hdw (Or.inr ?_))
        exact hd
      · refine hwy (eq_of_edge (C := T) hw hy hdw (Or.inl ?_))
        rw [hd, M.rev_rev]
      · exact not_inT_of_inT hoff1 ⟨w', hw', hd⟩ ⟨w, hw, hdw⟩
  · exact Agree.trans (i1.2 u hu1 hu2) (Agree.trans (i2.2 u hu1 hu2)
      (Agree.trans (a3 u hu1 hu2) (i4.2 u hu1 hu2)))
  · refine ⟨_, _, h4.congrκ fun d => ?_, fun Lo hLo x => ?_⟩
    · simp only [pivotVal]
      by_cases hd1 : d = a
      · rw [ite_eq_left hd1, ite_eq_right (by rw [hd1]; exact (M.rev_ne a).symm),
          ite_eq_left (by rw [hd1, M.rev_rev])]
      · by_cases hd2 : d = M.rev a
        · rw [ite_eq_right hd1, ite_eq_left hd2, ite_eq_left hd2]
        · rw [ite_eq_right hd1, ite_eq_right hd2, ite_eq_right hd2,
            ite_eq_right (fun h => hd1 (by rw [h, M.rev_rev]))]
    · have hl := hLo x
      have hc1 := le_abs_self (c : ℝ)
      have hc2 := neg_abs_le (c : ℝ)
      split_ifs <;> constructor <;> linarith

end Cotree

end Klein

end PlanarFlow
