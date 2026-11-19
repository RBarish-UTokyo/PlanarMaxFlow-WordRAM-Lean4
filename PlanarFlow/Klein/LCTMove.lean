module

public import PlanarFlow.Klein.LCTPivot
public import PlanarFlow.Klein.LCTQuery

/-!
# A move on the stored trees

* `dataRun_of_steps`: **a run on the data is determined by its selected darts**: trees and values
  that start from data compatible with the shortest-path tree of `u`, select at every step a dart
  of least value on the path of the cotree (with value below `L - 2B`), reparent its head on it
  (`T (i + 1)`, with the values `pivotVal` of `pivot_values`) and stop when the least value is at
  least `L - 2B`, form a run on the data (`DataRun`, so a run of the pivot loop by
  `dataRun_isRun`). The trees of the run are thus exactly the reparented trees, as stored by the
  operations of `PlanarFlow/Klein/LCTPivot.lean`.
* `Layout`, `Stored`: the two trees of a move stored in one forest on disjoint nodes (the
  spanning tree with the weights `φ`, a cotree rooted at the face `fe` with the values `val`, the
  values at the nodes of the faces at least `Lo`, all values integers).
* `stored_min2`: **`MINPATH` on the stored data** (the fields `sel`, `low`, `stop` of `DataRun`
  from the answer of `min2`).
* `pivot_stored`: **a pivot on the stored data**: sixteen valid operations, printing nothing,
  store the reparented tree with the values `pivotVal`.
* `rerootChild_stored`: between two moves, `evert` at the node of the next source re-roots the
  stored spanning tree at it (`rerootChild`, `PlanarFlow/Klein/Next.lean`); the reparenting of
  the next target that follows is a pivot (`pivot_stored`, with the value of `reparent_vinv`).
* `move_stored`: **a move on the stored data**: from stored data compatible with the
  shortest-path tree of `u`, `17 m + 1` valid operations (per pivot the query `min2` and the
  sixteen operations of the pivot, then a last `min2`) print the nodes of the selected darts
  (`minAns`) and a final `0`, and the trees and values stored along the way are those of a run on
  the data (`DataRun`); the values at the nodes of the faces stay above the threshold `L - 2B`
  (each pivot moves them by at most `driftK`, and there are at most `#V` pivots). The list of
  operations is adaptive: each pivot depends on the answer of the query before it; the theorem
  gives its existence and properties, not yet a machine program that computes it.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree

lemma _root_.PlanarFlow.STFlow.DTree.ext_of {D X Y : Type*} [Fintype D] [DecidableEq D]
    [Fintype Y] [DecidableEq Y] {N : CombMap D X Y} {T₁ T₂ : DTree N}
    (hr : T₁.root = T₂.root) (hp : T₁.par = T₂.par) : T₁ = T₂ := by
  cases T₁; cases T₂; cases hr; cases hp; rfl

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

/-! ### A run on the data from its selected darts -/

section Steps

variable {S : Finset D} {ℓ : D → ℤ} {u v : V} {φ wt : D → ℤ} {e : D}

local notation "𝒢" => pieceGraph M S ℓ

variable (M S) in
/-- The forests of the pivot loop along the selected darts. -/
noncomputable def selForest (P₀ : V → Option {d // d ∈ S}) (d : ℕ → D) :
    ℕ → V → Option {d // d ∈ S}
  | 0 => P₀
  | i + 1 => open Classical in
    if h : d i ∈ S then Function.update (selForest P₀ d i) (M.head (d i)) (some ⟨d i, h⟩)
    else selForest P₀ d i

/-- **A run on the data is determined by its selected darts**: from initial data compatible with
the shortest-path tree of `u`, the trees reparented along darts of least value on the path of the
cotree, with the values `pivotVal`, form a run on the data. -/
theorem dataRun_of_steps (hM : M.IsPlane) (H : MoveHyp 𝒢 u v) (hU : UniqTight 𝒢)
    (heS : e ∉ S) (hrS : M.rev e ∉ S) (hφ : ∀ d ∈ S, φ d = ℓ d) {W L : ℤ}
    (hW : ∀ d, |φ d| ≤ W) (hwt : ∀ d ∈ S, Reach 𝒢 v (M.tail d) → wt d = ℓ d)
    (hwL : ∀ d, (d ∈ S → ¬ Reach 𝒢 v (M.tail d)) → L ≤ wt d)
    (hL : ∀ d ∈ S, ℓ d + 4 * (Fintype.card V * W) < L)
    {T : ℕ → DTree M.dual} {val : ℕ → D → ℤ} {d : ℕ → D} {m : ℕ}
    (hC₀ : Compat (T 0) u v e (tpar 𝒢 u)) (hV₀ : VInv (T 0) φ wt (val 0))
    (hsel : ∀ i < m, (T i).chi (M.face e) (M.face (M.rev e)) (d i) = 1 ∧
      ∀ d', (T i).chi (M.face e) (M.face (M.rev e)) d' = 1 → val i (d i) ≤ val i d')
    (hlow : ∀ i < m, val i (d i) < L - 2 * (Fintype.card V * W))
    (hT : ∀ i < m, (T (i + 1)).root = (T i).root ∧
      (T (i + 1)).par = Function.update (T i).par (M.head (d i)) (d i))
    (hval : ∀ i < m, val (i + 1) = pivotVal (T i) φ wt (val i) (M.head (d i)) (val i (d i)))
    (hstop : ∀ d', (T m).chi (M.face e) (M.face (M.rev e)) d' = 1 →
      L - 2 * (Fintype.card V * W) ≤ val m d') :
    DataRun S ℓ u v φ wt e (Fintype.card V * W) L T val (selForest M S (tpar 𝒢 u) d) d m := by
  classical
  set B : ℤ := Fintype.card V * W with hBdef
  set P := selForest M S (tpar 𝒢 u) d with hPdef
  have hB : ∀ (T : DTree M.dual) x, |T.psum φ x| ≤ B := fun T x => abs_psum_le_mul T hW x
  have hP : ∀ i (h : d i ∈ S), P (i + 1) = Function.update (P i) (M.head (d i)) (some ⟨d i, h⟩) :=
    fun i h => by simp only [hPdef, selForest, dite_eq_left h]
  -- one step
  have step : ∀ i < m, RInv 𝒢 u v (P i) → Compat (T i) u v e (P i) →
      VInv (T i) φ wt (val i) → ∃ h : d i ∈ S,
        RInv 𝒢 u v (P (i + 1)) ∧ Compat (T (i + 1)) u v e (P (i + 1)) ∧
          VInv (T (i + 1)) φ wt (val (i + 1)) := by
    intro i hi hI hC hV
    obtain ⟨hc, hm⟩ := hsel i hi
    have helig : d i ∈ S ∧ Reach 𝒢 v (M.tail (d i)) := by
      by_contra hne
      have hnT : ¬ (T i).InT (d i) := fun h => by
        rw [((T i).chi_spec hM.dual _ _).2.2.1 _ h] at hc; exact absurd hc (by norm_num)
      have hw := hwL (d i) fun h1 h2 => hne ⟨h1, h2⟩
      have hB3 := abs_le.1 (hB (T i) (M.tail (d i)))
      have hB4 := abs_le.1 (hB (T i) (M.head (d i)))
      have hlt := hlow i hi
      rw [hV _ hnT] at hlt
      omega
    have hact := (ractive_iff_chi hM H hI hC heS hrS ⟨d i, helig.1⟩).2 ⟨helig.2, hc⟩
    obtain ⟨h, ha, hmin, -⟩ := minpath_spec hM H hI hC heS hrS hφ hV (hB (T i)) hwt hwL hL hc
      hm ⟨_, hact.2.1, hact.2.2⟩
    obtain ⟨hy, hna, hI', hC', hV'⟩ := pivot_values hM H hU hI hC heS hrS hφ hV hwt ha hmin
    have hTe : T (i + 1) = (T i).reparent (M.head (d i)) (d i) hy (dual_face_rev (d i)) hna :=
      DTree.ext_of (hT i hi).1 (hT i hi).2
    refine ⟨h, ?_, ?_, ?_⟩
    · rw [hP i h]; exact hI'
    · rw [hP i h, hTe]; exact hC'
    · rw [hTe, hval i hi]; exact hV'
  have key : ∀ i ≤ m, RInv 𝒢 u v (P i) ∧ Compat (T i) u v e (P i) ∧
      VInv (T i) φ wt (val i) := by
    intro i
    induction i with
    | zero => intro _; exact ⟨rInv_init H, hC₀, hV₀⟩
    | succ i ih =>
      intro hi
      obtain ⟨hI, hC, hV⟩ := ih (by omega)
      obtain ⟨-, hI', hC', hV'⟩ := step i (by omega) hI hC hV
      exact ⟨hI', hC', hV'⟩
  refine ⟨rfl, fun i hi => (key i hi).2.1, fun i hi => (key i hi).2.2, fun i _ x => hB _ x,
    hsel, hlow, fun i hi => ?_, hstop⟩
  obtain ⟨hI, hC, hV⟩ := key i hi.le
  obtain ⟨h, -⟩ := step i hi hI hC hV
  exact ⟨h, hP i h⟩

end Steps

/-! ### Integer values -/

/-- All the values of the forest are integers. -/
def IntF (Fo : Forest) : Prop := ∀ u, (∃ k : ℤ, Fo.val u = k) ∧ ∃ k : ℤ, Fo.val2 u = k

lemma intF_apply {n : ℕ} {Fo : Forest} (h : IntF Fo) (o : EOp) : IntF (o.apply n Fo) := by
  intro u
  obtain ⟨⟨k, hk⟩, ⟨k2, hk2⟩⟩ := h u
  cases o with
  | add v z =>
    refine ⟨?_, ⟨k2, hk2⟩⟩
    change ∃ j : ℤ, (if u ∈ rootPath Fo n v then Fo.val u + z else Fo.val u) = j
    split_ifs
    · exact ⟨k + z, by rw [hk]; push_cast; ring⟩
    · exact ⟨k, hk⟩
  | add2 v z =>
    refine ⟨⟨k, hk⟩, ?_⟩
    change ∃ j : ℤ, (if u ∈ rootPath Fo n v then Fo.val2 u + z else Fo.val2 u) = j
    split_ifs
    · exact ⟨k2 + z, by rw [hk2]; push_cast; ring⟩
    · exact ⟨k2, hk2⟩
  | evert v =>
    change (∃ j : ℤ, (if u ∈ rootPath Fo n v then Fo.val2 u else Fo.val u) = j) ∧
      ∃ j : ℤ, (if u ∈ rootPath Fo n v then Fo.val u else Fo.val2 u) = j
    split_ifs
    · exact ⟨⟨k2, hk2⟩, ⟨k, hk⟩⟩
    · exact ⟨⟨k, hk⟩, ⟨k2, hk2⟩⟩
  | link v w => exact ⟨⟨k, hk⟩, ⟨k2, hk2⟩⟩
  | cut v => exact ⟨⟨k, hk⟩, ⟨k2, hk2⟩⟩
  | min v z => exact ⟨⟨k, hk⟩, ⟨k2, hk2⟩⟩
  | min2 v z => exact ⟨⟨k, hk⟩, ⟨k2, hk2⟩⟩
  | sum v => exact ⟨⟨k, hk⟩, ⟨k2, hk2⟩⟩
  | parent v => exact ⟨⟨k, hk⟩, ⟨k2, hk2⟩⟩

lemma intF_runOpsE {n : ℕ} : ∀ (os : List EOp) {Fo : Forest}, IntF Fo →
    IntF (runOpsE n Fo os).1
  | [], _, h => h
  | o :: os, _, h => intF_runOpsE os (intF_apply h o)

/-! ### The stored data of a move -/

section Stored

variable (M) in
/-- **The layout of the nodes**: the spanning tree on the nodes `ιv` of the vertices and `ιg` of
its edges, the cotree on the nodes `ιf` of the faces and `ιe` of its edges, all distinct. -/
structure Layout (n : ℕ) (ιv : V → ℕ) (ιg : D → ℕ) (ιf : F → ℕ) (ιe : D → ℕ) : Prop where
  prim : Nodes n M.dual ιv ιg
  dual : Nodes n M ιf ιe
  hv : 2 * Fintype.card V ≤ n
  hf : 2 * Fintype.card F ≤ n
  vf : ∀ x y, ιv x ≠ ιf y
  ve : ∀ x d, ιv x ≠ ιe d
  gf : ∀ d y, ιg d ≠ ιf y
  ge : ∀ d d', ιg d ≠ ιe d'

variable (M) in
/-- **The stored data of a move**: the forest stores the spanning tree `T` with the values `φ` of
its parent darts (both values `0` at the nodes of the vertices), and a cotree of `T` rooted at
the face `fe` with the values `val` of the darts and values at least `Lo` at the nodes of the
faces; the nodes of the edges off the two trees are isolated, and all the values are
integers. -/
structure Stored (n : ℕ) (ιv : V → ℕ) (ιg : D → ℕ) (ιf : F → ℕ) (ιe : D → ℕ) (φ : D → ℤ)
    (fe : F) (Lo : ℝ) (Fo : Forest) (T : DTree M.dual) (val : D → ℤ) : Prop where
  tree : TRep n Fo T ιv ιg (fun d => (φ (M.rev d) : ℝ)) 0 0
  treeIso : Iso n Fo T ιg
  cot : ∃ (C : DTree M) (β β₂ : F → ℝ), C.root = fe ∧
    (∀ x, x ≠ C.root → ¬ T.InT (C.par x)) ∧ TRep n Fo C ιf ιe (fun d => (val d : ℝ)) β β₂ ∧
    Iso n Fo C ιe ∧ ∀ x, Lo ≤ β x ∧ Lo ≤ β₂ x
  int : IntF Fo

variable {n : ℕ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ}

/-- **The query `MINPATH` on the stored data**: the answer of `min2` at the node of the face of
the reverse of `e`, with the threshold `z ≤ Lo`, is either the node of the edge of a dart `d` of
least value on the path of the cotree from the face of `e` to the face of its reverse, with value
below `z` (oriented by the parent of its node), followed by `1`, or a word followed by `0`, when
all those darts have value at least `z`. -/
theorem stored_min2 (hM : M.IsPlane) (hL : Layout M n ιv ιg ιf ιe) {φ : D → ℤ} {e : D}
    {Lo : ℝ} {Fo : Forest} {T : DTree M.dual} {val : D → ℤ}
    (hS : Stored M n ιv ιg ιf ιe φ (M.face e) Lo Fo T val) {z : ℤ} (hz : (z : ℝ) ≤ Lo) :
    (∃ d, (EOp.min2 (ιf (M.face (M.rev e))) z).answer n Fo = [ιe d, 1] ∧
        Fo.par (ιe d) = ιf (M.face d) ∧ T.chi (M.face e) (M.face (M.rev e)) d = 1 ∧
        val d < z ∧ ∀ d', T.chi (M.face e) (M.face (M.rev e)) d' = 1 → val d ≤ val d') ∨
      (∃ w, (EOp.min2 (ιf (M.face (M.rev e))) z).answer n Fo = [w, 0] ∧
        ∀ d', T.chi (M.face e) (M.face (M.rev e)) d' = 1 → z ≤ val d') := by
  obtain ⟨C, β, β₂, hroot, hoff, hR, -, hLo⟩ := hS.cot
  have h := eop_min2_answer hM hoff hR hL.dual.f_lt hL.dual.e_lt hL.hf
    (fun y => hz.trans (hLo y).2) (M.face (M.rev e))
  rw [hroot] at h
  exact h

/-- **A pivot on the stored data** (the article's Section 3.2, on the dynamic trees): the
operations `cotreeOps` (on the cotree) and `reparentOps` (on the spanning tree), sixteen in all,
are valid, print nothing, and store the reparented tree `T.reparent y b` with the values
`pivotVal T φ wt val y c` of `reparent_vinv`; the values at the nodes of the faces move by at
most `|c|`. -/
theorem pivot_stored (hM : M.IsPlane) (hL : Layout M n ιv ιg ιf ιe) {φ : D → ℤ} {fe : F}
    {Lo : ℝ} {Fo : Forest} {T : DTree M.dual} {val : D → ℤ}
    (hS : Stored M n ιv ιg ιf ιe φ fe Lo Fo T val) {y : V} (hy : y ≠ T.root) {b : D}
    (hby : M.dual.face (M.dual.rev b) = y) (hna : ¬ T.Anc y (M.dual.face b)) (hbT : ¬ T.InT b)
    (wt : D → ℤ) (c : ℤ) :
    ∃ os : List EOp, os.length = 16 ∧ ValidOpsE n Fo os ∧ (runOpsE n Fo os).2 = [] ∧
      Stored M n ιv ιg ιf ιe φ fe (Lo - |(c : ℝ)|) (runOpsE n Fo os).1
        (T.reparent y b hy hby hna) (pivotVal T φ wt val y c) := by
  classical
  obtain ⟨C, β, β₂, hroot, hoff, hRc, hIc, hLo⟩ := hS.cot
  have hRt := hS.tree
  obtain ⟨z, hz, hzb, hza⟩ := exists_cut_face hM hoff hy hby hna hbT
  obtain ⟨⟨v₁, hv₁⟩, ⟨v₂, hv₂⟩⟩ := hS.int (ιe (T.par y))
  set os1 := cotreeOps ιf ιe C (T.par y) z fe c (wt (T.par y) - φ (T.par y) - c - v₁)
      (wt (M.rev (T.par y)) + φ (T.par y) + c - v₂) with hos1
  obtain ⟨hval1, hout1, C', hroot', hoff', hI', hag1, β', β₂', hR', hLo'⟩ :=
    cotreePivot_trep hM hoff hL.dual hL.hf hRc hIc hy hby hna hbT hz hzb hza fe φ wt c hv₁ hv₂
      hos1
  set F1 := (runOpsE n Fo os1).1 with hF1
  -- the spanning tree is kept by the pivot on the cotree
  have hRt1 := hRt.congr (fun x => hag1 _ (hL.vf x) (hL.ve x))
    (fun d => hag1 _ (hL.gf d) (hL.ge d))
  have hIt1 := hS.treeIso.congr (fun d => hag1 _ (hL.gf d) (hL.ge d))
  have hint1 := intF_runOpsE (n := n) os1 hS.int
  obtain ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩⟩ := hint1 (ιg b)
  have hoffb : ∀ x, x ≠ T.root → b ≠ T.par x ∧ b ≠ M.dual.rev (T.par x) :=
    off_iff_not_inT.2 hbT
  obtain ⟨hval2, hout2, hR2, hI2, hag2⟩ := reparent_trep hRt1 hIt1 hL.prim hL.hv hy hby hna
    hoffb (t₁ := φ b) (t₂ := φ (M.rev b)) hw₁ hw₂
  refine ⟨os1 ++ reparentOps ιv ιg T y b (φ b - w₁) (φ (M.rev b) - w₂), ?_,
    (validOpsE_append n _ _ _).2 ⟨hval1, hval2⟩, ?_, ?_⟩
  · simp [hos1, cotreeOps, exchangeOps, reparentOps]
  · rw [runOpsE_append, hout1, hout2]; rfl
  · rw [runOpsE_append]
    refine ⟨hR2.congrκ fun d => ?_, hI2, ⟨C', β', β₂', hroot', hoff',
      hR'.congr (fun x => hag2 _ (fun v => (hL.vf v x).symm) (fun d => (hL.gf d x).symm))
        (fun d => hag2 _ (fun v => (hL.ve v d).symm) (fun d' => (hL.ge d' d).symm)),
      hI'.congr (fun d => hag2 _ (fun v => (hL.ve v d).symm) (fun d' => (hL.ge d' d).symm)),
      hLo' Lo hLo⟩, intF_runOpsE _ hint1⟩
    by_cases h1 : d = b
    · rw [ite_eq_left h1, h1]
    · rw [ite_eq_right h1]
      by_cases h2 : d = M.dual.rev b
      · rw [ite_eq_left h2, h2]
        show ((φ b : ℤ) : ℝ) = ((φ (M.rev (M.rev b)) : ℤ) : ℝ)
        rw [M.rev_rev]
      · rw [ite_eq_right h2]

/-- Re-rooting the spanning tree at a child of the root is re-rooting it. -/
lemma rerootChild_eq_reroot (T : DTree M.dual) {v : V} (hv : v ≠ T.root)
    (hup : M.tail (T.par v) = T.root) : rerootChild T v hv hup = T.reroot v := by
  have hupv : T.up v = T.root := by rw [T.up_of_ne hv]; exact hup
  have hd : T.depth v = 1 := by rw [T.depth_up hv, hupv, T.depth_root]
  refine DTree.ext_of rfl (funext fun x => ?_)
  rw [reroot_par]
  by_cases hx : x = T.root
  · subst hx
    have h := rerootPar_anc T (w := v) (i := 0) (by omega)
    rw [Function.iterate_one, hupv, Function.iterate_zero_apply] at h
    rw [h, rerootChild_par_root]; rfl
  · rw [rerootChild_par T hv hup x hx, rerootPar_not]
    rintro ⟨i, hi, hix⟩
    obtain rfl : i = 0 := by omega
    rw [Function.iterate_one, hupv] at hix
    exact hx hix.symm

/-- **Re-rooting the spanning tree at the next source** (a child of the root, between two moves):
`evert` at its node is valid, prints nothing, and stores `rerootChild`, with the same cotree and
values (`rerootChild_vinv`: with weights `0` on the edge to the new root, the values keep the
invariant). -/
theorem rerootChild_stored (hL : Layout M n ιv ιg ιf ιe) {φ : D → ℤ} {fe : F} {Lo : ℝ}
    {Fo : Forest} {T : DTree M.dual} {val : D → ℤ}
    (hS : Stored M n ιv ιg ιf ιe φ fe Lo Fo T val) {v : V} (hv : v ≠ T.root)
    (hup : M.tail (T.par v) = T.root) :
    ValidOpsE n Fo [.evert (ιv v)] ∧ (runOpsE n Fo [.evert (ιv v)]).2 = [] ∧
      Stored M n ιv ιg ιf ιe φ fe Lo (runOpsE n Fo [.evert (ιv v)]).1
        (rerootChild T v hv hup) val := by
  have hrun : runOpsE n Fo [.evert (ιv v)] = (evert Fo n (ιv v), []) := rfl
  have hint := intF_runOpsE (n := n) [.evert (ιv v)] hS.int
  rw [hrun] at hint ⊢
  rw [rerootChild_eq_reroot]
  obtain ⟨C, β, β₂, hroot, hoff, hRc, hIc, hLo⟩ := hS.cot
  have h1 := evert_trep hS.tree hL.prim hL.hv v
  have i1 := evert_iso hS.tree hS.treeIso hL.prim hL.hv v
  have hag : ∀ u, (∀ x, u ≠ ιv x) → (∀ d, u ≠ ιg d) → Agree Fo (evert Fo n (ιv v)) u := i1.2
  refine ⟨⟨hL.prim.f_lt v, trivial⟩, rfl, h1.congrβ (fun _ => by simp) (fun _ => by simp),
    i1.1, ⟨C, β, β₂, hroot, fun x hx h => hoff x hx (reroot_inT h), ?_, ?_, hLo⟩, hint⟩
  · exact hRc.congr (fun x => hag _ (fun v => (hL.vf v x).symm) (fun d => (hL.gf d x).symm))
      (fun d => hag _ (fun v => (hL.ve v d).symm) (fun d' => (hL.ge d' d).symm))
  · exact hIc.congr (fun d => hag _ (fun v => (hL.ve v d).symm) (fun d' => (hL.ge d' d).symm))

end Stored

/-! ### A move on the stored data -/

section MoveStored

variable {S : Finset D} {ℓ : D → ℤ} {u v : V} {φ wt : D → ℤ} {e : D}
variable {n : ℕ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ}

local notation "𝒢" => pieceGraph M S ℓ

variable (ιe) in
/-- The words printed by the queries `min2` of `m` pivots on the darts `d 0, d 1, …`. -/
def minAns : (ℕ → D) → ℕ → List ℕ
  | _, 0 => []
  | d, m + 1 => ιe (d 0) :: 1 :: minAns (fun i => d (i + 1)) m

variable (M S ℓ u v) in
open Classical in
/-- The red vertices of the move for the forest `P` of the pivot loop. -/
noncomputable def redSet (P : V → Option {d // d ∈ S}) : Finset V :=
  (moveSet 𝒢 u v).filter fun x => ¬ Hang 𝒢 P v x

/-- The bound of the shift of the values at the nodes of the faces in one pivot. -/
def driftK (L W : ℤ) (nV : ℕ) : ℤ := |L| + |W| + 2 * |(nV : ℤ) * W|

/-- **A move on the stored data**: from stored data compatible with the shortest-path tree of `u`
(with the values at the nodes of the faces at least `L - 2B` plus `#V` times the drift bound),
there are `m` pivots and a list of `17 m + 1` valid operations — per pivot the query `min2` at the
node of the face of the reverse of `e` with the threshold `L - 2B` and the sixteen operations of
`pivot_stored`, then a last query `min2` — whose printed words are the nodes of the edges of the
selected darts, each followed by `1`, then a word followed by `0`; the trees and values stored
along the way form a run on the data (`DataRun`, each tree the reparented previous one), and the
final forest stores the last tree and values, with the values at the nodes of the faces lowered by
at most `#V` times the drift bound. -/
theorem move_stored (hM : M.IsPlane) (H : MoveHyp 𝒢 u v) (hU : UniqTight 𝒢)
    (heS : e ∉ S) (hrS : M.rev e ∉ S) (hφ : ∀ d ∈ S, φ d = ℓ d) {W L : ℤ}
    (hW : ∀ d, |φ d| ≤ W) (hwt : ∀ d ∈ S, Reach 𝒢 v (M.tail d) → wt d = ℓ d)
    (hwL : ∀ d, (d ∈ S → ¬ Reach 𝒢 v (M.tail d)) → L ≤ wt d)
    (hL : ∀ d ∈ S, ℓ d + 4 * (Fintype.card V * W) < L) (hLay : Layout M n ιv ιg ιf ιe)
    {T₀ : DTree M.dual} {val₀ : D → ℤ} {Fo₀ : Forest} {Lo₀ : ℝ}
    (hC₀ : Compat T₀ u v e (tpar 𝒢 u)) (hV₀ : VInv T₀ φ wt val₀)
    (hS₀ : Stored M n ιv ιg ιf ιe φ (M.face e) Lo₀ Fo₀ T₀ val₀)
    (hLo : ((L - 2 * (Fintype.card V * W) : ℤ) : ℝ) +
      Fintype.card V * (driftK L W (Fintype.card V) : ℝ) ≤ Lo₀) :
    ∃ (T : ℕ → DTree M.dual) (val : ℕ → D → ℤ) (d : ℕ → D) (m : ℕ) (os : List EOp) (w : ℕ)
      (Lo : ℝ), T 0 = T₀ ∧ val 0 = val₀ ∧
      DataRun S ℓ u v φ wt e (Fintype.card V * W) L T val (selForest M S (tpar 𝒢 u) d) d m ∧
      (∀ i < m, (T (i + 1)).root = (T i).root ∧
        (T (i + 1)).par = Function.update (T i).par (M.head (d i)) (d i)) ∧
      os.length = 17 * m + 1 ∧ ValidOpsE n Fo₀ os ∧
      (runOpsE n Fo₀ os).2 = minAns ιe d m ++ [w, 0] ∧
      Stored M n ιv ιg ιf ιe φ (M.face e) Lo (runOpsE n Fo₀ os).1 (T m) (val m) ∧
      Lo₀ - Fintype.card V * (driftK L W (Fintype.card V) : ℝ) ≤ Lo := by
  classical
  set B : ℤ := Fintype.card V * W with hBdef
  set z : ℤ := L - 2 * B with hz
  set K : ℤ := driftK L W (Fintype.card V) with hK
  have hB : ∀ (T : DTree M.dual) x, |T.psum φ x| ≤ B := fun T x => abs_psum_le_mul T hW x
  have hK0 : (0 : ℝ) ≤ K := by
    have : (0 : ℤ) ≤ K := by
      simp only [hK, driftK]; positivity
    exact_mod_cast this
  -- the query
  set q := EOp.min2 (ιf (M.face (M.rev e))) z with hq
  have hvq : ∀ Fo : Forest, q.apply n Fo = Fo := fun _ => rfl
  -- the loop, by induction on the number of red vertices
  have claim : ∀ r : ℕ, ∀ (T₀ : DTree M.dual) (val₀ : D → ℤ) (P₀ : V → Option {d // d ∈ S})
      (Fo₀ : Forest) (Lo₀ : ℝ), RInv 𝒢 u v P₀ → Compat T₀ u v e P₀ → VInv T₀ φ wt val₀ →
      Stored M n ιv ιg ιf ιe φ (M.face e) Lo₀ Fo₀ T₀ val₀ → (redSet M S ℓ u v P₀).card = r →
      (z : ℝ) + r * K ≤ Lo₀ →
      ∃ (T : ℕ → DTree M.dual) (val : ℕ → D → ℤ) (d : ℕ → D) (m : ℕ) (os : List EOp) (w : ℕ)
        (Lo : ℝ), T 0 = T₀ ∧ val 0 = val₀ ∧
        (∀ i < m, (T i).chi (M.face e) (M.face (M.rev e)) (d i) = 1 ∧
          ∀ d', (T i).chi (M.face e) (M.face (M.rev e)) d' = 1 → val i (d i) ≤ val i d') ∧
        (∀ i < m, val i (d i) < z) ∧
        (∀ i < m, (T (i + 1)).root = (T i).root ∧
          (T (i + 1)).par = Function.update (T i).par (M.head (d i)) (d i)) ∧
        (∀ i < m, val (i + 1) = pivotVal (T i) φ wt (val i) (M.head (d i)) (val i (d i))) ∧
        (∀ d', (T m).chi (M.face e) (M.face (M.rev e)) d' = 1 → z ≤ val m d') ∧
        os.length = 17 * m + 1 ∧ ValidOpsE n Fo₀ os ∧
        (runOpsE n Fo₀ os).2 = minAns ιe d m ++ [w, 0] ∧
        Stored M n ιv ιg ιf ιe φ (M.face e) Lo (runOpsE n Fo₀ os).1 (T m) (val m) ∧
        Lo₀ - r * K ≤ Lo := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
    intro T₀ val₀ P₀ Fo₀ Lo₀ hI hC hV hS hr hLo
    have hzLo : (z : ℝ) ≤ Lo₀ := by
      have : (0 : ℝ) ≤ r * K := mul_nonneg (Nat.cast_nonneg _) hK0
      linarith
    have hvq0 : ValidOpsE n Fo₀ [q] := ⟨hLay.dual.f_lt _, trivial⟩
    rcases stored_min2 hM hLay hS hzLo with ⟨d₀, hans, -, hd₀, hlt, hmin⟩ | ⟨w, hans, hstop⟩
    · -- a pivot on the selected dart
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
      -- the drift
      have hcK : |((val₀ d₀ : ℤ) : ℝ)| ≤ K := by
        have hc : |val₀ d₀| ≤ K := by
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
          simp only [hK, driftK]
          rw [← hBdef]
          exact abs_le.2 ⟨by linarith, by linarith⟩
        rw [← Int.cast_abs]; exact_mod_cast hc
      obtain ⟨os1, hlen1, hv1, hout1, hS1⟩ :=
        pivot_stored hM hLay hS hy (dual_face_rev d₀) hna hnT wt (val₀ d₀)
      have hLo1 : (z : ℝ) + ((redSet M S ℓ u v (Function.update P₀ (M.head d₀)
          (some ⟨d₀, h⟩))).card : ℕ) * K ≤ Lo₀ - |((val₀ d₀ : ℤ) : ℝ)| := by
        have h1 : (((redSet M S ℓ u v (Function.update P₀ (M.head d₀)
            (some ⟨d₀, h⟩))).card : ℕ) : ℝ) + 1 ≤ r := by
          rw [← hr]; exact_mod_cast hred
        nlinarith
      obtain ⟨T, val, d, m, os, w, Lo, hT0, hv0, hsel, hlow, hTs, hval, hstop, hlen, hvalid,
          hout, hSf, hLoF⟩ := ih _ (hr ▸ hred) _ _ _ _ _ hI' hC' hV' hS1 rfl hLo1
      refine ⟨fun i => match i with | 0 => T₀ | i + 1 => T i,
        fun i => match i with | 0 => val₀ | i + 1 => val i,
        fun i => match i with | 0 => d₀ | i + 1 => d i, m + 1, [q] ++ os1 ++ os, w, Lo,
        rfl, rfl, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, hstop, ?_,
        ?_, ?_, ?_, ?_⟩
      · rcases i with _ | i
        · exact ⟨hd₀, hmin⟩
        · exact hsel i (by omega)
      · rcases i with _ | i
        · exact hlt
        · exact hlow i (by omega)
      · rcases i with _ | i
        · show (T 0).root = T₀.root ∧ (T 0).par = Function.update T₀.par (M.head d₀) d₀
          rw [hT0]; exact ⟨rfl, rfl⟩
        · exact hTs i (by omega)
      · rcases i with _ | i
        · exact hv0
        · exact hval i (by omega)
      · simp only [List.length_append, hlen1, hlen, List.length_singleton]; ring
      · refine (validOpsE_append n _ _ _).2 ⟨(validOpsE_append n _ _ _).2 ⟨hvq0, ?_⟩, ?_⟩
        · simp only [runOpsE, hvq]; exact hv1
        · rw [runOpsE_append]; simp only [runOpsE, hvq]; exact hvalid
      · rw [runOpsE_append, runOpsE_append]
        simp only [runOpsE, hvq, List.append_nil]
        rw [hans, hout1, hout]
        rfl
      · rw [runOpsE_append, runOpsE_append]
        simp only [runOpsE, hvq]
        exact hSf
      · have h1 : (((redSet M S ℓ u v (Function.update P₀ (M.head d₀)
            (some ⟨d₀, h⟩))).card : ℕ) : ℝ) + 1 ≤ r := by
          rw [← hr]; exact_mod_cast hred
        nlinarith
    · -- the end of the move
      refine ⟨fun _ => T₀, fun _ => val₀, fun _ => e, 0, [q], w, Lo₀, rfl, rfl,
        fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega),
        fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega), hstop, rfl, hvq0,
        ?_, ?_, ?_⟩
      · simp only [runOpsE, List.append_nil]; rw [hans]; rfl
      · simp only [runOpsE, hvq]; exact hS
      · have : (0 : ℝ) ≤ r * K := mul_nonneg (Nat.cast_nonneg _) hK0
        linarith
  have hr0 : (redSet M S ℓ u v (tpar 𝒢 u)).card ≤ Fintype.card V := card_le_univ _
  have hr0' : (((redSet M S ℓ u v (tpar 𝒢 u)).card : ℕ) : ℝ) ≤ Fintype.card V := by
    exact_mod_cast hr0
  have h2 := mul_le_mul_of_nonneg_right hr0' hK0
  obtain ⟨T, val, d, m, os, w, Lo, hT0, hv0, hsel, hlow, hTs, hval, hstop, hlen, hvalid, hout,
      hSf, hLoF⟩ := claim _ T₀ val₀ _ Fo₀ Lo₀ (rInv_init H) hC₀ hV₀ hS₀ rfl (by
    have h3 : ((L - 2 * (Fintype.card V * W) : ℤ) : ℝ) = (z : ℝ) := rfl
    linarith)
  refine ⟨T, val, d, m, os, w, Lo, hT0, hv0, ?_, hTs, hlen, hvalid, hout, hSf, by linarith⟩
  subst hT0 hv0
  exact dataRun_of_steps hM H hU heS hrS hφ hW hwt hwL hL hC₀ hV₀ hsel hlow hTs hval hstop

end MoveStored

end Klein

end PlanarFlow
