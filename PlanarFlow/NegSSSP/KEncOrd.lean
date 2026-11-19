module

public import PlanarFlow.NegSSSP.KEncOut

/-!
# The depth orders of the one-face encoding, on the machine

The encoding of a one-face instance (`Klein.KVal`, `Klein.KInit`) holds the initial spanning
tree `T` and cotree `C` with orders (`Klein.Orders`): a list `fs` of all the nodes of the tree,
and a list `ys` of all the nodes but the root **by nondecreasing depth**, with the words
`ιv fs[i]` and `σ (par ys[i])` and the two lengths. Here a program writes them from the parent
darts of a tree, natural words only:

* `tbq`: the queue of a breadth-first search of a rooted tree given by parent pointers `pn`
  (the kept nodes `kf v ≠ 0`), children by increasing number (`tch`); `TQ`: its invariant;
  `tq_orders`: **the queue is a depth order** (`Klein.Orders` for `fs` all the nodes and `ys`
  the queue without its root).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge

/-! ### The queue of a tree search -/

/-- The children of `u` among the nodes `< n`: the kept nodes `v` with parent `pn v = u`, by
increasing number. -/
def tch (n : ℕ) (pn kf : ℕ → ℕ) (u : ℕ) : List ℕ :=
  (List.range n).filter fun v => decide (kf v ≠ 0 ∧ pn v = u)

/-- The queue of the search after `k` nodes are processed: the root, then the children of the
nodes of the queue, in order. -/
def tbq (n r : ℕ) (pn kf : ℕ → ℕ) : ℕ → List ℕ
  | 0 => [r]
  | k + 1 => tbq n r pn kf k ++ tch n pn kf ((tbq n r pn kf k).getD k 0)

/-- **The invariant of the search** after `k` nodes processed: the queue `q` starts with the
root, has distinct nodes `< n`, every node after the root is kept, with its parent at an earlier
processed position `a j < k` (`a` nondecreasing), and the children of the processed nodes are
queued. -/
structure TQ (n r : ℕ) (pn kf : ℕ → ℕ) (k : ℕ) (q : List ℕ) : Prop where
  hd : q.getD 0 0 = r
  pos : 0 < q.length
  nd : q.Nodup
  lt : ∀ v ∈ q, v < n
  kle : k ≤ q.length
  par : ∃ a : ℕ → ℕ, (∀ j, 0 < j → j < q.length → a j < j ∧ a j < k ∧ kf (q.getD j 0) ≠ 0 ∧
      pn (q.getD j 0) = q.getD (a j) 0) ∧
    ∀ j j', 0 < j → j ≤ j' → j' < q.length → a j ≤ a j'
  cl : ∀ p < k, ∀ v ∈ tch n pn kf (q.getD p 0), v ∈ q

variable {n r : ℕ} {pn kf : ℕ → ℕ}

lemma mem_tch {u v : ℕ} : v ∈ tch n pn kf u ↔ v < n ∧ kf v ≠ 0 ∧ pn v = u := by
  simp [tch]

lemma tch_nodup (u : ℕ) : (tch n pn kf u).Nodup := List.nodup_range.filter _

lemma tq_zero (hr : r < n) : TQ n r pn kf 0 [r] :=
  ⟨rfl, by simp, List.nodup_singleton r, fun v hv => by simp at hv; omega, by simp,
    ⟨fun _ => 0, fun j hj hj' => by simp at hj'; omega, fun j j' hj _ hj' => by simp at hj'; omega⟩,
    fun p hp => by omega⟩

lemma TQ.length_le {k : ℕ} {q : List ℕ} (h : TQ n r pn kf k q) : q.length ≤ n := by
  have := (List.toFinset_card_of_nodup h.nd).symm
  rw [this]
  calc q.toFinset.card ≤ (Finset.range n).card :=
        Finset.card_le_card fun v hv => Finset.mem_range.2 (h.lt v (List.mem_toFinset.1 hv))
    _ = n := Finset.card_range n

lemma getD_mem {q : List ℕ} {j : ℕ} (hj : j < q.length) : q.getD j 0 ∈ q := by
  rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj

/-- **One step of the search**: the children of the node at position `k` appended. -/
lemma TQ.step (hkr : kf r = 0) {k : ℕ} {q : List ℕ} (h : TQ n r pn kf k q) (hk : k < q.length) :
    TQ n r pn kf (k + 1) (q ++ tch n pn kf (q.getD k 0)) := by
  obtain ⟨a, ha, hmono⟩ := h.par
  have hga : ∀ j, j < q.length → (q ++ tch n pn kf (q.getD k 0)).getD j 0 = q.getD j 0 :=
    fun j hj => List.getD_append _ _ _ _ hj
  have hdisj : ∀ v ∈ tch n pn kf (q.getD k 0), v ∉ q := by
    intro v hv hvq
    obtain ⟨-, hkv, hpv⟩ := mem_tch.1 hv
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hvq
    have hj0 : 0 < j := by
      rcases Nat.eq_zero_or_pos j with rfl | h0
      · have : q[0] = r := by rw [← List.getD_eq_getElem _ 0 hj]; exact h.hd
        rw [this] at hkv; exact absurd hkr hkv
      · exact h0
    obtain ⟨h1, h2, -, h4⟩ := ha j hj0 hj
    rw [List.getD_eq_getElem _ _ hj] at h4
    rw [h4] at hpv
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hk] at hpv
    have := (List.Nodup.getElem_inj_iff h.nd).1 hpv
    omega
  refine ⟨?_, by simp; omega, ?_, fun v hv => ?_, ?_, ⟨fun j => if j < q.length then a j else k,
    fun j hj hj' => ?_, fun j j' hj hjj hj' => ?_⟩, fun p hp v hv => ?_⟩
  · rw [hga 0 h.pos]; exact h.hd
  · exact List.nodup_append.2 ⟨h.nd, tch_nodup _, fun x hx y hy hxy => hdisj y hy (hxy ▸ hx)⟩
  · rcases List.mem_append.1 hv with hv | hv
    · exact h.lt v hv
    · exact (mem_tch.1 hv).1
  · simp; omega
  · by_cases hjq : j < q.length
    · simp only [hjq, ↓reduceIte]
      obtain ⟨h1, h2, h3, h4⟩ := ha j hj hjq
      rw [hga j hjq, hga (a j) (by omega)]
      exact ⟨h1, by omega, h3, h4⟩
    · simp only [hjq, ↓reduceIte]
      have hj2 : j - q.length < (tch n pn kf (q.getD k 0)).length := by
        simp only [List.length_append] at hj'; omega
      have e : (q ++ tch n pn kf (q.getD k 0)).getD j 0 =
          (tch n pn kf (q.getD k 0)).getD (j - q.length) 0 :=
        List.getD_append_right _ _ _ _ (by omega)
      have hm := mem_tch.1 (getD_mem hj2)
      rw [e, hga k hk]
      exact ⟨by omega, by omega, hm.2.1, hm.2.2⟩
  · by_cases hjq : j < q.length
    · by_cases hjq' : j' < q.length
      · simp only [hjq, hjq', ↓reduceIte]; exact hmono j j' hj hjj hjq'
      · simp only [hjq, hjq', ↓reduceIte]; exact (ha j hj hjq).2.1.le
    · simp only [hjq, show ¬ j' < q.length by omega, ↓reduceIte, le_refl]
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
    · rw [hga p (by omega)] at hv
      exact List.mem_append_left _ (h.cl p hp v hv)
    · rw [hga p hk] at hv
      exact List.mem_append_right _ hv

/-! ### The queue of a tree is a depth order -/

section Tree

open STFlow

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype F] [DecidableEq F]
  {M : CombMap D V F}

/-- The node numbered `v` (any node above `n`). -/
def tinv {n : ℕ} (τ : F ≃ Fin n) (y₀ : F) (v : ℕ) : F := if h : v < n then τ.symm ⟨v, h⟩ else y₀

lemma tinv_tau {n : ℕ} (τ : F ≃ Fin n) (y₀ y : F) : tinv τ y₀ (τ y) = y := by
  simp [tinv]

lemma tau_tinv {n : ℕ} (τ : F ≃ Fin n) (y₀ : F) {v : ℕ} (hv : v < n) : (τ (tinv τ y₀ v) : ℕ) = v := by
  simp [tinv, hv]

/-- The hypotheses on the data of a tree `C`, its nodes numbered by `τ`: the root numbered `r`,
the parent of a node `pn`, the kept nodes `kf ≠ 0` all but the root. -/
structure TreeData (C : DTree M) {n : ℕ} (τ : F ≃ Fin n) (r : ℕ) (pn kf : ℕ → ℕ) : Prop where
  root : r = τ C.root
  par : ∀ y, y ≠ C.root → pn (τ y) = τ (C.up y)
  kf : ∀ y, kf (τ y) = 0 ↔ y = C.root

variable {C : DTree M} {τ : F ≃ Fin n}

/-- **The finished search queues every node.** -/
theorem TQ.mem_all (hT : TreeData C τ r pn kf) {q : List ℕ} (h : TQ n r pn kf q.length q)
    (y : F) : (τ y : ℕ) ∈ q := by
  suffices H : ∀ m y, C.depth y = m → (τ y : ℕ) ∈ q from H _ y rfl
  intro m
  induction m with
  | zero =>
    intro y hy
    have : y = C.root := by have := C.iterate_depth y; rw [hy] at this; exact this
    rw [this, ← hT.root, ← h.hd]
    exact getD_mem h.pos
  | succ m ih =>
    intro y hy
    have hyr : y ≠ C.root := by rintro rfl; rw [C.depth_root] at hy; omega
    have hu : C.depth (C.up y) = m := by have := C.depth_up hyr; omega
    obtain ⟨p, hp, hpe⟩ := List.getElem_of_mem (ih _ hu)
    refine h.cl p hp _ (mem_tch.2 ⟨(τ y).2, fun h0 => hyr ((hT.kf y).1 h0), ?_⟩)
    rw [hT.par y hyr, List.getD_eq_getElem _ _ hp, hpe]

theorem TQ.length_eq (hT : TreeData C τ r pn kf) {q : List ℕ} (h : TQ n r pn kf q.length q) :
    q.length = n := by
  refine le_antisymm h.length_le ?_
  rw [← List.toFinset_card_of_nodup h.nd]
  calc n = (Finset.range n).card := (Finset.card_range n).symm
    _ ≤ q.toFinset.card := Finset.card_le_card fun v hv => by
        have hv' := Finset.mem_range.1 hv
        have := h.mem_all hT (τ.symm ⟨v, hv'⟩)
        rw [Equiv.apply_symm_apply] at this
        exact List.mem_toFinset.2 this

/-- **The queue is by nondecreasing depth.** -/
theorem TQ.depth_mono (hT : TreeData C τ r pn kf) {k : ℕ} {q : List ℕ} (h : TQ n r pn kf k q) :
    ∀ j, j < q.length → ∀ i ≤ j,
      C.depth (tinv τ C.root (q.getD i 0)) ≤ C.depth (tinv τ C.root (q.getD j 0)) := by
  obtain ⟨a, ha, hmono⟩ := h.par
  have hstep : ∀ j, 0 < j → j < q.length →
      C.depth (tinv τ C.root (q.getD j 0)) = C.depth (tinv τ C.root (q.getD (a j) 0)) + 1 := by
    intro j hj hj'
    obtain ⟨h1, -, h3, h4⟩ := ha j hj hj'
    have hlt : q.getD j 0 < n := h.lt _ (getD_mem hj')
    set y := tinv τ C.root (q.getD j 0) with hy
    have hτ : (τ y : ℕ) = q.getD j 0 := tau_tinv τ C.root hlt
    have hyr : y ≠ C.root := fun e => h3 (by rw [← hτ]; exact (hT.kf y).2 e)
    have hup : C.up y = tinv τ C.root (q.getD (a j) 0) := by
      have := hT.par y hyr
      rw [hτ, h4] at this
      rw [this, tinv_tau]
    rw [C.depth_up hyr, hup]
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj i hij
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [h.hd, hT.root, tinv_tau, C.depth_root]; exact Nat.zero_le _
    · have hj0 : 0 < j := by omega
      rw [hstep i hi (by omega), hstep j hj0 hj]
      have := ih (a j) (ha j hj0 hj).1 (by have := (ha j hj0 hj).1; omega) (a i)
        (hmono i j hi hij hj)
      omega

/-- **The orders of a tree from the finished search**: all the nodes in the order of their
numbers, and the queue without its root, `Klein.Orders`. -/
theorem TQ.orders (hT : TreeData C τ r pn kf) {q : List ℕ} (h : TQ n r pn kf q.length q) :
    Klein.Orders C ((List.finRange n).map τ.symm) (q.tail.map (tinv τ C.root)) := by
  have hlen := h.length_eq hT
  have hq0 : ∀ v ∈ q.tail, v < n := fun v hv => h.lt v (List.mem_of_mem_tail hv)
  have htail : ∀ i (hi : i < q.tail.length), q.tail[i] = q.getD (i + 1) 0 := fun i hi => by
    rw [List.getElem_tail, List.getD_eq_getElem]
  refine ⟨(List.nodup_finRange n).map τ.symm.injective, fun y => ?_,
    (h.nd.sublist (List.tail_sublist q)).map_on fun x hx y hy e => ?_, fun y => ?_, ?_⟩
  · exact List.mem_map.2 ⟨τ y, List.mem_finRange _, τ.symm_apply_apply y⟩
  · rw [← tau_tinv τ C.root (hq0 x hx), ← tau_tinv τ C.root (hq0 y hy), e]
  · constructor
    · intro hy
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hy
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
      obtain ⟨a, ha, -⟩ := h.par
      have h3 := (ha (i + 1) (by omega) (by simp at hi; omega)).2.2.1
      intro e
      rw [htail i hi] at e
      apply h3
      rw [← tau_tinv τ C.root (h.lt _ (getD_mem (by simp at hi; omega))), e]
      exact (hT.kf _).2 rfl
    · intro hyr
      obtain ⟨j, hj, hje⟩ := List.getElem_of_mem (h.mem_all hT y)
      have hj0 : j ≠ 0 := by
        rintro rfl
        have : q.getD 0 0 = τ y := by rw [List.getD_eq_getElem _ _ hj, hje]
        rw [h.hd, hT.root] at this
        exact hyr (τ.injective (Fin.ext this)).symm
      refine List.mem_map.2 ⟨τ y, ?_, tinv_tau τ C.root y⟩
      rw [← hje]
      have : q[j] = q.tail[j - 1]'(by simp; omega) := by
        rw [List.getElem_tail]; congr 1; omega
      rw [this]
      exact List.getElem_mem _
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.getElem_map]
    rw [htail i (by simpa using hi), htail j (by simpa using hj)]
    exact h.depth_mono hT (j + 1) (by simp at hj; omega) (i + 1) (by omega)

end Tree

/-! ### The program -/

/-- The parents and the flags: `PN[u] := A[PD[u]] - of`, `Kf[u] := (u - r) + (r - u)`. -/
def toPrepBody : Stmt := block [.addN 1622 1602 1621, .loadN 1623 1622, .addN 1622 1603 1623,
  .loadN 1624 1622, .subN 1624 1624 1604, .addN 1622 1605 1621, .storeN 1622 1624,
  .subN 1625 1621 1601, .subN 1626 1601 1621, .addN 1625 1625 1626, .addN 1622 1606 1621,
  .storeN 1622 1625, .addN 1621 1621 1620]

/-- The parents and the flags of all the nodes. -/
def toPrep : Stmt :=
  .seq (block [.constN 1620 1, .constN 1621 0]) (.whileLtN 1621 1600 toPrepBody)

/-- The children lists, by `osProg`. -/
def toSort : Stmt :=
  .seq (block [.copyN 1500 1600, .copyN 1501 1600, .copyN 1502 1605, .copyN 1504 1606,
    .copyN 1505 1607, .copyN 1506 1608, .copyN 1507 1609, .copyN 1508 1610, .copyN 1509 1611])
    osProg

/-- A child `OL[i]` queued. -/
def toArc : Stmt := block [.addN 1622 1611 1621, .loadN 1623 1622, .addN 1622 1612 1631,
  .storeN 1622 1623, .addN 1631 1631 1620, .addN 1621 1621 1620]

/-- The node at the head of the queue: its children queued. -/
def toVert : Stmt :=
  .seq (block [.addN 1622 1612 1630, .loadN 1632 1622, .addN 1630 1630 1620,
    .addN 1622 1609 1632, .loadN 1621 1622, .addN 1622 1610 1632, .loadN 1633 1622])
    (.whileLtN 1621 1633 toArc)

/-- **The search**: the root queued, then the queue processed. -/
def toBfs : Stmt :=
  .seq (block [.storeN 1612 1601, .constN 1630 0, .constN 1631 1]) (.whileLtN 1630 1631 toVert)

/-- The two lengths: `HD[0] := n`, `HD[1] := qt - 1`. -/
def toOutHD : Stmt := block [.storeN 1615 1600, .subN 1634 1631 1620, .addN 1622 1615 1620,
  .storeN 1622 1634]

/-- The nodes in the order of their numbers: `IV[i] := i + of`. -/
def toOutIV : Stmt := .seq (block [.constN 1621 0]) (.whileLtN 1621 1600
  (block [.addN 1622 1621 1604, .addN 1623 1613 1621, .storeN 1623 1622, .addN 1621 1621 1620]))

/-- The parent darts in the order of the queue: `IT[i] := PD[Q[i + 1]]`. -/
def toOutIT : Stmt := .seq (block [.constN 1621 0]) (.whileLtN 1621 1634
  (block [.addN 1622 1612 1621, .addN 1622 1622 1620, .loadN 1623 1622, .addN 1622 1602 1623,
    .loadN 1624 1622, .addN 1622 1614 1621, .storeN 1622 1624, .addN 1621 1621 1620]))

/-- **The depth orders of a tree.** -/
def toProg : Stmt :=
  .seq toPrep (.seq toSort (.seq toBfs (.seq toOutHD (.seq toOutIV toOutIT))))

/-- The layout of `toProg`: the scratch `[Sb, Sb + 8 n + 1)` (parents, flags, the counts and
cursors of the sort, the children lists, the queue) apart from the inputs `PD` (`n` words) and
`A` (`nD` words) and from the outputs `IV`, `IT` (`n` words each, in a row) and `HD` (two
words); the outputs apart from `PD`. -/
structure ToLay (n nD r Sb PDb Ab IVb ITb HDb of W : ℕ) : Prop where
  pos : 0 < n
  rlt : r < n
  hPD : Sb + 8 * n + 1 ≤ PDb ∨ PDb + n ≤ Sb
  hA : Sb + 8 * n + 1 ≤ Ab ∨ Ab + nD ≤ Sb
  hO : HDb + 2 ≤ Sb ∨ Sb + 8 * n + 1 ≤ IVb
  hOP : HDb + 2 ≤ PDb ∨ PDb + n ≤ IVb
  iv : IVb + n ≤ ITb
  it : ITb + n ≤ HDb
  wS : Sb + 8 * n + 1 ≤ W
  wP : PDb + n ≤ W
  wA : Ab + nD ≤ W
  wH : HDb + 2 ≤ W
  wo : of + n ≤ W

/-- The registers of `toProg`. -/
structure ToRegs (n r Sb PDb Ab IVb ITb HDb of : ℕ) (c : Config) : Prop where
  r00 : c.nreg 1600 = n
  r01 : c.nreg 1601 = r
  r02 : c.nreg 1602 = PDb
  r03 : c.nreg 1603 = Ab
  r04 : c.nreg 1604 = of
  r05 : c.nreg 1605 = Sb
  r06 : c.nreg 1606 = Sb + n
  r07 : c.nreg 1607 = Sb + 2 * n
  r08 : c.nreg 1608 = Sb + 3 * n + 1
  r09 : c.nreg 1609 = Sb + 4 * n + 1
  r10 : c.nreg 1610 = Sb + 5 * n + 1
  r11 : c.nreg 1611 = Sb + 6 * n + 1
  r12 : c.nreg 1612 = Sb + 7 * n + 1
  r13 : c.nreg 1613 = IVb
  r14 : c.nreg 1614 = ITb
  r15 : c.nreg 1615 = HDb

theorem ToRegs.frame {n r Sb PDb Ab IVb ITb HDb of : ℕ} {c c' : Config}
    (h : ToRegs n r Sb PDb Ab IVb ITb HDb of c)
    (hn : ∀ r, 1600 ≤ r → r ≤ 1615 → c'.nreg r = c.nreg r) :
    ToRegs n r Sb PDb Ab IVb ITb HDb of c' :=
  ⟨(hn _ (by omega) (by omega)).trans h.r00, (hn _ (by omega) (by omega)).trans h.r01,
    (hn _ (by omega) (by omega)).trans h.r02, (hn _ (by omega) (by omega)).trans h.r03,
    (hn _ (by omega) (by omega)).trans h.r04, (hn _ (by omega) (by omega)).trans h.r05,
    (hn _ (by omega) (by omega)).trans h.r06, (hn _ (by omega) (by omega)).trans h.r07,
    (hn _ (by omega) (by omega)).trans h.r08, (hn _ (by omega) (by omega)).trans h.r09,
    (hn _ (by omega) (by omega)).trans h.r10, (hn _ (by omega) (by omega)).trans h.r11,
    (hn _ (by omega) (by omega)).trans h.r12, (hn _ (by omega) (by omega)).trans h.r13,
    (hn _ (by omega) (by omega)).trans h.r14, (hn _ (by omega) (by omega)).trans h.r15⟩

/-! ### The phases -/

variable {P : Input} {W : ℕ} {nD Sb PDb Ab IVb ITb HDb of : ℕ}

theorem toPrep_exec (hL : ToLay n nD r Sb PDb Ab IVb ITb HDb of W) (c : Config)
    (hc : WordsBounded W c) (hR : ToRegs n r Sb PDb Ab IVb ITb HDb of c)
    (hpd : ∀ u < n, c.nmem (PDb + u) < nD) :
    ∃ c' k, Exec P W toPrep c c' k ∧ k ≤ 15 * n + 4 ∧
      ((∀ u < n, c'.nmem (Sb + u) = c.nmem (Ab + c.nmem (PDb + u)) - of ∧
          c'.nmem (Sb + n + u) = (u - r) + (r - u)) ∧
        (∀ a, (a < Sb ∨ Sb + 2 * n ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 1620 ∨ 1626 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 1620 = 1 ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wS; have := hL.wP; have := hL.wA; have := hL.hPD; have := hL.hA; have := hL.rlt
  obtain ⟨r00, r01, r02, r03, r04, r05, r06, -⟩ := hR
  unfold toPrep
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i d =>
    (∀ u < i, d.nmem (Sb + u) = c.nmem (Ab + c.nmem (PDb + u)) - of ∧
        d.nmem (Sb + n + u) = (u - r) + (r - u)) ∧
      (∀ a, (a < Sb ∨ Sb + i ≤ a) → (a < Sb + n ∨ Sb + n + i ≤ a) → d.nmem a = c.nmem a) ∧
      (∀ r, r < 1620 ∨ 1626 < r → d.nreg r = c.nreg r) ∧ d.nreg 1620 = 1 ∧
      d.rreg = c.rreg ∧ d.rmem = c.rmem ∧ d.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 1621) (bR := 1600) (body := toPrepBody) J
    (K := 13) (n := n) _ ‹_› (by config_simp) (by config_simp; exact r00) ?_
    (fun i d hi hw ha hb ⟨g, gm, gn, g20, gr, grm, go⟩ => by
      have e01 : d.nreg 1601 = r := (gn 1601 (by omega)).trans r01
      have e02 : d.nreg 1602 = PDb := (gn 1602 (by omega)).trans r02
      have e03 : d.nreg 1603 = Ab := (gn 1603 (by omega)).trans r03
      have e04 : d.nreg 1604 = of := (gn 1604 (by omega)).trans r04
      have e05 : d.nreg 1605 = Sb := (gn 1605 (by omega)).trans r05
      have e06 : d.nreg 1606 = Sb + n := (gn 1606 (by omega)).trans r06
      have hp : d.nmem (PDb + i) = c.nmem (PDb + i) := gm _ (by omega) (by omega)
      have hpl := hpd i hi
      have hav : d.nmem (Ab + c.nmem (PDb + i)) = c.nmem (Ab + c.nmem (PDb + i)) :=
        gm _ (by omega) (by omega)
      unfold toPrepBody
      exec_block
      all_goals try ((try config_simp); (try simp only [e01, e02, e03, e05, e06, ha, hp, g20]); omega)
      dsimp only [J]
      config_simp
      simp only [e01, e02, e03, e04, e05, e06, ha, hp, hav, g20]
      refine ⟨by omega, trivial, hb, fun u hu => ?_, fun a h1 h2 => ?_, fun r hr => ?_, trivial,
        gr, grm, go⟩
      · simp only [upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
        · obtain ⟨g1, g2⟩ := g u hu
          constructor <;> split_ifs <;> omega
        · constructor <;> split_ifs <;> omega
      · simp only [upd_apply]
        split_ifs <;> first | omega | exact gm a (by omega) (by omega)
      · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr)) ?_
  · refine ⟨fun u hu => absurd hu (by omega), fun _ _ _ => rfl, fun r hr => ?_, ?_, rfl, rfl,
      rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  intro c₂ k₂ hk₂ _ hJ₂
  obtain ⟨_, g, gm, gn, g20, gr, grm, go⟩ := hJ₂
  exact ⟨by omega, g, fun a ha => gm a (by omega) (by omega), gn, g20, gr, grm, go⟩

/-- The children lists in memory: for every node `u < n`, the children of `u` are the words of
`OL` (at `Sb + 6 n + 1`) from `OB[u]` (at `Sb + 4 n + 1`) on, `OE[u]` (at `Sb + 5 n + 1`)
their end, at most `n`. -/
structure ToCh (n Sb : ℕ) (pn kf : ℕ → ℕ) (mem : ℕ → ℕ) : Prop where
  le : ∀ u < n, mem (Sb + 4 * n + 1 + u) + (tch n pn kf u).length ≤ n
  oe : ∀ u < n, mem (Sb + 5 * n + 1 + u) = mem (Sb + 4 * n + 1 + u) + (tch n pn kf u).length
  ol : ∀ u < n, ∀ j < (tch n pn kf u).length,
    mem (Sb + 6 * n + 1 + (mem (Sb + 4 * n + 1 + u) + j)) = (tch n pn kf u).getD j 0

theorem ToCh.frame {n Sb : ℕ} {mem mem' : ℕ → ℕ} (h : ToCh n Sb pn kf mem)
    (hm : ∀ a, Sb + 4 * n + 1 ≤ a → a < Sb + 7 * n + 1 → mem' a = mem a) :
    ToCh n Sb pn kf mem' := by
  refine ⟨fun u hu => ?_, fun u hu => ?_, fun u hu j hj => ?_⟩
  · rw [hm _ (by omega) (by omega)]; exact h.le u hu
  · rw [hm _ (by omega) (by omega), hm _ (by omega) (by omega)]; exact h.oe u hu
  · have := h.le u hu
    rw [hm (Sb + 4 * n + 1 + u) (by omega) (by omega), hm _ (by omega) (by omega)]
    exact h.ol u hu j hj

/-- **One child queued**: `Q[qt] := OL[i]`. -/
theorem toArc_exec (c : Config) (hc : WordsBounded W c) {OLb Qb i t : ℕ}
    (h11 : c.nreg 1611 = OLb) (h12 : c.nreg 1612 = Qb) (h20 : c.nreg 1620 = 1)
    (h21 : c.nreg 1621 = i) (h31 : c.nreg 1631 = t) (hw1 : OLb + i ≤ W) (hw2 : Qb + t ≤ W)
    (hw3 : t + 1 ≤ W) (hw4 : i + 1 ≤ W) :
    ∃ c' k, Exec P W toArc c c' k ∧ k = 6 ∧ c'.nreg 1621 = i + 1 ∧ c'.nreg 1631 = t + 1 ∧
      c'.nmem = upd c.nmem (Qb + t) (c.nmem (OLb + i)) ∧
      (∀ r, r ≠ 1621 → r ≠ 1622 → r ≠ 1623 → r ≠ 1631 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold toArc
  exec_block
  all_goals try ((try config_simp); (try simp only [h11, h12, h20, h21, h31]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [h20, h21]
  · config_simp; simp only [h20, h31]
  · config_simp; simp only [h11, h12, h21, h31]
  · config_simp; simp only [upd_apply, h1, h2, h3, h4, ↓reduceIte]

set_option maxHeartbeats 1000000 in
/-- **One node of the search**: the node `u` at position `k` of the queue `q` dequeued, its
children appended to the queue. -/
theorem toVert_exec (hL : ToLay n nD r Sb PDb Ab IVb ITb HDb of W) (c : Config)
    (hc : WordsBounded W c) (hR : ToRegs n r Sb PDb Ab IVb ITb HDb of c) (h20 : c.nreg 1620 = 1)
    (hch : ToCh n Sb pn kf c.nmem) {k : ℕ} {q : List ℕ} (hq : TQ n r pn kf k q)
    (hk : k < q.length) (h30 : c.nreg 1630 = k) (h31 : c.nreg 1631 = q.length)
    (hQ : ∀ i < q.length, c.nmem (Sb + 7 * n + 1 + i) = q.getD i 0)
    (hlen : (q ++ tch n pn kf (q.getD k 0)).length ≤ n) :
    ∃ c' t, Exec P W toVert c c' t ∧ t ≤ 9 + 8 * (tch n pn kf (q.getD k 0)).length ∧
      (ToRegs n r Sb PDb Ab IVb ITb HDb of c' ∧ c'.nreg 1620 = 1 ∧ c'.nreg 1630 = k + 1 ∧
        c'.nreg 1631 = (q ++ tch n pn kf (q.getD k 0)).length ∧
        (∀ i < (q ++ tch n pn kf (q.getD k 0)).length,
          c'.nmem (Sb + 7 * n + 1 + i) = (q ++ tch n pn kf (q.getD k 0)).getD i 0) ∧
        (∀ a, (a < Sb + 7 * n + 1 ∨ Sb + 8 * n + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 1620 ∨ 1634 < r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
        c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wS; have hqn := hq.length_le
  set u := q.getD k 0 with hu
  have hun : u < n := hq.lt _ (getD_mem hk)
  set ch := tch n pn kf u with hchd
  have hle := hch.le u hun
  have hoe := hch.oe u hun
  have hQu : c.nmem (Sb + 7 * n + 1 + k) = u := hQ k hk
  obtain ⟨r00, r01, r02, r03, r04, r05, r06, r07, r08, r09, r10, r11, r12, r13, r14, r15⟩ := hR
  unfold toVert
  refine spec_seq ?_
  exec_block
  all_goals try ((try config_simp); (try simp only [r09, r10, r12, h30, hQu, h20]); omega)
  set ob := c.nmem (Sb + 4 * n + 1 + u) with hob
  have hle' : ob + ch.length ≤ n := hle
  have hoe' : c.nmem (Sb + 5 * n + 1 + u) = ob + ch.length := hoe
  have hlen' : q.length + ch.length ≤ n := by simpa using hlen
  let I : Config → Prop := fun d =>
    WordsBounded W d ∧ ToRegs n r Sb PDb Ab IVb ITb HDb of d ∧ d.nreg 1620 = 1 ∧
      d.nreg 1630 = k + 1 ∧ d.nreg 1633 = ob + ch.length ∧
      (∃ j ≤ ch.length, d.nreg 1621 = ob + j ∧ d.nreg 1631 = q.length + j ∧
        (∀ i < q.length + j, d.nmem (Sb + 7 * n + 1 + i) = (q ++ ch).getD i 0) ∧
        (∀ a, (a < Sb + 7 * n + 1 + q.length ∨ Sb + 7 * n + 1 + q.length + j ≤ a) →
          d.nmem a = c.nmem a)) ∧
      (∀ r, r < 1620 ∨ 1634 < r → d.nreg r = c.nreg r) ∧ d.rreg = c.rreg ∧ d.rmem = c.rmem ∧
      d.output = c.output
  refine spec_while I (fun d => 8 * (ob + ch.length - d.nreg 1621)) (fun d h => h.1) ?_ ?_ ?_
  · intro d ⟨hw, hRd, d20, d30, d33, ⟨j, hj, d21, d31, dQ, dm⟩, dn, drr, drm, dout⟩ hlt
    rw [d33, d21] at hlt
    have hjl : j < ch.length := by omega
    have hol : d.nmem (Sb + 6 * n + 1 + (ob + j)) = ch.getD j 0 := by
      rw [dm _ (Or.inl (by omega))]; exact hch.ol u hun j hjl
    obtain ⟨d', t, ex, ht, e21, e31, em, en, err, erm, eo⟩ :=
      toArc_exec (P := P) d hw (OLb := Sb + 6 * n + 1) (Qb := Sb + 7 * n + 1) hRd.r11 hRd.r12 d20
        d21 d31 (by omega) (by omega) (by omega) (by omega)
    refine ⟨d', t, ex, ⟨ex.wb_right, hRd.frame fun r h1 h2 => en r (by omega) (by omega)
      (by omega) (by omega), by rw [en _ (by omega) (by omega) (by omega) (by omega)]; exact d20,
      by rw [en _ (by omega) (by omega) (by omega) (by omega)]; exact d30,
      by rw [en _ (by omega) (by omega) (by omega) (by omega)]; exact d33,
      ⟨j + 1, by omega, by rw [e21]; omega, by rw [e31]; omega, fun i hi => ?_, fun a ha => ?_⟩,
      fun r hr => ?_, by rw [err, drr], by rw [erm, drm], by rw [eo, dout]⟩, ?_⟩
    · rw [em, hol, upd_apply]
      split_ifs with h1
      · have : i = q.length + j := by omega
        subst this
        rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
      · exact dQ i (by omega)
    · rw [em, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      exact dm a (by omega)
    · rw [en r (by omega) (by omega) (by omega) (by omega)]; exact dn r hr
    · rw [e21, ht]; omega
  · refine ⟨‹_›, ?_, ?_, ?_, ?_, ⟨0, by omega, ?_, ?_, fun i hi => ?_, fun a ha => rfl⟩,
      fun r hr => ?_, rfl, rfl, rfl⟩
    · exact ToRegs.frame ⟨r00, r01, r02, r03, r04, r05, r06, r07, r08, r09, r10, r11, r12, r13,
        r14, r15⟩ fun r h1 h2 => by config_simp; simp only [upd_apply]; split_ifs <;> omega
    · config_simp; exact h20
    · config_simp; simp only [h30, h20]
    · config_simp; simp only [r10, r12, h30, hQu, hoe']; try rfl
    · config_simp; simp only [r09, r12, h30, hQu]; try rfl
    · config_simp; simp only [h31]; try rfl
    · config_simp; rw [List.getD_append _ _ _ _ (by omega)]; exact hQ i (by omega)
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  · intro d t ⟨hw, hRd, d20, d30, d33, ⟨j, hj, d21, d31, dQ, dm⟩, dn, drr, drm, dout⟩ hn ht
    rw [d33, d21] at hn
    have hj' : j = ch.length := by omega
    subst hj'
    have ht' : t ≤ 8 * ch.length + 2 := by
      config_simp at ht; simp only [r09, r12, h30, hQu] at ht; omega
    refine ⟨by omega, hRd, d20, d30, by rw [d31, List.length_append], fun i hi => dQ i (by simpa
      using hi), fun a ha => dm a (by omega), fun r hr => dn r hr, drr, drm, dout⟩

set_option maxHeartbeats 1000000 in
/-- **The search**: from the children lists, the queue `q` of the finished search (`TQ` with all
its nodes processed) at `Sb + 7 n + 1`, its length in `r1631`, within `19 n + 5` steps. -/
theorem toBfs_exec (hL : ToLay n nD r Sb PDb Ab IVb ITb HDb of W) (c : Config)
    (hc : WordsBounded W c) (hR : ToRegs n r Sb PDb Ab IVb ITb HDb of c) (h20 : c.nreg 1620 = 1)
    (hch : ToCh n Sb pn kf c.nmem) (hkr : kf r = 0) :
    ∃ c' t, Exec P W toBfs c c' t ∧ t ≤ 19 * n + 5 ∧
      (ToRegs n r Sb PDb Ab IVb ITb HDb of c' ∧ c'.nreg 1620 = 1 ∧
        ∃ q, TQ n r pn kf q.length q ∧ c'.nreg 1631 = q.length ∧
          (∀ i < q.length, c'.nmem (Sb + 7 * n + 1 + i) = q.getD i 0) ∧
          (∀ a, (a < Sb + 7 * n + 1 ∨ Sb + 8 * n + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
          (∀ r, r < 1620 ∨ 1634 < r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
          c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wS; have := hL.rlt; have := hL.pos
  obtain ⟨r00, r01, r02, r03, r04, r05, r06, r07, r08, r09, r10, r11, r12, r13, r14, r15⟩ := hR
  unfold toBfs
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let I : Config → Prop := fun d =>
    WordsBounded W d ∧ ToRegs n r Sb PDb Ab IVb ITb HDb of d ∧ d.nreg 1620 = 1 ∧
      ∃ q, TQ n r pn kf (d.nreg 1630) q ∧ d.nreg 1631 = q.length ∧
        (∀ i < q.length, d.nmem (Sb + 7 * n + 1 + i) = q.getD i 0) ∧
        (∀ a, (a < Sb + 7 * n + 1 ∨ Sb + 8 * n + 1 ≤ a) → d.nmem a = c.nmem a) ∧
        (∀ r, r < 1620 ∨ 1634 < r → d.nreg r = c.nreg r) ∧ d.rreg = c.rreg ∧
        d.rmem = c.rmem ∧ d.output = c.output
  refine spec_while I (fun d => 11 * (n - d.nreg 1630) + 8 * (n - d.nreg 1631)) (fun d h => h.1)
    ?_ ?_ ?_
  · intro d ⟨hw, hRd, d20, q, hq, d31, dQ, dm, dn, drr, drm, dout⟩ hlt
    rw [d31] at hlt
    have hq' := hq.step hkr hlt
    have hlen := hq'.length_le
    have hchd : ToCh n Sb pn kf d.nmem := hch.frame fun a h1 h2 => dm a (Or.inl (by omega))
    obtain ⟨d', t, ex, ht, hR', e20, e30, e31, eQ, em, en, err, erm, eo⟩ :=
      toVert_exec (P := P) hL d hw hRd d20 hchd hq hlt rfl d31 dQ hlen
    have hqn := hq.length_le
    refine ⟨d', t, ex, ⟨ex.wb_right, hR', e20, _, by rw [e30]; exact hq', e31, eQ,
      fun a ha => by rw [em a ha, dm a ha], fun r hr => by rw [en r hr, dn r hr],
      by rw [err, drr], by rw [erm, drm], by rw [eo, dout]⟩, ?_⟩
    rw [e30, e31, d31]
    simp only [List.length_append] at hlen ⊢
    omega
  · refine ⟨‹_›, ToRegs.frame ⟨r00, r01, r02, r03, r04, r05, r06, r07, r08, r09, r10, r11, r12,
      r13, r14, r15⟩ fun r h1 h2 => by config_simp; simp only [upd_apply]; split_ifs <;> omega,
      by config_simp; exact h20, [r], ?_, by config_simp; rfl, fun i hi => ?_, fun a ha => ?_,
      fun r hr => ?_, rfl, rfl, rfl⟩
    · config_simp; exact tq_zero hL.rlt
    · config_simp
      simp only [List.length_singleton, Nat.lt_one_iff] at hi
      subst hi
      simp only [r12, r01, upd_apply, Nat.add_zero, ↓reduceIte, List.getD_cons_zero]
    · config_simp
      simp only [r12, upd_apply]
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  · intro d t ⟨hw, hRd, d20, q, hq, d31, dQ, dm, dn, drr, drm, dout⟩ hn ht
    rw [d31] at hn
    have hk : d.nreg 1630 = q.length := by have := hq.kle; omega
    rw [hk] at hq
    refine ⟨?_, hRd, d20, q, hq, d31, dQ, dm, dn, drr, drm, dout⟩
    config_simp at ht
    omega

lemma blk_tch (u : ℕ) :
    (Monge.FR.blk (csList pn id kf (fun _ => 0) n) u).map (fun a => a.2.1) = tch n pn kf u :=
  blk_map_csList pn kf _ u n

set_option maxHeartbeats 1000000 in
/-- **The children lists**: `osProg` on the parents `PN` and the flags `Kf`. -/
theorem toSort_exec (hL : ToLay n nD r Sb PDb Ab IVb ITb HDb of W) (c : Config)
    (hc : WordsBounded W c) (hR : ToRegs n r Sb PDb Ab IVb ITb HDb of c)
    (hpk : ∀ u < n, c.nmem (Sb + u) = pn u ∧ c.nmem (Sb + n + u) = kf u)
    (htlt : ∀ u < n, kf u ≠ 0 → pn u < n) :
    ∃ c' t, Exec P W toSort c c' t ∧ t ≤ 9 + osCost n n ∧
      (ToCh n Sb pn kf c'.nmem ∧
        (∀ a, (a < Sb + 2 * n ∨ Sb + 7 * n + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 1500 ∨ 1520 < r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
        c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wS; have := hL.pos
  obtain ⟨r00, r01, r02, r03, r04, r05, r06, r07, r08, r09, r10, r11, r12, r13, r14, r15⟩ := hR
  unfold toSort
  refine spec_seq ?_
  exec_block
  have hOL : OsLay n n Sb (Sb + n) (Sb + 2 * n) (Sb + 3 * n + 1) (Sb + 4 * n + 1)
      (Sb + 5 * n + 1) (Sb + 6 * n + 1) W pn kf :=
    ⟨htlt, by omega, Or.inr (by omega), Or.inr (by omega), Or.inl (by omega), by omega, by omega,
      Or.inr (by omega), Or.inr (by omega), by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  refine spec_use (osProg_exec (P := P) hOL _ ‹_› ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun i hi => ?_, fun i hi => ?_⟩) ?_
  all_goals try (config_simp; simp only [r00, r05, r06, r07, r08, r09, r10, r11]; done)
  · config_simp; exact (hpk i hi).1
  · config_simp; exact (hpk i hi).2
  intro c' t ht hw ⟨hOB, hOLs, hm, hn, hr, hrm, ho⟩
  set L := csList pn id kf (fun _ => 0) n with hLd
  refine ⟨by omega, ⟨fun u hu => ?_, fun u hu => ?_, fun u hu j hj => ?_⟩, fun a ha => ?_,
    fun r hr' => ?_, hr, hrm, ho⟩
  · have hl := congrArg List.length (blk_tch (pn := pn) (kf := kf) (n := n) u)
    rw [List.length_map] at hl
    rw [(hOB u hu).1, ← hl, ← length_pre_succ]
    exact (Monge.FR.length_pre_le _ _).trans (length_csList_le n)
  · have hl := congrArg List.length (blk_tch (pn := pn) (kf := kf) (n := n) u)
    rw [List.length_map] at hl
    rw [(hOB u hu).1, (hOB u hu).2, ← hl, ← length_pre_succ]
  · have hl := congrArg List.length (blk_tch (pn := pn) (kf := kf) (n := n) u)
    rw [List.length_map] at hl
    have hj' : j < (Monge.FR.blk L u).length := by rw [hl]; exact hj
    have hlt : (Monge.FR.pre L u).length + j < (Monge.FR.pre L n).length := by
      have := Monge.FR.length_pre_mono L (show u + 1 ≤ n by omega)
      rw [length_pre_succ] at this; omega
    rw [(hOB u hu).1, hOLs _ hlt, pre_getD_blk L hu hj']
    have h := List.getElem_of_eq (blk_tch (pn := pn) (kf := kf) (n := n) u) (i := j)
      (by simpa using hj')
    simp only [List.getElem_map] at h
    rw [h, List.getD_eq_getElem]
  · rw [hm a (by omega) (by omega)]
  · rw [hn r (by omega)]; config_simp; simp only [upd_apply]; split_ifs <;> omega

end NegSSSP

end PlanarFlow
