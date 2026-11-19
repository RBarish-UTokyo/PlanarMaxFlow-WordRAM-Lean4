module

public import PlanarFlow.BKMNW.MachCost
public import PlanarFlow.BKMNW.DistTransfer
public import PlanarFlow.Monge.FRLayout
public import PlanarFlow.NegSSSP.Step

/-!
# Calls of FR-Dijkstra on explicit arcs only, on the machine

A call `fr emptyDDG E r φ` of FR-Dijkstra with no dense distance graph is Dijkstra with a price
function on the explicit arcs `E`. This file proves that **every such call is realized by a run of
the machine program `PlanarFlow.Monge.FR.frProg` within `cNegMach.dij |S| |E|` steps**, `S` any
finite set of vertices holding the root and the ends of the arcs (`cNegMach_dij_exec_list`), the
distances being left in memory:

* the vertices of `S` are numbered `0, …, |S| - 1` (by `Finset.equivFin`) and the input is laid out
  by `PlanarFlow.Monge.FR.mkPrm` with one corner, so that the machine's dense distance graph has no
  arcs (`NegSSSP.cNegMach_dij_exec`);
* the distances of the machine's graph are those of the call, read along the numbering
  (`isDist_transfer`).

The calls of Dijkstra in a step of the negative-length recursion (`PlanarFlow.NegSSSP.dijk`, on the
vertices of a piece and a virtual root) are such calls, with `S` the root and the vertices of the
piece: `cNegMach_dijk_exec` realizes each within `cNegMach.dij (w + 1) (m + w)` steps, `m` the darts
and `w` the vertices of the piece, which is the charge of `NegCosts.node`. The two calls of
Dijkstra in the dual graph in the cancellation of the push-back (`PlanarFlow.BKMNW.dualDijkstra`,
nonnegative lengths) are such calls too, with `S` all the faces: `BKMNW.cMach_fr_exec_dual`
realizes each within `cMach.fr nf n` steps (`nf` faces, `n` darts), the charge of
`SubCosts.pushRun`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine Monge.FR BKMNW

section List

variable {X : Type*} [DecidableEq X]

/-- **Every call of FR-Dijkstra on explicit arcs only is realized by a run of `frProg` within
`cNegMach.dij |S| |E|` steps**, `S` a set of vertices holding the root `r` and the ends of the
arcs `E`, with a feasible price function `φ`; `fr` is any implementation meeting `FRSpec`. The run
leaves, for each vertex `y` of `S` (numbered `idx y`), the flag `1` iff `y` is reachable and its
distance. -/
theorem cNegMach_dij_exec_list (C : ℕ) (S : Finset X) (E : List (X × X × ℤ)) {r : X}
    (hr : r ∈ S) (hE : ∀ e ∈ E, e.1 ∈ S ∧ e.2.1 ∈ S) (hE0 : E ≠ []) {φ : X → ℤ}
    (hpot : ((emptyDDG (F := X)).union E).IsPot φ) {fr : FRFun X} (hfr : FRSpec fr)
    (I : Input) :
    ∃ (Pr : Prm) (c₀ c' : Config) (steps : ℕ) (idx : X → ℕ),
      Exec I Pr.W frProg c₀ c' steps ∧ steps ≤ (cNegMach C).dij S.card E.length ∧
      c'.output = c₀.output ∧
      ∀ y ∈ S, idx y < Pr.N ∧ (c'.nmem (Pr.sb + idx y) = 1 ↔ fr emptyDDG E r φ y ≠ none) ∧
        ∀ ℓ, fr emptyDDG E r φ y = some ℓ → c'.rmem (Pr.db + idx y) = ℓ := by
  set GF := (emptyDDG (F := X)).union E with hGF
  set n := S.card with hn
  set e := S.equivFin
  -- the numbering of `S`
  let β : ℕ → X := fun i => if h : i < n then (e.symm ⟨i, h⟩).1 else r
  let idx : X → ℕ := fun y => if h : y ∈ S then (e ⟨y, h⟩ : ℕ) else 0
  have hidx_lt : ∀ y ∈ S, idx y < n := fun y hy => by
    simp only [idx, hy, ↓reduceDIte]; exact (e ⟨y, hy⟩).2
  have hβidx : ∀ y ∈ S, β (idx y) = y := fun y hy => by
    have h : (e ⟨y, hy⟩ : ℕ) < n := (e ⟨y, hy⟩).2
    simp only [β, idx, hy, ↓reduceDIte, h]
    simp
  have hβS : ∀ i < n, β i ∈ S := fun i hi => by
    simp only [β, hi, ↓reduceDIte]; exact (e.symm ⟨i, hi⟩).2
  have hβinj : ∀ i < n, ∀ j < n, β i = β j → i = j := fun i hi j hj h => by
    simp only [β, hi, hj, ↓reduceDIte] at h
    have := e.symm.injective (Subtype.ext h)
    exact congrArg Fin.val this
  have hn1 : 1 ≤ n := by
    have := card_pos.2 ⟨r, hr⟩; omega
  -- the input
  let pm : ℕ → ℤ := fun x => φ (β x)
  let Es : List (ℕ × ℕ × ℤ) := E.map fun a => (idx a.1, idx a.2.1, a.2.2)
  have hEs : ∀ a ∈ Es, a.1 < n ∧ a.2.1 < n := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
    exact ⟨hidx_lt _ (hE a' ha').1, hidx_lt _ (hE a' ha').2⟩
  set Pr := mkPrm n 1 (fun _ _ => 0) pm (idx r) Es with hPr
  have hL : Lay Pr := mkPrm_lay le_rfl hn1 (hidx_lt r hr) fun a ha => (hEs a ha).2
  have hfvv : ∀ {i : ℕ}, i < n → ((fv Pr hL.N_pos i : Fin Pr.N) : ℕ) = i := fun hi => fv_val hi
  have hlenEx : (exArcs Pr hL.N_pos).length = (arcList n Es).length :=
    length_exArcs_mkPrm hL.N_pos
  have hgetEx : ∀ t (ht : t < (exArcs Pr hL.N_pos).length), (exArcs Pr hL.N_pos)[t] =
      (fv Pr hL.N_pos ((arcList n Es)[t]'(by rw [← hlenEx]; exact ht)).1,
        fv Pr hL.N_pos ((arcList n Es)[t]'(by rw [← hlenEx]; exact ht)).2.1,
        ((arcList n Es)[t]'(by rw [← hlenEx]; exact ht)).2.2) := fun t ht =>
    exArcs_mkPrm_get hL.N_pos ht
  have hm_pos : 0 < (arcList n Es).length := by
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil E hE0
    have ha' : (idx a.1, idx a.2.1, a.2.2) ∈ Es := List.mem_map.2 ⟨_, ha, rfl⟩
    exact List.length_pos_of_mem (mem_arcList.2 ⟨ha', (hEs _ ha').1⟩)
  -- the vertex of a machine vertex
  let ι : Fin Pr.N → X := fun x => β x.1
  have hι : Function.Injective ι := fun x y h => Fin.ext (hβinj x.1 x.2 y.1 y.2 h)
  set Gm := (emptyDDG (F := Fin Pr.N)).union (exArcs Pr hL.N_pos)
  -- explicit arcs correspond
  have hex_m : ∀ t : Fin (exArcs Pr hL.N_pos).length, ∃ j : Fin E.length,
      ι (Gm.src (.inr t)) = GF.src (.inr j) ∧ ι (Gm.dst (.inr t)) = GF.dst (.inr j) ∧
        Gm.len (.inr t) = GF.len (.inr j) := by
    intro t
    have ht : t.1 < (arcList n Es).length := lt_of_lt_of_eq t.2 hlenEx
    have hget := hgetEx t.1 t.2
    have ha : (arcList n Es)[t.1] ∈ Es := (mem_arcList.1 (List.getElem_mem ht)).1
    obtain ⟨a, ha', he'⟩ := List.mem_map.1 ha
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ha'
    refine ⟨⟨j, hj⟩, ?_, ?_, ?_⟩
    · show β ((exArcs Pr hL.N_pos)[t.1]).1.1 = E[j].1
      rw [hget, hfvv (by rw [← he']; exact hidx_lt _ (hE _ ha').1), ← he']
      exact hβidx _ (hE _ ha').1
    · show β ((exArcs Pr hL.N_pos)[t.1]).2.1.1 = E[j].2.1
      rw [hget, hfvv (by rw [← he']; exact hidx_lt _ (hE _ ha').2), ← he']
      exact hβidx _ (hE _ ha').2
    · show ((exArcs Pr hL.N_pos)[t.1]).2.2 = E[j].2.2
      rw [hget, ← he']
  have hex_F : ∀ j : Fin E.length, ∃ t : Fin (exArcs Pr hL.N_pos).length,
      ι (Gm.src (.inr t)) = GF.src (.inr j) ∧ ι (Gm.dst (.inr t)) = GF.dst (.inr j) ∧
        Gm.len (.inr t) = GF.len (.inr j) := by
    intro j
    have hmemE : E[j.1] ∈ E := List.getElem_mem j.2
    have ha : (idx E[j.1].1, idx E[j.1].2.1, E[j.1].2.2) ∈ arcList n Es :=
      mem_arcList.2 ⟨List.mem_map.2 ⟨_, hmemE, rfl⟩, hidx_lt _ (hE _ hmemE).1⟩
    obtain ⟨t, ht, hta⟩ := List.mem_iff_getElem.1 ha
    have ht' : t < (exArcs Pr hL.N_pos).length := by rw [hlenEx]; exact ht
    have hget := hgetEx t ht'
    refine ⟨⟨t, ht'⟩, ?_, ?_, ?_⟩
    · show β ((exArcs Pr hL.N_pos)[t]).1.1 = E[j.1].1
      rw [hget]; simp only [hta]
      rw [hfvv (hidx_lt _ (hE _ hmemE).1)]; exact hβidx _ (hE _ hmemE).1
    · show β ((exArcs Pr hL.N_pos)[t]).2.1.1 = E[j.1].2.1
      rw [hget]; simp only [hta]
      rw [hfvv (hidx_lt _ (hE _ hmemE).2)]; exact hβidx _ (hE _ hmemE).2
    · show ((exArcs Pr hL.N_pos)[t]).2.2 = E[j.1].2.2
      rw [hget]; simp only [hta]
  -- the transfer
  have htr : Transfer Gm GF ι := by
    refine ⟨hι, ?_, ?_⟩
    · rintro (⟨_, h, -⟩ | t)
      · simp [emptyDDG] at h
      · obtain ⟨j, h1, h2, h3⟩ := hex_m t
        exact ⟨.inr j, h1.symm, h2.symm, h3.symm⟩
    · rintro (⟨_, h, -⟩ | j) x hx
      · simp [emptyDDG] at h
      · left
        obtain ⟨t, h1, h2, h3⟩ := hex_F j
        exact ⟨.inr t, hι (h1.trans hx), h2, h3⟩
  -- the potential of the machine's input
  have hp : Gm.IsPot (fun y => Pr.p y) := by
    rintro (⟨_, h, -⟩ | t)
    · simp [emptyDDG] at h
    · obtain ⟨j, h1, h2, h3⟩ := hex_m t
      have := hpot (.inr j)
      show φ (ι (Gm.dst (.inr t))) ≤ φ (ι (Gm.src (.inr t))) + Gm.len (.inr t)
      rw [h1, h2, h3]; exact this
  -- the run
  obtain ⟨c₀, hw, hin, hDa⟩ := exists_frConfig hL
  obtain ⟨c', steps, he, hsteps, -, hout, δ, hδ, hmem⟩ :=
    cNegMach_dij_exec (I := I) C hL rfl mkPrm_off_zero hm_pos hp c₀ hw hin hDa
  have hroot : ι (fv Pr hL.N_pos Pr.r) = r := by
    show β (fv Pr hL.N_pos (idx r) : ℕ) = r
    rw [hfvv (hidx_lt r hr)]; exact hβidx r hr
  have hδF := isDist_transfer htr hδ
  rw [hroot] at hδF
  have heq := (hfr emptyDDG E r φ hpot).unique hδF
  have key : ∀ y (hy : y ∈ S), fr emptyDDG E r φ y = δ ⟨idx y, hidx_lt y hy⟩ := by
    intro y hy
    have hy' : ι ⟨idx y, hidx_lt y hy⟩ = y := hβidx y hy
    rw [heq]
    calc htr.pull δ y = htr.pull δ (ι ⟨idx y, hidx_lt y hy⟩) := by rw [hy']
      _ = _ := htr.pull_iota δ _
  refine ⟨Pr, c₀, c', steps, idx, he, ?_, hout, fun y hy => ⟨hidx_lt y hy, ?_, ?_⟩⟩
  · refine hsteps.trans ?_
    have hmk : Pr.m ≤ E.length := by
      show (arcList n Es).length ≤ E.length
      have := length_pre_le Es n
      simpa [Es, arcList] using this
    show 6300 * (n + Pr.m) * lg n ≤ 6300 * (n + E.length) * lg n
    gcongr
  · rw [key y hy]; exact (hmem ⟨idx y, hidx_lt y hy⟩).1
  · intro ℓ hℓ
    rw [key y hy] at hℓ
    exact (hmem ⟨idx y, hidx_lt y hy⟩).2 ℓ hℓ

end List

/-! ### The calls of Dijkstra in a step of the recursion -/

section Dijk

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
variable (N : CombMap D V F)

/-- The vertices of the call of Dijkstra in a piece: the virtual root and the vertices of the
piece. -/
def dijVerts (P : Finset D) : Finset (Option V) := insert none ((verts N P).image some)

lemma card_dijVerts (P : Finset D) : (dijVerts N P).card = (verts N P).card + 1 := by
  unfold dijVerts
  rw [card_insert_of_notMem (by simp), card_image_of_injective _ (Option.some_injective _)]

lemma length_dijArcs (P : Finset D) (ℓ : D → ℤ) (W : Finset V) (init : V → ℤ) :
    (dijArcs N P ℓ W init).length = P.card + W.card := by
  simp [dijArcs]

lemma dijArcs_ends {P : Finset D} {ℓ : D → ℤ} {init : V → ℤ} {e : Option V × Option V × ℤ}
    (he : e ∈ dijArcs N P ℓ (verts N P) init) : e.1 ∈ dijVerts N P ∧ e.2.1 ∈ dijVerts N P := by
  unfold dijArcs at he
  simp only [List.mem_append, List.mem_map, mem_toList] at he
  rcases he with ⟨d, hd, rfl⟩ | ⟨v, hv, rfl⟩
  · refine ⟨mem_insert_of_mem (mem_image_of_mem _ ?_), mem_insert_of_mem (mem_image_of_mem _ ?_)⟩
    · exact mem_union_left _ (mem_image_of_mem _ hd)
    · exact mem_union_right _ (mem_image_of_mem _ hd)
  · exact ⟨mem_insert_self _ _, mem_insert_of_mem (mem_image_of_mem _ hv)⟩

/-- **Every call of Dijkstra in a step of the negative-length recursion is realized by a run of
`frProg` within `cNegMach.dij (w + 1) (m + w)` steps** (`m` the darts and `w` the vertices of the
nonempty piece `P`), the size at which `NegCosts.node` charges it. The call is `dijk` on any
lengths `ℓ`, boundary `B`, boundary values `E` and feasible potential `δ` of the piece; `fr` is any
implementation meeting `FRSpec`. The run leaves, for the root and each vertex of the piece
(numbered `idx`), the flag `1` iff it is reachable and its distance. -/
theorem cNegMach_dijk_exec (C : ℕ) {fr : FRFun (Option V)} (hfr : FRSpec fr) {P : Finset D}
    (hP : P.Nonempty) (ℓ : D → ℤ) (B : Finset V) (E δ : V → ℤ) (hδ : (pg N P ℓ).IsPot δ)
    (I : Input) :
    ∃ (Pr : Prm) (c₀ c' : Config) (steps : ℕ) (idx : Option V → ℕ),
      Exec I Pr.W frProg c₀ c' steps ∧
      steps ≤ (cNegMach C).dij ((verts N P).card + 1) (P.card + (verts N P).card) ∧
      c'.output = c₀.output ∧
      ∀ y ∈ dijVerts N P, idx y < Pr.N ∧
        (c'.nmem (Pr.sb + idx y) = 1 ↔ dijk N fr P ℓ B E δ y ≠ none) ∧
        ∀ x, dijk N fr P ℓ B E δ y = some x → c'.rmem (Pr.db + idx y) = x := by
  have hne : dijArcs N P ℓ (verts N P) (initLen B E δ) ≠ [] := by
    obtain ⟨d, hd⟩ := hP
    intro h
    have : (some (N.tail d), some (N.head d), ℓ d) ∈ dijArcs N P ℓ (verts N P) (initLen B E δ) :=
      by unfold dijArcs; simp only [List.mem_append, List.mem_map, mem_toList]; exact
        Or.inl ⟨d, hd, rfl⟩
    rw [h] at this; simp at this
  have := cNegMach_dij_exec_list C (dijVerts N P) (dijArcs N P ℓ (verts N P) (initLen B E δ))
    (mem_insert_self _ _) (fun e he => dijArcs_ends N he) hne (isPot_price hδ) hfr I
  rwa [card_dijVerts, length_dijArcs] at this

end Dijk

end NegSSSP

namespace BKMNW

open Finset WordRAM WordRAM.Machine Monge.FR

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]

/-- **Every call of Dijkstra in the dual graph (the cancellation of the push-back) is realized by
a run of `frProg` within `cMach.fr nf n` steps** (`nf` faces and `n` darts), the size at which
`SubCosts.pushRun` charges it. The call is `dualDijkstra` on nonnegative lengths `ℓ` from any face
`r`; `fr` is any implementation meeting `FRSpec`. The run leaves, for each face `y` (numbered
`idx y`), the flag `1` iff `y` is reachable and its distance. -/
theorem cMach_fr_exec_dual (C C₀ : ℕ) (M : CombMap D V F) [Nonempty D] {fr : FRFun F}
    (hfr : FRSpec fr) {ℓ : D → ℤ} (hℓ : ∀ d, 0 ≤ ℓ d) (r : F) (I : Input) :
    ∃ (Pr : Prm) (c₀ c' : Config) (steps : ℕ) (idx : F → ℕ),
      Exec I Pr.W frProg c₀ c' steps ∧
      steps ≤ (cMach C C₀).fr (Fintype.card F) (Fintype.card D) ∧ c'.output = c₀.output ∧
      ∀ y, idx y < Pr.N ∧ (c'.nmem (Pr.sb + idx y) = 1 ↔ dualDijkstra M fr ℓ r y ≠ none) ∧
        ∀ x, dualDijkstra M fr ℓ r y = some x → c'.rmem (Pr.db + idx y) = x := by
  have hpot : ((emptyDDG (F := F)).union (dualArcs M ℓ)).IsPot 0 := by
    rintro (⟨p, hp, -⟩ | i)
    · simp [emptyDDG] at hp
    · simp only [Pi.zero_apply, zero_add, DDG.union, dualArcs, explicitArcs,
        List.get_eq_getElem, List.getElem_map]
      exact hℓ _
  have hlen : (dualArcs M ℓ).length = Fintype.card D := by
    simp [dualArcs, length_explicitArcs]
  have hne : dualArcs M ℓ ≠ [] := by
    intro h
    have := hlen; rw [h] at this
    exact Fintype.card_ne_zero this.symm
  obtain ⟨Pr, c₀, c', steps, idx, he, hs, hout, hmem⟩ :=
    NegSSSP.cNegMach_dij_exec_list C (univ : Finset F) (dualArcs M ℓ) (mem_univ r)
      (fun _ _ => ⟨mem_univ _, mem_univ _⟩) hne hpot hfr I
  refine ⟨Pr, c₀, c', steps, idx, he, hs.trans ?_, hout, fun y => hmem y (mem_univ y)⟩
  rw [card_univ, hlen]
  show 6300 * (Fintype.card F + Fintype.card D) * lg (Fintype.card F) ≤
    6300 * (Fintype.card F * lg (Fintype.card F) ^ 2 + Fintype.card D * lg (Fintype.card F))
  have h1 : 1 ≤ lg (Fintype.card F) := one_le_lg _
  have h2 : Fintype.card F * lg (Fintype.card F) ≤ Fintype.card F * lg (Fintype.card F) ^ 2 := by
    rw [sq, ← mul_assoc]; exact Nat.le_mul_of_pos_right _ h1
  nlinarith

end BKMNW

end PlanarFlow
