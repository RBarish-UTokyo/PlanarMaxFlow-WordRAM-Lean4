module

public import PlanarFlow.BKMNW.FRDij
public import PlanarFlow.NegSSSP.LinNode
public import PlanarFlow.NegSSSP.ArcSort

/-!
# Calls of FR-Dijkstra on explicit arcs with a given numbering of the vertices

`PlanarFlow.NegSSSP.cNegMach_dij_exec_list` realizes every call `fr emptyDDG E r φ` of
FR-Dijkstra on explicit arcs by a run of `frProg`, numbering the vertices by `Finset.equivFin`
and laying out the arcs `E` in their order. The glue of a node needs the outcome **at numbers it
chose** (the minima `minProg` read the two runs at the vertex numbers of the node), and lays out
the arcs in the order of its own enumeration. This file proves the variant:

* `cNegMach_dij_exec_num`: for any numbering `idx` injective on `S` with values below `n`
  (gaps allowed), any list `Es` of numbered arcs with the same members as the arcs of `E`
  numbered, and any prices `p` with `p (idx y) = φ y` on `S`, every configuration holding the
  input `mkPrm n 1 Dm p (idx r) Es` (`Inp`, `Data`) runs `frProg` within
  `cNegMach.dij n |Es|` steps to the flag `1` at `sb + i` iff `i` is the number of a vertex
  reached, and the distance at `db + idx y`.
* `dijk_exec_num`: the calls of Dijkstra of a step (`NegSSSP.dijk`), with the root numbered `0`
  and the vertex `x` numbered `ν x + 1`, `ν` injective on the vertices of the node below `w`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine Monge.FR BKMNW

section Num

variable {X : Type*} [DecidableEq X]

/-- **Every call of FR-Dijkstra on explicit arcs only is realized by `frProg` at a given
numbering** (see the module docstring). -/
theorem cNegMach_dij_exec_num (C : ℕ) (S : Finset X) (E : List (X × X × ℤ)) {r : X}
    (hr : r ∈ S) (hE : ∀ e ∈ E, e.1 ∈ S ∧ e.2.1 ∈ S) (hE0 : E ≠ []) {φ : X → ℤ}
    (hpot : ((emptyDDG (F := X)).union E).IsPot φ) {fr : FRFun X} (hfr : FRSpec fr)
    {n : ℕ} (idx : X → ℕ) (hidx : ∀ y ∈ S, idx y < n)
    (hinj : ∀ y ∈ S, ∀ z ∈ S, idx y = idx z → y = z) (Es : List (ℕ × ℕ × ℤ))
    (hEs : ∀ a ∈ Es, ∃ a' ∈ E, (idx a'.1, idx a'.2.1, a'.2.2) = a)
    (hEs' : ∀ a' ∈ E, (idx a'.1, idx a'.2.1, a'.2.2) ∈ Es) (Dm : ℕ → ℕ → ℤ) (p : ℕ → ℤ)
    (hp : ∀ y ∈ S, p (idx y) = φ y) (I : Input) (c₀ : Config)
    (hw : WordsBounded (mkPrm n 1 Dm p (idx r) Es).W c₀)
    (hin : Inp (mkPrm n 1 Dm p (idx r) Es) c₀) (hDa : Data (mkPrm n 1 Dm p (idx r) Es) c₀) :
    ∃ c' steps, Exec I (mkPrm n 1 Dm p (idx r) Es).W frProg c₀ c' steps ∧
      steps ≤ (cNegMach C).dij n Es.length ∧ c'.output = c₀.output ∧
      (∀ i < n, (c'.nmem ((mkPrm n 1 Dm p (idx r) Es).sb + i) = 1 ↔
        ∃ y ∈ S, idx y = i ∧ fr emptyDDG E r φ y ≠ none)) ∧
      ∀ y ∈ S, ∀ ℓ, fr emptyDDG E r φ y = some ℓ →
        c'.rmem ((mkPrm n 1 Dm p (idx r) Es).db + idx y) = ℓ := by
  classical
  set GF := (emptyDDG (F := X)).union E with hGF
  set Pr := mkPrm n 1 Dm p (idx r) Es with hPr
  have hn1 : 1 ≤ n := by have := hidx r hr; omega
  have hEsn : ∀ a ∈ Es, a.1 < n ∧ a.2.1 < n := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := hEs a ha
    exact ⟨hidx _ (hE a' ha').1, hidx _ (hE a' ha').2⟩
  have hL : Lay Pr := mkPrm_lay le_rfl hn1 (hidx r hr) fun a ha => (hEsn a ha).2
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
    exact List.length_pos_of_mem (mem_arcList.2 ⟨hEs' a ha, hidx _ (hE a ha).1⟩)
  -- the vertices of the machine in `X ⊕ ℕ`
  let ι : Fin Pr.N → X ⊕ ℕ := fun i =>
    if h : ∃ y ∈ S, idx y = i.1 then .inl h.choose else .inr i.1
  have hιy : ∀ y ∈ S, ∀ (h : idx y < Pr.N), ι ⟨idx y, h⟩ = .inl y := by
    intro y hy h
    have hex : ∃ z ∈ S, idx z = idx y := ⟨y, hy, rfl⟩
    simp only [ι, hex, ↓reduceDIte]
    exact congrArg _ (hinj _ hex.choose_spec.1 _ hy hex.choose_spec.2)
  have hι : Function.Injective ι := by
    intro a b hab
    by_cases ha : ∃ y ∈ S, idx y = a.1
    · obtain ⟨y, hy, hya⟩ := ha
      have ea : ι a = .inl y := by
        have := hιy y hy (hya ▸ a.2); rwa [show (⟨idx y, hya ▸ a.2⟩ : Fin Pr.N) = a from
          Fin.ext hya] at this
      by_cases hb : ∃ z ∈ S, idx z = b.1
      · obtain ⟨z, hz, hzb⟩ := hb
        have eb : ι b = .inl z := by
          have := hιy z hz (hzb ▸ b.2); rwa [show (⟨idx z, hzb ▸ b.2⟩ : Fin Pr.N) = b from
            Fin.ext hzb] at this
        rw [ea, eb] at hab
        exact Fin.ext (hya.symm.trans ((congrArg idx (Sum.inl_injective hab)).trans hzb))
      · have eb : ι b = .inr b.1 := by simp only [ι, hb, ↓reduceDIte]
        rw [ea, eb] at hab; exact absurd hab (by simp)
    · have ea : ι a = .inr a.1 := by simp only [ι, ha, ↓reduceDIte]
      by_cases hb : ∃ z ∈ S, idx z = b.1
      · obtain ⟨z, hz, hzb⟩ := hb
        have eb : ι b = .inl z := by
          have := hιy z hz (hzb ▸ b.2); rwa [show (⟨idx z, hzb ▸ b.2⟩ : Fin Pr.N) = b from
            Fin.ext hzb] at this
        rw [ea, eb] at hab; exact absurd hab (by simp)
      · have eb : ι b = .inr b.1 := by simp only [ι, hb, ↓reduceDIte]
        rw [ea, eb] at hab; exact Fin.ext (Sum.inr_injective hab)
  -- the common graph on `X ⊕ ℕ`
  let EY : List ((X ⊕ ℕ) × (X ⊕ ℕ) × ℤ) := E.map fun a => (.inl a.1, .inl a.2.1, a.2.2)
  set GY := (emptyDDG (F := X ⊕ ℕ)).union EY with hGY
  set Gm := (emptyDDG (F := Fin Pr.N)).union (exArcs Pr hL.N_pos)
  have hEYlen : EY.length = E.length := List.length_map _
  have hEYget : ∀ (j : ℕ) (hj : j < EY.length), EY[j] =
      (.inl (E[j]'(hEYlen ▸ hj)).1, .inl (E[j]'(hEYlen ▸ hj)).2.1, (E[j]'(hEYlen ▸ hj)).2.2) :=
    fun j hj => List.getElem_map _
  -- the arcs of the machine are the arcs of `E`
  have hex_m : ∀ t : Fin (exArcs Pr hL.N_pos).length, ∃ j : Fin EY.length,
      ι (Gm.src (.inr t)) = GY.src (.inr j) ∧ ι (Gm.dst (.inr t)) = GY.dst (.inr j) ∧
        Gm.len (.inr t) = GY.len (.inr j) := by
    intro t
    have ht : t.1 < (arcList n Es).length := lt_of_lt_of_eq t.2 hlenEx
    have hget := hgetEx t.1 t.2
    have ha : (arcList n Es)[t.1] ∈ Es := (mem_arcList.1 (List.getElem_mem ht)).1
    obtain ⟨a, ha', he'⟩ := hEs _ ha
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ha'
    have hjY : j < EY.length := by rw [hEYlen]; exact hj
    refine ⟨⟨j, hjY⟩, ?_, ?_, ?_⟩
    · show ι ((exArcs Pr hL.N_pos)[t.1]).1 = EY[j].1
      rw [hEYget j hjY]
      have h1 : ((exArcs Pr hL.N_pos)[t.1]).1 = ⟨idx E[j].1, hidx _ (hE _ ha').1⟩ := by
        rw [hget]; exact Fin.ext (by rw [hfvv (by rw [← he']; exact hidx _ (hE _ ha').1), ← he'])
      rw [h1, hιy _ (hE _ ha').1 (hidx _ (hE _ ha').1)]
    · show ι ((exArcs Pr hL.N_pos)[t.1]).2.1 = EY[j].2.1
      rw [hEYget j hjY]
      have h1 : ((exArcs Pr hL.N_pos)[t.1]).2.1 = ⟨idx E[j].2.1, hidx _ (hE _ ha').2⟩ := by
        rw [hget]; exact Fin.ext (by rw [hfvv (by rw [← he']; exact hidx _ (hE _ ha').2), ← he'])
      rw [h1, hιy _ (hE _ ha').2 (hidx _ (hE _ ha').2)]
    · show ((exArcs Pr hL.N_pos)[t.1]).2.2 = EY[j].2.2
      rw [hEYget j hjY, hget, ← he']
  have hex_F : ∀ j : Fin EY.length, ∃ t : Fin (exArcs Pr hL.N_pos).length,
      ι (Gm.src (.inr t)) = GY.src (.inr j) ∧ ι (Gm.dst (.inr t)) = GY.dst (.inr j) ∧
        Gm.len (.inr t) = GY.len (.inr j) := by
    intro j
    have hjE : j.1 < E.length := by rw [← hEYlen]; exact j.2
    have hmemE : E[j.1] ∈ E := List.getElem_mem hjE
    have ha : (idx E[j.1].1, idx E[j.1].2.1, E[j.1].2.2) ∈ arcList n Es :=
      mem_arcList.2 ⟨hEs' _ hmemE, hidx _ (hE _ hmemE).1⟩
    obtain ⟨t, ht, hta⟩ := List.mem_iff_getElem.1 ha
    have ht' : t < (exArcs Pr hL.N_pos).length := by rw [hlenEx]; exact ht
    have hget := hgetEx t ht'
    refine ⟨⟨t, ht'⟩, ?_, ?_, ?_⟩
    · show ι ((exArcs Pr hL.N_pos)[t]).1 = EY[j.1].1
      rw [hEYget j.1 j.2]
      have h1 : ((exArcs Pr hL.N_pos)[t]).1 = ⟨idx E[j.1].1, hidx _ (hE _ hmemE).1⟩ := by
        rw [hget]; exact Fin.ext (by simp only [hta]; exact hfvv (hidx _ (hE _ hmemE).1))
      rw [h1, hιy _ (hE _ hmemE).1 (hidx _ (hE _ hmemE).1)]
    · show ι ((exArcs Pr hL.N_pos)[t]).2.1 = EY[j.1].2.1
      rw [hEYget j.1 j.2]
      have h1 : ((exArcs Pr hL.N_pos)[t]).2.1 = ⟨idx E[j.1].2.1, hidx _ (hE _ hmemE).2⟩ := by
        rw [hget]; exact Fin.ext (by simp only [hta]; exact hfvv (hidx _ (hE _ hmemE).2))
      rw [h1, hιy _ (hE _ hmemE).2 (hidx _ (hE _ hmemE).2)]
    · show ((exArcs Pr hL.N_pos)[t]).2.2 = EY[j.1].2.2
      rw [hEYget j.1 j.2, hget]; simp only [hta]
  -- the two transfers
  have htr : Transfer Gm GY ι := by
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
  have htr2 : Transfer GF GY Sum.inl := by
    refine ⟨Sum.inl_injective, ?_, ?_⟩
    · rintro (⟨_, h, -⟩ | j)
      · simp [emptyDDG] at h
      · have hjY : j.1 < EY.length := by rw [hEYlen]; exact j.2
        refine ⟨.inr ⟨j.1, hjY⟩, ?_, ?_, ?_⟩
        · show EY[j.1].1 = .inl E[j.1].1
          rw [hEYget j.1 hjY]
        · show EY[j.1].2.1 = .inl E[j.1].2.1
          rw [hEYget j.1 hjY]
        · show EY[j.1].2.2 = E[j.1].2.2
          rw [hEYget j.1 hjY]
    · rintro (⟨_, h, -⟩ | j) x hx
      · simp [emptyDDG] at h
      · left
        have hjE : j.1 < E.length := by rw [← hEYlen]; exact j.2
        refine ⟨.inr ⟨j.1, hjE⟩, ?_, ?_, ?_⟩
        · have : EY[j.1].1 = .inl x := hx
          rw [hEYget j.1 j.2] at this
          exact Sum.inl_injective this
        · show Sum.inl E[j.1].2.1 = EY[j.1].2.1
          rw [hEYget j.1 j.2]
        · show E[j.1].2.2 = EY[j.1].2.2
          rw [hEYget j.1 j.2]
  -- the potential of the machine's input
  have hpm : Gm.IsPot (fun y => Pr.p y) := by
    rintro (⟨_, h, -⟩ | t)
    · simp [emptyDDG] at h
    · have ht : t.1 < (arcList n Es).length := lt_of_lt_of_eq t.2 hlenEx
      have hget := hgetEx t.1 t.2
      have ha : (arcList n Es)[t.1] ∈ Es := (mem_arcList.1 (List.getElem_mem ht)).1
      obtain ⟨a, ha', he'⟩ := hEs _ ha
      obtain ⟨j, hj, hja⟩ := List.mem_iff_getElem.1 ha'
      have hpj := hpot (.inr ⟨j, hj⟩)
      change φ E[j].2.1 ≤ φ E[j].1 + E[j].2.2 at hpj
      rw [hja] at hpj
      show p ((exArcs Pr hL.N_pos)[t.1]).2.1 ≤ p ((exArcs Pr hL.N_pos)[t.1]).1 +
        ((exArcs Pr hL.N_pos)[t.1]).2.2
      rw [hget, hfvv (by rw [← he']; exact hidx _ (hE _ ha').2),
        hfvv (by rw [← he']; exact hidx _ (hE _ ha').1), ← he']
      simp only
      rw [hp _ (hE _ ha').1, hp _ (hE _ ha').2]
      exact hpj
  -- the run
  obtain ⟨c', steps, he, hsteps, -, hout, δ, hδ, hmem⟩ :=
    cNegMach_dij_exec (I := I) C hL rfl mkPrm_off_zero hm_pos hpm c₀ hw hin hDa
  have hroot : ι (fv Pr hL.N_pos Pr.r) = .inl r := by
    have : fv Pr hL.N_pos Pr.r = ⟨idx r, hidx r hr⟩ := Fin.ext (hfvv (hidx r hr))
    rw [this, hιy r hr (hidx r hr)]
  have hδY := isDist_transfer htr hδ
  rw [hroot] at hδY
  have hδF := isDist_transfer htr2 (hfr emptyDDG E r φ hpot)
  have heq := hδY.unique hδF
  have key : ∀ i : Fin Pr.N, δ i = htr2.pull (fr emptyDDG E r φ) (ι i) := by
    intro i; rw [← heq, htr.pull_iota]
  refine ⟨c', steps, he, ?_, hout, fun i hi => ?_, fun y hy ℓ hℓ => ?_⟩
  · refine hsteps.trans ?_
    have hmk : Pr.m ≤ Es.length := by
      show (arcList n Es).length ≤ Es.length
      exact length_pre_le Es n
    show 6300 * (n + Pr.m) * lg n ≤ 6300 * (n + Es.length) * lg n
    gcongr
  · rw [(hmem ⟨i, hi⟩).1, key ⟨i, hi⟩]
    by_cases hS : ∃ y ∈ S, idx y = i
    · obtain ⟨y, hy, rfl⟩ := hS
      rw [hιy y hy hi, htr2.pull_iota]
      exact ⟨fun h => ⟨y, hy, rfl, h⟩, fun ⟨z, hz, hzy, h⟩ => by
        rwa [← hinj z hz y hy hzy]⟩
    · have hι' : ι ⟨i, hi⟩ = .inr i := by simp only [ι, hS, ↓reduceDIte]
      rw [hι']
      have : htr2.pull (fr emptyDDG E r φ) (.inr i) = none := by
        unfold Transfer.pull; simp
      rw [this]
      exact ⟨fun h => absurd rfl h, fun ⟨y, hy, hyi, _⟩ => absurd ⟨y, hy, hyi⟩ hS⟩
  · have h1 := (hmem ⟨idx y, hidx y hy⟩).2 ℓ
    rw [key, hιy y hy (hidx y hy), htr2.pull_iota] at h1
    exact h1 hℓ

end Num

/-! ### The calls of Dijkstra of a step at the vertex numbers of the node -/

section Node

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {N : CombMap D V F}

/-- The numbering of the vertices of a call of Dijkstra: the root `0`, the vertex `x` at
`ν x + 1`. -/
def numV (ν : V → ℕ) : Option V → ℕ
  | none => 0
  | some x => ν x + 1

lemma verts_sub_of_sub {P P' : Finset D} (h : P ⊆ P') : verts N P ⊆ verts N P' :=
  union_subset_union (image_subset_image h) (image_subset_image h)

/-- **The calls of Dijkstra of a step at the vertex numbers of the node**: for a nonempty part
`X` of a node in the plain encoding (vertex numbers `ν` below `w`), with the root numbered `0`
and the vertex `x` numbered `ν x + 1`, any list `Es` of the arcs `dijArcs` numbered, and prices
`p` (`p 0` the price of the root, `p (ν x + 1) = δ x`), every configuration holding the input
`mkPrm (w + 1) 1 Dm p 0 Es` runs `frProg` within `cNegMach.dij (w + 1) |Es|` steps to the flag
`1` at `sb + (v + 1)` (`v < w`) iff `v` is the number of a vertex reached by `dijk`, and the
distance of the vertex `x` at `db + (ν x + 1)`. -/
theorem dijk_exec_num (C : ℕ) {fr : FRFun (Option V)} (hfr : FRSpec fr) {P₀ P₁ : Finset D}
    {m w : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V} (h : NodeEnc N P₀ P₁ m w e ν ι)
    {X : Finset D} (hX : X ⊆ P₀ ∪ P₁) (hXn : X.Nonempty) (ℓ : D → ℤ) (B : Finset V)
    (E δ : V → ℤ) (hδ : (pg N X ℓ).IsPot δ) (Es : List (ℕ × ℕ × ℤ))
    (hEs : ∀ a ∈ Es, ∃ a' ∈ dijArcs N X ℓ (verts N X) (initLen B E δ),
      (numV ν a'.1, numV ν a'.2.1, a'.2.2) = a)
    (hEs' : ∀ a' ∈ dijArcs N X ℓ (verts N X) (initLen B E δ),
      (numV ν a'.1, numV ν a'.2.1, a'.2.2) ∈ Es)
    (Dm : ℕ → ℕ → ℤ) (p : ℕ → ℤ) (hp0 : p 0 = price B E δ none)
    (hpv : ∀ x ∈ verts N (P₀ ∪ P₁), p (ν x + 1) = δ x) (I : Input) (c₀ : Config)
    (hw : WordsBounded (mkPrm (w + 1) 1 Dm p 0 Es).W c₀)
    (hin : Inp (mkPrm (w + 1) 1 Dm p 0 Es) c₀) (hDa : Data (mkPrm (w + 1) 1 Dm p 0 Es) c₀) :
    ∃ c' steps, Exec I (mkPrm (w + 1) 1 Dm p 0 Es).W frProg c₀ c' steps ∧
      steps ≤ (cNegMach C).dij (w + 1) Es.length ∧ c'.output = c₀.output ∧
      (∀ v < w, (c'.nmem ((mkPrm (w + 1) 1 Dm p 0 Es).sb + (v + 1)) = 1 ↔
        ∃ x ∈ verts N (P₀ ∪ P₁), ν x = v ∧ dijk N fr X ℓ B E δ (some x) ≠ none)) ∧
      ∀ x ∈ verts N (P₀ ∪ P₁), ∀ z, dijk N fr X ℓ B E δ (some x) = some z →
        c'.rmem ((mkPrm (w + 1) 1 Dm p 0 Es).db + (ν x + 1)) = z := by
  have hne : dijArcs N X ℓ (verts N X) (initLen B E δ) ≠ [] := by
    obtain ⟨d, hd⟩ := hXn
    intro h'
    have : (some (N.tail d), some (N.head d), ℓ d) ∈ dijArcs N X ℓ (verts N X) (initLen B E δ) :=
      by unfold dijArcs; simp only [List.mem_append, List.mem_map, mem_toList]; exact
        Or.inl ⟨d, hd, rfl⟩
    rw [h'] at this; simp at this
  have hsub : dijVerts N X ⊆ dijVerts N (P₀ ∪ P₁) :=
    insert_subset_insert _ (image_subset_image (verts_sub_of_sub hX))
  have hmemS : ∀ y ∈ dijVerts N (P₀ ∪ P₁), y = none ∨ ∃ x ∈ verts N (P₀ ∪ P₁), y = some x := by
    intro y hy
    rcases mem_insert.1 hy with rfl | hy
    · exact Or.inl rfl
    · obtain ⟨x, hx, rfl⟩ := mem_image.1 hy; exact Or.inr ⟨x, hx, rfl⟩
  have hidx : ∀ y ∈ dijVerts N (P₀ ∪ P₁), numV ν y < w + 1 := by
    intro y hy
    rcases hmemS y hy with rfl | ⟨x, hx, rfl⟩
    · simp [numV]
    · have := h.lt x hx; simp only [numV]; omega
  have hinj : ∀ y ∈ dijVerts N (P₀ ∪ P₁), ∀ z ∈ dijVerts N (P₀ ∪ P₁), numV ν y = numV ν z →
      y = z := by
    intro y hy z hz hyz
    rcases hmemS y hy with rfl | ⟨x, hx, rfl⟩ <;> rcases hmemS z hz with rfl | ⟨x', hx', rfl⟩
    · rfl
    · simp [numV] at hyz
    · simp [numV] at hyz
    · simp only [numV, add_left_inj] at hyz
      rw [← h.inv x hx, ← h.inv x' hx', hyz]
  have hp : ∀ y ∈ dijVerts N (P₀ ∪ P₁), p (numV ν y) = price B E δ y := by
    intro y hy
    rcases hmemS y hy with rfl | ⟨x, hx, rfl⟩
    · exact hp0
    · exact hpv x hx
  obtain ⟨c', steps, hex, hst, hout, hfl, hval⟩ := cNegMach_dij_exec_num C (dijVerts N (P₀ ∪ P₁))
    (dijArcs N X ℓ (verts N X) (initLen B E δ)) (mem_insert_self _ _)
    (fun a ha => ⟨hsub (dijArcs_ends N ha).1, hsub (dijArcs_ends N ha).2⟩) hne (isPot_price hδ) hfr
    (numV ν) hidx hinj Es hEs hEs' Dm p hp I c₀ hw hin hDa
  refine ⟨c', steps, hex, hst, hout, fun v hv => ?_, fun x hx z hz => ?_⟩
  · refine (hfl (v + 1) (by omega)).trans ?_
    constructor
    · rintro ⟨y, hy, hyv, hne⟩
      rcases hmemS y hy with rfl | ⟨x, hx, rfl⟩
      · simp [numV] at hyv
      · exact ⟨x, hx, by simp only [numV] at hyv; omega, hne⟩
    · rintro ⟨x, hx, rfl, hne⟩
      exact ⟨some x, mem_insert_of_mem (mem_image_of_mem _ hx), rfl, hne⟩
  · exact hval (some x) (mem_insert_of_mem (mem_image_of_mem _ hx)) z hz

lemma sum_enum {b : ℕ} {β : ℕ → V} {B : Finset V} (hβ : IsEnum b β B) (f : V → ℝ) :
    ∑ i ∈ range b, f (β i) = ∑ v ∈ B, f v :=
  sum_nbij β (fun i hi => hβ.mem i (mem_range.1 hi))
    (fun i hi j hj hij => hβ.inj i (mem_range.1 hi) j (mem_range.1 hj) hij)
    (fun v hv => by obtain ⟨i, hi, rfl⟩ := hβ.surj v hv; exact ⟨i, mem_range.2 hi, rfl⟩)
    (fun _ _ => rfl)

/-- **The outputs of `cProg` and `pProg` are the values of `NegSSSP.step`**: at the boundary
`B` enumerated by `β` with vertex numbers `ν (β i)`, the sum of `cProg` is the lowering `C`, the
price of the root of `pProg` is `price B (E - C) δ none`, and the initial lengths at the vertex
numbers are `initLen B (E - C) δ`. -/
theorem arith_node {P₀ P₁ : Finset D} {m w : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V}
    (h : NodeEnc N P₀ P₁ m w e ν ι) {b : ℕ} {β : ℕ → V} (hβ : IsEnum b β (bdry N P₀ P₁))
    (E δ₀ δ₁ δ : V → ℤ) (C : ℤ) (I : ℕ → ℝ)
    (hb : ∀ i < b, I (ν (β i)) = (E (β i) : ℝ) - C)
    (ho : ∀ v < w, (∀ i < b, ν (β i) ≠ v) → I v = δ (ι v)) :
    (∑ i ∈ range b, (|(E (β i) : ℝ) - δ₀ (β i)| + |(E (β i) : ℝ) - δ₁ (β i)|) =
        ((∑ v ∈ bdry N P₀ P₁, (|E v - δ₀ v| + |E v - δ₁ v|) : ℤ) : ℝ)) ∧
      (∑ i ∈ range b, |(δ (β i) : ℝ) - ((E (β i) : ℝ) - C)| =
        ((price (bdry N P₀ P₁) (fun y => E y - C) δ none : ℤ) : ℝ)) ∧
      ∀ x ∈ verts N (P₀ ∪ P₁), I (ν x) = initLen (bdry N P₀ P₁) (fun y => E y - C) δ x := by
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · rw [sum_enum hβ (fun v => |(E v : ℝ) - δ₀ v| + |(E v : ℝ) - δ₁ v|)]; push_cast; rfl
  · rw [sum_enum hβ (fun v => |(δ v : ℝ) - ((E v : ℝ) - C)|)]; simp only [price]; push_cast
    rfl
  · unfold initLen
    by_cases hB : x ∈ bdry N P₀ P₁
    · obtain ⟨i, hi, rfl⟩ := hβ.surj x hB
      rw [hb i hi, ite_eq_left_of_eq_true _ _ (eq_true hB)]; push_cast; rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hB), ho _ (h.lt x hx) fun i hi hi' => hB ?_,
        h.inv x hx]
      have hβv : β i ∈ verts N (P₀ ∪ P₁) := bdry_sub_verts (hβ.mem i hi)
      rw [← h.inv x hx, ← hi', h.inv _ hβv]; exact hβ.mem i hi

open Classical in
/-- The outcome of a run of Dijkstra at the vertex number `v`: the outcome at the vertex of
number `v`, none at a number of no vertex of the node. -/
noncomputable def oNum (N : CombMap D V F) (P₀ P₁ : Finset D) (ν : V → ℕ) (ι : ℕ → V)
    (Dk : Option V → Option ℤ) (v : ℕ) : Option ℤ :=
  if ∃ x ∈ verts N (P₀ ∪ P₁), ν x = v then Dk (some (ι v)) else none

/-- **The normalized flags and the distances of a run of Dijkstra at the vertex numbers are the
data of `minProg`**: from the facts of `dijk_exec_num` on the run `c₀` (settled flags at `Sb`,
distances at `Rb`, vertex `x` at `ν x + 1`) and a configuration with the flags normalized
(`nrmProg`) at `Fb + v` and the distances at `Vb + v`, the flag at `Fb + v` is `1` iff
`oNum … v` is some, and the value is its distance. -/
theorem minIn_of_run {P₀ P₁ : Finset D} {m w : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V}
    (h : NodeEnc N P₀ P₁ m w e ν ι) {Dk : Option V → Option ℤ} {Sb Rb Fb Vb : ℕ}
    {c₀ cm : Config}
    (hfl : ∀ v < w, (c₀.nmem (Sb + (v + 1)) = 1 ↔
      ∃ x ∈ verts N (P₀ ∪ P₁), ν x = v ∧ Dk (some x) ≠ none))
    (hval : ∀ x ∈ verts N (P₀ ∪ P₁), ∀ z, Dk (some x) = some z → c₀.rmem (Rb + (ν x + 1)) = z)
    (hF : ∀ v < w, cm.nmem (Fb + v) = if c₀.nmem (Sb + (v + 1)) = 1 then 1 else 0)
    (hV : ∀ v < w, cm.rmem (Vb + v) = c₀.rmem (Rb + (v + 1))) :
    (∀ v < w, cm.nmem (Fb + v) = if (oNum N P₀ P₁ ν ι Dk v).isSome then 1 else 0) ∧
      (∀ v < w, ∀ z, oNum N P₀ P₁ ν ι Dk v = some z → cm.rmem (Vb + v) = z) := by
  refine ⟨fun v hv => ?_, fun v hv z hz => ?_⟩
  · rw [hF v hv]
    have hiff : c₀.nmem (Sb + (v + 1)) = 1 ↔ (oNum N P₀ P₁ ν ι Dk v).isSome := by
      rw [hfl v hv]
      unfold oNum
      constructor
      · rintro ⟨x, hx, rfl, hne⟩
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨x, hx, rfl⟩), h.inv x hx]
        exact Option.isSome_iff_ne_none.2 hne
      · intro hs
        by_cases hex : ∃ x ∈ verts N (P₀ ∪ P₁), ν x = v
        · obtain ⟨x, hx, rfl⟩ := hex
          rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨x, hx, rfl⟩), h.inv x hx] at hs
          exact ⟨x, hx, rfl, Option.isSome_iff_ne_none.1 hs⟩
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hex)] at hs; simp at hs
    by_cases h1 : c₀.nmem (Sb + (v + 1)) = 1
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1),
        ite_eq_left_of_eq_true _ _ (eq_true (hiff.1 h1))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1),
        ite_eq_right_of_eq_false _ _ (eq_false fun h' => h1 (hiff.2 h'))]
  · unfold oNum at hz
    by_cases hex : ∃ x ∈ verts N (P₀ ∪ P₁), ν x = v
    · obtain ⟨x, hx, rfl⟩ := hex
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨x, hx, rfl⟩), h.inv x hx] at hz
      rw [hV _ hv]; exact hval x hx z hz
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hex)] at hz; simp at hz

/-- **The minima of the two runs at the vertex numbers**: with the data of `minProg` from two
runs (`minIn_of_run`), `minProg` writes the value of `NegSSSP.step` at `x`,
`(omin (D₀ (some x)) (D₁ (some x))).getD 0`, at `Ob + ν x` for every vertex `x` of the node,
within `21 w + 3` steps. -/
theorem minProg_node_num {P₀ P₁ : Finset D} {m w : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V}
    (h : NodeEnc N P₀ P₁ m w e ν ι) {D₀ D₁ : Option V → Option ℤ} {F0 V0 F1 V1 Ob W : ℕ}
    {I : Input} (hL : MinLay w F0 V0 F1 V1 Ob W) (cm : Config) (hcm : WordsBounded W cm)
    (hIm : MinIn w F0 V0 F1 V1 Ob (oNum N P₀ P₁ ν ι D₀) (oNum N P₀ P₁ ν ι D₁) cm) :
    ∃ c' k, Exec I W minProg cm c' k ∧ k ≤ 21 * w + 3 ∧
      (∀ x ∈ verts N (P₀ ∪ P₁),
        c'.rmem (Ob + ν x) = ((omin (D₀ (some x)) (D₁ (some x))).getD 0 : ℤ)) ∧
      (∀ a, (a < Ob ∨ Ob + w ≤ a) → c'.rmem a = cm.rmem a) ∧ c'.nmem = cm.nmem := by
  obtain ⟨c', k, hex, hk, hv, hm, hn, -, -⟩ := minProg_exec (P := I) hL cm hcm hIm
  refine ⟨c', k, hex, hk, fun x hx => ?_, hm, hn⟩
  have e : ∀ Dk : Option V → Option ℤ, oNum N P₀ P₁ ν ι Dk (ν x) = Dk (some x) := fun Dk => by
    unfold oNum; rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨x, hx, rfl⟩), h.inv x hx]
  rw [hv _ (h.lt x hx), e, e]

lemma mem_csList {T H K : ℕ → ℕ} {Lz : ℕ → ℤ} {a : ℕ × ℕ × ℤ} :
    ∀ n, a ∈ csList T H K Lz n ↔ ∃ i < n, K i ≠ 0 ∧ a = (T i, H i, Lz i)
  | 0 => by simp [csList]
  | n + 1 => by
    rw [csList, List.mem_append, mem_csList n]
    constructor
    · rintro (⟨i, hi, h1, h2⟩ | h)
      · exact ⟨i, by omega, h1, h2⟩
      · by_cases hK : K n = 0
        · simp [hK] at h
        · simp only [hK, ↓reduceIte, List.mem_singleton] at h
          exact ⟨n, by omega, hK, h⟩
    · rintro ⟨i, hi, h1, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inl ⟨i, hi, h1, h2⟩
      · right; simp [h1, h2]

lemma encS_eq_iff {P₀ P₁ : Finset D} {e : ℕ → D} (hd : Disjoint P₀ P₁) {i s : ℕ} (hs : s ≤ 1)
    (hi : e i ∈ P₀ ∪ P₁) : encS P₀ e i = s ↔ e i ∈ partOf P₀ P₁ s := by
  unfold encS partOf
  rcases mem_union.1 hi with h0 | h1
  · have : e i ∉ P₁ := disjoint_left.1 hd h0
    by_cases hs0 : s = 0 <;> simp [h0, this, hs0] <;> omega
  · have : e i ∉ P₀ := fun h => disjoint_left.1 hd h h1
    by_cases hs0 : s = 0 <;> simp [h1, this, hs0] <;> omega

/-- **The candidate arcs of `aProg` are the arcs of the call of Dijkstra, numbered**: on the
plain encoding of a node, the kept arcs of the arrays written by `aProg` for the side `s` (the
darts at `d < m`, the arcs from the root at `m + v`; the keep flag of `m + v` nonzero iff the
vertex `v` is an end of a dart of the side), with the lengths `ℓ` and `initLen B E δ`, are the
arcs `dijArcs` of the part `partOf P₀ P₁ s` numbered by `numV ν` (the hypotheses of
`dijk_exec_num`). -/
theorem csList_dijArcs {P₀ P₁ : Finset D} {m w : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V}
    (h : NodeEnc N P₀ P₁ m w e ν ι) {s : ℕ} (hs : s ≤ 1) (ℓ : D → ℤ) (B : Finset V)
    (E δ : V → ℤ) (Tq Hq K : ℕ → ℕ) (Lz : ℕ → ℤ)
    (hT : ∀ i < m, Tq i = encT N e ν i + 1 ∧ Hq i = encH N e ν i + 1 ∧
      (K i ≠ 0 ↔ encS P₀ e i = s) ∧ Lz i = ℓ (e i))
    (hV : ∀ v < w, Tq (m + v) = 0 ∧ Hq (m + v) = v + 1 ∧
      (K (m + v) ≠ 0 ↔ InSide (encT N e ν) (encH N e ν) (encS P₀ e) m s v) ∧
      Lz (m + v) = initLen B E δ (ι v)) :
    (∀ a ∈ csList Tq Hq K Lz (m + w), ∃ a' ∈ dijArcs N (partOf P₀ P₁ s) ℓ
        (verts N (partOf P₀ P₁ s)) (initLen B E δ), (numV ν a'.1, numV ν a'.2.1, a'.2.2) = a) ∧
      (∀ a' ∈ dijArcs N (partOf P₀ P₁ s) ℓ (verts N (partOf P₀ P₁ s)) (initLen B E δ),
        (numV ν a'.1, numV ν a'.2.1, a'.2.2) ∈ csList Tq Hq K Lz (m + w)) := by
  have hmemD : ∀ a', a' ∈ dijArcs N (partOf P₀ P₁ s) ℓ (verts N (partOf P₀ P₁ s))
      (initLen B E δ) ↔ (∃ d ∈ partOf P₀ P₁ s, a' = (some (N.tail d), some (N.head d), ℓ d)) ∨
        ∃ x ∈ verts N (partOf P₀ P₁ s), a' = (none, some x, initLen B E δ x) := by
    intro a'
    unfold dijArcs
    simp only [List.mem_append, List.mem_map, mem_toList]
    constructor
    · rintro (⟨d, hd, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact Or.inl ⟨d, hd, rfl⟩
      · exact Or.inr ⟨x, hx, rfl⟩
    · rintro (⟨d, hd, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact Or.inl ⟨d, hd, rfl⟩
      · exact Or.inr ⟨x, hx, rfl⟩
  have hsub : partOf P₀ P₁ s ⊆ P₀ ∪ P₁ := by
    unfold partOf; split_ifs
    · exact subset_union_left
    · exact subset_union_right
  have hvsub : verts N (partOf P₀ P₁ s) ⊆ verts N (P₀ ∪ P₁) := verts_sub_of_sub hsub
  refine ⟨fun a ha => ?_, fun a' ha' => ?_⟩
  · obtain ⟨i, hi, hK, rfl⟩ := (mem_csList _).1 ha
    by_cases him : i < m
    · obtain ⟨h1, h2, h3, h4⟩ := hT i him
      have hei := h.enum.mem i him
      refine ⟨(some (N.tail (e i)), some (N.head (e i)), ℓ (e i)),
        (hmemD _).2 (Or.inl ⟨e i, (encS_eq_iff h.disj hs hei).1 (h3.1 hK), rfl⟩), ?_⟩
      simp only [numV, h1, h2, h4, encT, encH]
    · obtain ⟨v, rfl⟩ : ∃ v, i = m + v := ⟨i - m, by omega⟩
      obtain ⟨h1, h2, h3, h4⟩ := hV v (by omega)
      obtain ⟨d, hd, hSd, hTH⟩ := h3.1 hK
      have hed := h.enum.mem d hd
      obtain ⟨x, hx, hxv⟩ : ∃ x ∈ verts N (P₀ ∪ P₁), ν x = v := by
        rcases hTH with h' | h'
        · exact ⟨N.tail (e d), mem_verts.2 ⟨e d, hed, Or.inl rfl⟩, h'⟩
        · exact ⟨N.head (e d), mem_verts.2 ⟨e d, hed, Or.inr rfl⟩, h'⟩
      have hxs : x ∈ verts N (partOf P₀ P₁ s) := by
        rw [← inSide_enc h hs hx, hxv]; exact ⟨d, hd, hSd, hTH⟩
      refine ⟨(none, some x, initLen B E δ x), (hmemD _).2 (Or.inr ⟨x, hxs, rfl⟩), ?_⟩
      rw [h1, h2, h4, ← hxv, h.inv x hx]; rfl
  · rcases (hmemD a').1 ha' with ⟨d, hd, rfl⟩ | ⟨x, hx, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := h.enum.surj d (hsub hd)
      obtain ⟨h1, h2, h3, h4⟩ := hT i hi
      refine (mem_csList _).2 ⟨i, by omega, h3.2 ((encS_eq_iff h.disj hs (hsub hd)).2 hd), ?_⟩
      simp only [numV, h1, h2, h4, encT, encH]
    · have hx' := hvsub hx
      have hv := h.lt x hx'
      obtain ⟨h1, h2, h3, h4⟩ := hV (ν x) hv
      refine (mem_csList _).2 ⟨m + ν x, by omega, h3.2 ((inSide_enc h hs hx').2 hx), ?_⟩
      rw [h1, h2, h4, h.inv x hx']; rfl

end Node

end NegSSSP

end PlanarFlow
