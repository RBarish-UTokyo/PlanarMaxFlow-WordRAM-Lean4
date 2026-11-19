module

public import PlanarFlow.BKMNW.FRFixPath
public import PlanarFlow.BKMNW.FrCall

/-!
# FR-Dijkstra of a stage of FixConservationOnPath with explicit corners, on natural words

`cMach_fr_exec_fixPath_faces` realizes every FR call of `fixPath` by a run of `frProg`, with the
corners and their numbering chosen *classically* (`exists_fixCornersInj`). A program must choose
them itself; here the corners are **any** numbering `β` of the faces along the path (injective on
`[0, b)`, onto `P.faces`, with inverse `idx`), the input any list `Es` equal to the explicit arcs
numbered by `idx`, and the result the natural one of the fixed program (`FrFix.FResN`, as left by
`FrFix.frCall_exec`):

* `frDec P L w` (the integer of a residue word), **`FResN.dijkRun`**, **`FResN.isDist`** (the
  natural result gives the distances of the Monge library's graph);
* **`fr_corners_eq`**: for every face `y` along the path, the flag at `Fb + idx y` is `1` iff
  `fr … y ≠ none`, and then `fr … y = some (frDec … (nm (Rb + idx y)))` — for any `fr` meeting
  `FRSpec` (so for `frRef`). The crossing inequality is a hypothesis (`crossing_fixPath` for
  increasing first positions around the path).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine Monge.FR

/-! ### The natural result gives the distances -/

section Res

variable {P : Prm}

/-- The integer of a residue word of the natural FR program. -/
def frDec (P : Prm) (L w : ℕ) : ℤ := if w ≤ frH P L then (w : ℤ) else (w : ℤ) - frM P L

/-- **The natural result is a run of Dijkstra's algorithm** on the Monge library's graph. -/
theorem FResN.dijkRun (hL : Lay P) (h0 : P.off 0 = 0) {L K : ℕ} {v : ℕ → ℕ} {dd : ℕ → ℤ}
    {nm : ℕ → ℕ} {Fb Rb : ℕ} (h : FrFix.FResN P L K v dd nm Fb Rb) :
    Monge.DijkRun (frGraph P hL.N_pos) (fun y => P.p y) (fv P hL.N_pos P.r) K
      (fun i => fv P hL.N_pos (v i)) dd := by
  obtain ⟨hR, hK, hvl, hcl, -, -⟩ := h
  have hN := hL.N_pos
  refine ⟨hK, show fv P hN (v 0) = _ by rw [hR.root hK], hR.root_d hK, fun i j hi hj e => ?_,
    fun k hk0 hk => ?_, fun k hk i hik a ha hy => ?_, fun i hi a ha => ?_⟩
  · exact hR.inj i j hi hj (fv_inj (hvl i hi) (hvl j hj) e)
  · obtain ⟨i, hi, ℓ, harc, he⟩ := hR.parent k hk0 hk
    obtain ⟨a, h1, h2, h3⟩ := arc_of_isArc hL (hvl i (by omega)) harc
    exact ⟨i, hi, a, h1, h2, by rw [h3, he]⟩
  · have harc := isArc_of_arc hL h0 (hvl i (by omega)) a ha
    have := hR.least k hk i hik _ _ harc fun j hj e => hy j hj (by
      apply Fin.ext; rw [fv_val (hvl j (by omega))]; exact e)
    show (dd k : ℤ) - P.p (fv P hN (v k) : ℕ) ≤ _
    rw [fv_val (hvl k hk)]; exact this
  · have harc := isArc_of_arc hL h0 (hvl i hi) a ha
    obtain ⟨j, hj, e⟩ := hcl i hi _ _ harc
    exact ⟨j, hj, Fin.ext (by rw [fv_val (hvl j hj)]; exact e)⟩

/-- **The natural result gives the distances of the specification** in the union of the dense
distance graph of the corners and the explicit arcs: the flag at `Fb + y` is `1` iff `y` is
reached, and the distance is the integer of the residue word at `Rb + y`. -/
theorem FResN.isDist (hL : Lay P) (h0 : P.off 0 = 0)
    (hA : Nonempty (Monge.Arc P.b ⊕ Fin (exArcs P hL.N_pos).length))
    (hp : ((faceDDG (fv P hL.N_pos) P.b P.D).union (exArcs P hL.N_pos)).IsPot (fun y => P.p y))
    {L K : ℕ} {v : ℕ → ℕ} {dd : ℕ → ℤ} {nm : ℕ → ℕ} {Fb Rb : ℕ}
    (h : FrFix.FResN P L K v dd nm Fb Rb) :
    ∃ δ : Fin P.N → Option ℤ,
      IsDist ((faceDDG (fv P hL.N_pos) P.b P.D).union (exArcs P hL.N_pos)) (fv P hL.N_pos P.r) δ ∧
      ∀ y : Fin P.N, (nm (Fb + y) = 1 ↔ δ y ≠ none) ∧
        ∀ ℓ, δ y = some ℓ → ℓ = frDec P L (nm (Rb + y)) := by
  classical
  have hrun := FResN.dijkRun hL h0 h
  have hp' := (isPot_ddgPlus_iff (fv_inj_corner hL)).2 hp
  have hg := hrun.gdist hp'
  obtain ⟨-, -, hvl, -, hsf, hdist⟩ := h
  have hvy : ∀ (y : Fin P.N) i, i < K → (fv P hL.N_pos (v i) = y ↔ v i = y) := fun y i hi =>
    ⟨fun h => by rw [← h, fv_val (hvl i hi)], fun h => Fin.ext (by rw [fv_val (hvl i hi)]; exact h)⟩
  refine ⟨_, (gdist_ddgPlus_iff (fv_inj_corner hL)).1 hg, fun y => ⟨?_, fun ℓ hℓ => ?_⟩⟩
  · rw [hsf y y.2]
    split_ifs with h
    · simp only [ne_eq, reduceCtorEq, not_false_eq_true, iff_true]
      obtain ⟨i, hi, hv⟩ := h
      exact ⟨i, hi, (hvy y i hi).1 hv⟩
    · simp only [ne_eq, not_true_eq_false, iff_false]
      rintro ⟨i, hi, hv⟩
      exact h ⟨i, hi, (hvy y i hi).2 hv⟩
  · split_ifs at hℓ with hy
    obtain ⟨hi, hv⟩ := Classical.choose_spec hy
    rw [← Option.some_inj.1 hℓ, hdist _ hi, (hvy y _ hi).1 hv]
    rfl

end Res

/-! ### The corners chosen by the program -/

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **FR-Dijkstra of a stage of `fixPath` from the natural result of the fixed program, with
explicit corners.** The corners `β 0, …, β (b-1)` are the faces along the path, each once
(inverse `idx`); the input is `mkPrm b b Dm pm (idx r) Es` with `Dm i j` the length of the dense
distance graph between `β i` and `β j` and `pm x = φ (β x)` (for `i, j, x < b`), `Es` the explicit arcs numbered by
`idx`; the crossing inequality holds; `φ` is feasible. Then for every face `y` along the path,
the flag at `Fb + idx y` tells whether `fr … y` is a value, and its value is the integer of the
residue word at `Rb + idx y`. -/
theorem fr_corners_eq (P : SPath M) (hk : 0 < P.k)
    {mssp : List D → (D → ℤ) → F → F → Option ℤ} {c f₀ : D → ℤ} (L : D → ℤ) {r : F}
    (hr : r ∈ P.faces) {φ : F → ℤ}
    (hpot : (DDG.union ⟨P.faces, mssp P.darts (c - f₀)⟩
      (explicitArcs (M.dualGraph L) P.darts)).IsPot φ)
    {fr : FRFun F} (hfr : FRSpec fr)
    {b : ℕ} {β : ℕ → F} {idx : F → ℕ} (hX : ∀ i < b, β i ∈ P.faces)
    (hinj : ∀ i < b, ∀ j < b, β i = β j → i = j) (hidx_lt : ∀ y ∈ P.faces, idx y < b)
    (hβidx : ∀ y ∈ P.faces, β (idx y) = y)
    (hsome : ∀ i < b, ∀ j < b, ∃ a,
      (⟨P.faces, mssp P.darts (c - f₀)⟩ : DDG F).len (β i) (β j) = some a)
    {Es : List (ℕ × ℕ × ℤ)}
    (hEsE : Es = (explicitArcs (M.dualGraph L) P.darts).map fun e => (idx e.1, idx e.2.1, e.2.2))
    {L' K : ℕ} {v : ℕ → ℕ} {dd : ℕ → ℤ} {nm : ℕ → ℕ} {Fb Rb : ℕ}
    {Dm : ℕ → ℕ → ℤ} (hDm : ∀ i < b, ∀ j < b,
      Dm i j = ((⟨P.faces, mssp P.darts (c - f₀)⟩ : DDG F).len (β i) (β j)).getD 0)
    {pm : ℕ → ℤ} (hpm : ∀ x < b, pm x = φ (β x))
    (hDc : Monge.Crossing b Dm)
    (hres : FrFix.FResN (mkPrm b b Dm pm (idx r) Es) L' K v dd nm Fb Rb) :
    ∀ y ∈ P.faces,
      (nm (Fb + idx y) = 1 ↔
        fr ⟨P.faces, mssp P.darts (c - f₀)⟩ (explicitArcs (M.dualGraph L) P.darts) r φ y ≠
          none) ∧
      ∀ ℓ, fr ⟨P.faces, mssp P.darts (c - f₀)⟩ (explicitArcs (M.dualGraph L) P.darts) r φ y =
        some ℓ → ℓ = frDec (mkPrm b b Dm pm (idx r) Es) L' (nm (Rb + idx y)) := by
  classical
  subst hEsE
  set H : DDG F := ⟨P.faces, mssp P.darts (c - f₀)⟩ with hH
  set E := explicitArcs (M.dualGraph L) P.darts with hE
  set Es : List (ℕ × ℕ × ℤ) := E.map (fun e => (idx e.1, idx e.2.1, e.2.2)) with hEsD
  have hidx : ∀ y ∈ P.faces, ∃ i < b, β i = y := fun y hy => ⟨idx y, hidx_lt y hy, hβidx y hy⟩
  have hidxβ : ∀ i < b, idx (β i) = i := fun i hi =>
    hinj _ (hidx_lt _ (hX i hi)) _ hi (hβidx _ (hX i hi))
  -- the ends of the explicit arcs are faces along the path
  have hEmem : ∀ e ∈ E, e.1 ∈ P.faces ∧ e.2.1 ∈ P.faces := by
    intro e he
    simp only [hE, explicitArcs, List.mem_map] at he
    obtain ⟨d, hd, rfl⟩ := he
    exact ⟨P.face_mem hd, P.face_mem (P.rev_mem_darts hd)⟩
  have hb : 1 ≤ b := by
    obtain ⟨i, hi, -⟩ := hidx r hr; omega
  -- the input
  have hEs : ∀ a ∈ Es, a.1 < b ∧ a.2.1 < b := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
    exact ⟨hidx_lt _ (hEmem e he).1, hidx_lt _ (hEmem e he).2⟩
  set Pr := mkPrm b b Dm pm (idx r) Es with hPr
  have hL : Lay Pr := mkPrm_lay hb le_rfl (hidx_lt r hr) fun a ha => (hEs a ha).2
  have hN : 0 < Pr.N := hb
  have hfvv : ∀ {i : ℕ}, i < b → ((fv Pr hN i : Fin Pr.N) : ℕ) = i := fun hi => fv_val hi
  have hlenEx : (exArcs Pr hL.N_pos).length = (arcList b Es).length :=
    length_exArcs_mkPrm hL.N_pos
  have hgetEx : ∀ t (ht : t < (exArcs Pr hL.N_pos).length), (exArcs Pr hL.N_pos)[t] =
      (fv Pr hL.N_pos ((arcList b Es)[t]'(by rw [← hlenEx]; exact ht)).1,
        fv Pr hL.N_pos ((arcList b Es)[t]'(by rw [← hlenEx]; exact ht)).2.1,
        ((arcList b Es)[t]'(by rw [← hlenEx]; exact ht)).2.2) := fun t ht =>
    exArcs_mkPrm_get hL.N_pos ht
  -- arcs of the machine's input
  have hm_pos : 0 < (arcList b Es).length := by
    obtain ⟨d, hd⟩ : ∃ d, d ∈ P.darts := ⟨P.d 0, P.d_mem 0 hk⟩
    have he : (M.face d, M.face (M.rev d), L d) ∈ E := by
      simp only [hE, explicitArcs, List.mem_map]; exact ⟨d, hd, rfl⟩
    have ha : (idx (M.face d), idx (M.face (M.rev d)), L d) ∈ Es :=
      List.mem_map.2 ⟨_, he, rfl⟩
    exact List.length_pos_of_mem (mem_arcList.2 ⟨ha, (hEs _ ha).1⟩)
  have hA : Nonempty (Monge.Arc Pr.b ⊕ Fin (exArcs Pr hL.N_pos).length) :=
    ⟨.inr ⟨0, by rw [hlenEx]; exact hm_pos⟩⟩
  -- the corner of a machine vertex
  let ι : Fin Pr.N → F := fun x => β x.1
  have hι : Function.Injective ι := fun x y h =>
    Fin.ext (hinj x.1 x.2 y.1 y.2 h)
  -- the dense distance graph of the machine
  have hfd_len : ∀ i < b, ∀ j < b, i ≠ j →
      (faceDDG (fv Pr hL.N_pos) Pr.b Pr.D).len (fv Pr hL.N_pos i) (fv Pr hL.N_pos j) =
        some (Dm i j) := by
    intro i hi j hj hij
    have hex : ∃ q : Monge.Arc Pr.b, fv Pr hL.N_pos q.1.1 = fv Pr hL.N_pos i ∧
        fv Pr hL.N_pos q.1.2 = fv Pr hL.N_pos j :=
      ⟨⟨(⟨i, hi⟩, ⟨j, hj⟩), fun h => hij (congrArg Fin.val h)⟩, rfl, rfl⟩
    simp only [faceDDG, hex, ↓reduceDIte]
    have h1 := fv_inj (P := Pr) (hN := hL.N_pos) hex.choose.1.1.2 hi hex.choose_spec.1
    have h2 := fv_inj (P := Pr) (hN := hL.N_pos) hex.choose.1.2.2 hj hex.choose_spec.2
    rw [h1, h2]; rfl
  have hfd_arc : ∀ q : (faceDDG (fv Pr hL.N_pos) Pr.b Pr.D).Arc, ∃ i < b, ∃ j < b, i ≠ j ∧
      q.1.1 = fv Pr hL.N_pos i ∧ q.1.2 = fv Pr hL.N_pos j := by
    rintro ⟨⟨x, y⟩, -, -, hsm⟩
    simp only [faceDDG] at hsm
    split_ifs at hsm with hex
    · obtain ⟨q, rfl, rfl⟩ := hex
      exact ⟨q.1.1, q.1.1.2, q.1.2, q.1.2.2, fun h => q.2 (Fin.ext h), rfl, rfl⟩
    · simp at hsm
  set Gm := (faceDDG (fv Pr hL.N_pos) Pr.b Pr.D).union (exArcs Pr hL.N_pos)
  set GF := H.union E
  -- explicit arcs correspond
  have hex_m : ∀ t : Fin (exArcs Pr hL.N_pos).length, ∃ j : Fin E.length,
      ι (Gm.src (.inr t)) = GF.src (.inr j) ∧ ι (Gm.dst (.inr t)) = GF.dst (.inr j) ∧
        Gm.len (.inr t) = GF.len (.inr j) := by
    intro t
    have ht : t.1 < (arcList b Es).length := lt_of_lt_of_eq t.2 hlenEx
    have hget := hgetEx t.1 t.2
    have ha : (arcList b Es)[t.1] ∈ Es := (mem_arcList.1 (List.getElem_mem ht)).1
    obtain ⟨e, he, he'⟩ := List.mem_map.1 ha
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 he
    refine ⟨⟨j, hj⟩, ?_, ?_, ?_⟩
    · show β ((exArcs Pr hL.N_pos)[t.1]).1.1 = E[j].1
      rw [hget, hfvv (by rw [← he']; exact hidx_lt _ (hEmem _ he).1), ← he']
      exact hβidx _ (hEmem _ he).1
    · show β ((exArcs Pr hL.N_pos)[t.1]).2.1.1 = E[j].2.1
      rw [hget, hfvv (by rw [← he']; exact hidx_lt _ (hEmem _ he).2), ← he']
      exact hβidx _ (hEmem _ he).2
    · show ((exArcs Pr hL.N_pos)[t.1]).2.2 = E[j].2.2
      rw [hget, ← he']
  have hex_F : ∀ j : Fin E.length, ∃ t : Fin (exArcs Pr hL.N_pos).length,
      ι (Gm.src (.inr t)) = GF.src (.inr j) ∧ ι (Gm.dst (.inr t)) = GF.dst (.inr j) ∧
        Gm.len (.inr t) = GF.len (.inr j) := by
    intro j
    have hmemE : E[j.1] ∈ E := List.getElem_mem j.2
    have ha : (idx E[j.1].1, idx E[j.1].2.1, E[j.1].2.2) ∈ arcList b Es :=
      mem_arcList.2 ⟨List.mem_map.2 ⟨_, hmemE, rfl⟩, hidx_lt _ (hEmem _ hmemE).1⟩
    obtain ⟨t, ht, hta⟩ := List.mem_iff_getElem.1 ha
    have ht' : t < (exArcs Pr hL.N_pos).length := by rw [hlenEx]; exact ht
    have hget := hgetEx t ht'
    refine ⟨⟨t, ht'⟩, ?_, ?_, ?_⟩
    · show β ((exArcs Pr hL.N_pos)[t]).1.1 = E[j.1].1
      rw [hget]; simp only [hta]
      rw [hfvv (hidx_lt _ (hEmem _ hmemE).1)]; exact hβidx _ (hEmem _ hmemE).1
    · show β ((exArcs Pr hL.N_pos)[t]).2.1.1 = E[j.1].2.1
      rw [hget]; simp only [hta]
      rw [hfvv (hidx_lt _ (hEmem _ hmemE).2)]; exact hβidx _ (hEmem _ hmemE).2
    · show ((exArcs Pr hL.N_pos)[t]).2.2 = E[j.1].2.2
      rw [hget]; simp only [hta]
  -- the transfer
  have htr : Transfer Gm GF ι := by
    refine ⟨hι, ?_, ?_⟩
    · rintro (q | t)
      · obtain ⟨i, hi, j, hj, hij, h1, h2⟩ := hfd_arc q
        obtain ⟨a, ha⟩ := hsome i hi j hj
        have hq : (H.len (β i) (β j)).isSome := by rw [ha]; rfl
        refine ⟨.inl ⟨(β i, β j), hX i hi, hX j hj, hq⟩, ?_, ?_, ?_⟩
        · show β i = β (q.1.1 : ℕ); rw [h1, hfvv hi]
        · show β j = β (q.1.2 : ℕ); rw [h2, hfvv hj]
        · show (H.len (β i) (β j)).getD 0 =
            ((faceDDG (fv Pr hL.N_pos) Pr.b Pr.D).len q.1.1 q.1.2).getD 0
          rw [h1, h2, hfd_len i hi j hj hij, Option.getD_some, hDm i hi j hj]
      · obtain ⟨j, h1, h2, h3⟩ := hex_m t
        exact ⟨.inr j, h1.symm, h2.symm, h3.symm⟩
    · rintro (q | j) x hx
      · obtain ⟨⟨u, v⟩, hu, hv, hsm⟩ := q
        change u = β x.1 at hx
        by_cases huv : u = v
        · right
          subst huv
          refine ⟨rfl, ?_⟩
          have := hpot (.inl ⟨(u, u), hu, hv, hsm⟩)
          change φ u ≤ φ u + (H.len u u).getD 0 at this
          change 0 ≤ (H.len u u).getD 0
          omega
        · left
          obtain ⟨j, hj, rfl⟩ := hidx v hv
          have hxu : x.1 < b := x.2
          have hne : x.1 ≠ j := fun h => huv (by rw [hx, h])
          refine ⟨.inl ⟨(fv Pr hL.N_pos x.1, fv Pr hL.N_pos j), ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
          · exact mem_image.2 ⟨x.1, mem_range.2 hxu, rfl⟩
          · exact mem_image.2 ⟨j, mem_range.2 hj, rfl⟩
          · rw [hfd_len x.1 hxu j hj hne]; rfl
          · show fv Pr hL.N_pos x.1 = x; exact Fin.ext (hfvv hxu)
          · show β (fv Pr hL.N_pos j : ℕ) = β j; rw [hfvv hj]
          · show ((faceDDG (fv Pr hL.N_pos) Pr.b Pr.D).len (fv Pr hL.N_pos x.1)
              (fv Pr hL.N_pos j)).getD 0 = (H.len u (β j)).getD 0
            rw [hfd_len x.1 hxu j hj hne, hx, Option.getD_some, hDm x.1 hxu j hj]
      · left
        obtain ⟨t, h1, h2, h3⟩ := hex_F j
        refine ⟨.inr t, hι (h1.trans hx), h2, h3⟩
  -- the potential of the machine's input
  have hp : Gm.IsPot (fun y => Pr.p y) := by
    rintro (q | t)
    · obtain ⟨i, hi, j, hj, hij, h1, h2⟩ := hfd_arc q
      obtain ⟨a, ha⟩ := hsome i hi j hj
      have hq : (H.len (β i) (β j)).isSome := by rw [ha]; rfl
      have := hpot (.inl ⟨(β i, β j), hX i hi, hX j hj, hq⟩)
      show pm (q.1.2 : ℕ) ≤ pm (q.1.1 : ℕ) +
        ((faceDDG (fv Pr hL.N_pos) Pr.b Pr.D).len q.1.1 q.1.2).getD 0
      rw [h1, h2, hfd_len i hi j hj hij, hfvv hi, hfvv hj, Option.getD_some, hpm i hi, hpm j hj,
        hDm i hi j hj]
      exact this
    · obtain ⟨j, h1, h2, h3⟩ := hex_m t
      have := hpot (.inr j)
      show Pr.p (Gm.dst (.inr t)) ≤ Pr.p (Gm.src (.inr t)) + Gm.len (.inr t)
      rw [show Pr.p (Gm.dst (.inr t)) = φ (ι (Gm.dst (.inr t))) from hpm _ (Gm.dst (.inr t)).2,
        show Pr.p (Gm.src (.inr t)) = φ (ι (Gm.src (.inr t))) from hpm _ (Gm.src (.inr t)).2,
        h1, h2, h3]
      exact this
  -- the run's result
  obtain ⟨δ, hδ, hmem⟩ := FResN.isDist hL mkPrm_off_zero hA hp hres
  have hroot : ι (fv Pr hL.N_pos Pr.r) = r := by
    show β (fv Pr hL.N_pos (idx r) : ℕ) = r
    rw [hfvv (hidx_lt r hr)]; exact hβidx r hr
  have hδF := isDist_transfer htr hδ
  rw [hroot] at hδF
  have heq := (hfr H E r φ hpot).unique hδF
  intro y hy
  have hy' : ι ⟨idx y, hidx_lt y hy⟩ = y := hβidx y hy
  have key : fr H E r φ y = δ ⟨idx y, hidx_lt y hy⟩ := by
    rw [heq]
    calc htr.pull δ y = htr.pull δ (ι ⟨idx y, hidx_lt y hy⟩) := by rw [hy']
      _ = _ := htr.pull_iota δ _
  rw [key]
  exact hmem ⟨idx y, hidx_lt y hy⟩

end BKMNW

end PlanarFlow
