module

public import PlanarFlow.BKMNW.MachCost
public import PlanarFlow.BKMNW.FixMonge
public import PlanarFlow.BKMNW.DistTransfer
public import PlanarFlow.Monge.FRLayout

/-!
# The calls of FR-Dijkstra in FixConservationOnPath, on the machine

Every stage of FixConservationOnPath (`PlanarFlow.BKMNW.fpStep`) calls FR-Dijkstra on the dense
distance graph `⟨P.faces, mssp P.darts (c - f₀)⟩` of the faces along the path `P` and the explicit
arcs of the dual darts of `P`, from a face of `P`, with a feasible price function. The cost models
charge each call `fr x (2k)` as `fixPath` runs it (`SubCosts.fixRun`, `x` the faces along the
path, `k` its darts) and `fr (2k) (2k)` in the recurrence of the article (`SubCosts.fix`). This
file proves that **every such call is realized by a run of the machine program
`PlanarFlow.Monge.FR.frProg` within `cMach.fr x (2k)` steps** (`cMach_fr_exec_fixPath_faces`;
`cMach_fr_exec_fixPath`: within `cMach.fr (2k) (2k)`), the distances being left in memory:

* the corners are the faces along the path at their first positions around it, in increasing
  order (`exists_fixCornersInj`); the crossing inequality between them is `crossing_fixPath`;
* the input is laid out by `PlanarFlow.Monge.FR.mkPrm` (vertices `0, …, b - 1`, the corners, and
  the explicit arcs tail by tail);
* the distances of the machine's graph are those of the call, read along the corners
  (`isDist_transfer`): the loops of the dense distance graph of the call have nonnegative length
  under the feasible price function, and the call's graph has no other vertices.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine Monge.FR

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-! ### The corners: each face along the path once -/

/-- **The faces along the path, each once**, at their first positions around it, in increasing
order. -/
theorem exists_fixCornersInj (hrot : M.RotTrans) (P : SPath M) :
    ∃ (b : ℕ) (s : ℕ → ℕ), (∀ i j, i < j → j < b → s i < s j) ∧ (∀ i < b, s i < fixPer M P) ∧
      (∀ i < b, fixCorner M P (s i) ∈ P.faces) ∧
      (∀ i < b, ∀ j < b, fixCorner M P (s i) = fixCorner M P (s j) → i = j) ∧
      ∀ x ∈ P.faces, ∃ i < b, fixCorner M P (s i) = x := by
  classical
  obtain ⟨b₀, s₀, -, hs₀, -, hcov₀⟩ := exists_fixCorners hrot P
  let S : Finset ℕ := (range (fixPer M P)).filter fun i =>
    fixCorner M P i ∈ P.faces ∧ ∀ j < i, fixCorner M P j ≠ fixCorner M P i
  let s : ℕ → ℕ := fun i => if h : i < S.card then S.orderEmbOfFin rfl ⟨i, h⟩ else 0
  have hmem : ∀ i (h : i < S.card), s i ∈ S := fun i h => by
    simp only [s, h, ↓reduceDIte]; exact S.orderEmbOfFin_mem rfl _
  have hmono : ∀ i j, i < j → j < S.card → s i < s j := fun i j hij hj => by
    simp only [s, hj, show i < S.card by omega, ↓reduceDIte]
    exact (S.orderEmbOfFin rfl).strictMono (show (⟨i, by omega⟩ : Fin S.card) < ⟨j, hj⟩ from hij)
  refine ⟨S.card, s, hmono, fun i hi => mem_range.1 (mem_filter.1 (hmem i hi)).1,
    fun i hi => (mem_filter.1 (hmem i hi)).2.1, fun i hi j hj he => ?_, fun x hx => ?_⟩
  · by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact (mem_filter.1 (hmem j hj)).2.2 (s i) (hmono i j h hj) he
    · exact (mem_filter.1 (hmem i hi)).2.2 (s j) (hmono j i h hi) he.symm
  · obtain ⟨i₀, hi₀, hx₀⟩ := hcov₀ x hx
    have hex : ∃ n, fixCorner M P n = x := ⟨_, hx₀⟩
    set n := Nat.find hex
    have hn : fixCorner M P n = x := Nat.find_spec hex
    have hnle : n ≤ s₀ i₀ := Nat.find_min' hex hx₀
    have hnS : n ∈ S := mem_filter.2 ⟨mem_range.2 (lt_of_le_of_lt hnle (hs₀ i₀ hi₀)),
      by rw [hn]; exact hx, fun j hj h => Nat.find_min hex hj (h.trans hn)⟩
    have hrange := S.range_orderEmbOfFin rfl
    have : n ∈ Set.range (S.orderEmbOfFin rfl) := by rw [hrange]; exact hnS
    obtain ⟨⟨i, hi⟩, hi'⟩ := this
    refine ⟨i, hi, ?_⟩
    simp only [s, hi, ↓reduceDIte, hi', hn]

/-! ### The realization -/

open Classical in
/-- **Every call of FR-Dijkstra in FixConservationOnPath is realized by a run of `frProg`
within `cMach.fr x (2k)` steps** (`x` the faces along the path and `k` its darts), the size at which
`SubCosts.fixRun` charges it (`cMach_fr_exec_fixPath`: within `cMach.fr (2k) (2k)`, the charge of
`SubCosts.fix`). The call is on the dense distance graph `⟨P.faces, mssp P.darts (c - f₀)⟩` and the
explicit arcs of the darts of `P` (with any lengths `L`), from a face `r` of `P`, with a feasible
price function `φ`; `fr` is any implementation meeting `FRSpec`. The run leaves, for each face `y`
along the path (numbered `idx y`), the flag `1` iff `y` is reachable and its distance. -/
theorem cMach_fr_exec_fixPath_faces (C C₀ : ℕ) (hM : M.IsPlane) (hrot : M.RotTrans) (P : SPath M)
    (hk : 0 < P.k) {mssp : List D → (D → ℤ) → F → F → Option ℤ} (hmssp : MSSPSpecAt M mssp P)
    {c f₀ : D → ℤ} (hf₀ : IsPseudo M c f₀) (L : D → ℤ) {r : F} (hr : r ∈ P.faces)
    {φ : F → ℤ}
    (hpot : (DDG.union ⟨P.faces, mssp P.darts (c - f₀)⟩
      (explicitArcs (M.dualGraph L) P.darts)).IsPot φ)
    {fr : FRFun F} (hfr : FRSpec fr) (I : Input) :
    ∃ (Pr : Prm) (c₀ c' : Config) (steps : ℕ) (idx : F → ℕ),
      Exec I Pr.W frProg c₀ c' steps ∧ steps ≤ (cMach C C₀).fr P.faces.card (2 * P.k) ∧
      c'.output = c₀.output ∧
      ∀ y ∈ P.faces, idx y < Pr.N ∧
        (c'.nmem (Pr.sb + idx y) = 1 ↔
          fr ⟨P.faces, mssp P.darts (c - f₀)⟩ (explicitArcs (M.dualGraph L) P.darts) r φ y ≠
            none) ∧
        ∀ ℓ, fr ⟨P.faces, mssp P.darts (c - f₀)⟩ (explicitArcs (M.dualGraph L) P.darts) r φ y =
          some ℓ → c'.rmem (Pr.db + idx y) = ℓ := by
  set H : DDG F := ⟨P.faces, mssp P.darts (c - f₀)⟩ with hH
  set E := explicitArcs (M.dualGraph L) P.darts with hE
  obtain ⟨b, s, hs, hsk, hX, hinj, hcov⟩ := exists_fixCornersInj hrot P
  set β : ℕ → F := fun i => fixCorner M P (s i) with hβ
  -- the number of a face along the path
  have hidx : ∀ y ∈ P.faces, ∃ i < b, β i = y := hcov
  let idx : F → ℕ := fun y => if h : y ∈ P.faces then (hidx y h).choose else 0
  have hidx_lt : ∀ y ∈ P.faces, idx y < b := fun y hy => by
    simp only [idx, hy, ↓reduceDIte]; exact (hidx y hy).choose_spec.1
  have hβidx : ∀ y ∈ P.faces, β (idx y) = y := fun y hy => by
    simp only [idx, hy, ↓reduceDIte]; exact (hidx y hy).choose_spec.2
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
  let Dm : ℕ → ℕ → ℤ := fun i j => (H.len (β i) (β j)).getD 0
  let pm : ℕ → ℤ := fun x => φ (β x)
  let Es : List (ℕ × ℕ × ℤ) := E.map fun e => (idx e.1, idx e.2.1, e.2.2)
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
  -- the lengths are finite between the corners
  have hnn : ∀ e, e ∉ P.darts → 0 ≤ (c - f₀) e := fun e _ => by
    simp only [Pi.sub_apply]; linarith [hf₀.le_cap e]
  have hsome : ∀ i < b, ∀ j, ∃ a, H.len (β i) (β j) = some a := fun i hi j =>
    fixDDG_some P hmssp hnn (hX i hi) (s j)
  -- the crossing inequality
  have hDc : Monge.Crossing Pr.b Pr.D := crossing_fixPath hM hrot P hmssp hf₀ hs hsk hX
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
        obtain ⟨a, ha⟩ := hsome i hi j
        have hq : (H.len (β i) (β j)).isSome := by rw [ha]; rfl
        refine ⟨.inl ⟨(β i, β j), hX i hi, hX j hj, hq⟩, ?_, ?_, ?_⟩
        · show β i = β (q.1.1 : ℕ); rw [h1, hfvv hi]
        · show β j = β (q.1.2 : ℕ); rw [h2, hfvv hj]
        · show (H.len (β i) (β j)).getD 0 =
            ((faceDDG (fv Pr hL.N_pos) Pr.b Pr.D).len q.1.1 q.1.2).getD 0
          rw [h1, h2, hfd_len i hi j hj hij]; rfl
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
            rw [hfd_len x.1 hxu j hj hne, hx]; rfl
      · left
        obtain ⟨t, h1, h2, h3⟩ := hex_F j
        refine ⟨.inr t, hι (h1.trans hx), h2, h3⟩
  -- the potential of the machine's input
  have hp : Gm.IsPot (fun y => Pr.p y) := by
    rintro (q | t)
    · obtain ⟨i, hi, j, hj, hij, h1, h2⟩ := hfd_arc q
      obtain ⟨a, ha⟩ := hsome i hi j
      have hq : (H.len (β i) (β j)).isSome := by rw [ha]; rfl
      have := hpot (.inl ⟨(β i, β j), hX i hi, hX j hj, hq⟩)
      show pm (q.1.2 : ℕ) ≤ pm (q.1.1 : ℕ) +
        ((faceDDG (fv Pr hL.N_pos) Pr.b Pr.D).len q.1.1 q.1.2).getD 0
      rw [h1, h2, hfd_len i hi j hj hij, hfvv hi, hfvv hj]
      exact this
    · obtain ⟨j, h1, h2, h3⟩ := hex_m t
      have := hpot (.inr j)
      show φ (ι (Gm.dst (.inr t))) ≤ φ (ι (Gm.src (.inr t))) + Gm.len (.inr t)
      rw [h1, h2, h3]; exact this
  -- the run
  obtain ⟨c₀, hw, hin, hDa⟩ := NegSSSP.exists_frConfig hL
  obtain ⟨c', steps, he, hsteps, -, hout, δ, hδ, hmem⟩ :=
    cMach_fr_exec (I := I) C C₀ hL mkPrm_off_zero hDc hA hp c₀ hw hin hDa
  have hroot : ι (fv Pr hL.N_pos Pr.r) = r := by
    show β (fv Pr hL.N_pos (idx r) : ℕ) = r
    rw [hfvv (hidx_lt r hr)]; exact hβidx r hr
  have hδF := isDist_transfer htr hδ
  rw [hroot] at hδF
  have heq := (hfr H E r φ hpot).unique hδF
  refine ⟨Pr, c₀, c', steps, idx, he, ?_, hout, fun y hy => ⟨hidx_lt y hy, ?_, ?_⟩⟩
  · refine hsteps.trans ?_
    have h1 : b ≤ P.faces.card := by
      have : (range b).image β ⊆ P.faces := fun x hx => by
        obtain ⟨i, hi, rfl⟩ := mem_image.1 hx; exact hX i (mem_range.1 hi)
      have h2 := card_le_card this
      rwa [card_image_of_injOn (fun i hi j hj h => hinj i (mem_range.1 hi) j (mem_range.1 hj) h),
        card_range] at h2
    have hmk : Pr.m ≤ 2 * P.k := by
      show (arcList b Es).length ≤ 2 * P.k
      have := length_pre_le Es b
      simp only [Es, List.length_map, hE, explicitArcs, P.length_darts] at this
      exact this
    show 6300 * (b * lg b ^ 2 + Pr.m * lg b) ≤
      6300 * (P.faces.card * lg P.faces.card ^ 2 + 2 * P.k * lg P.faces.card)
    have hl := lg_mono h1
    gcongr
  · have hy' : ι ⟨idx y, hidx_lt y hy⟩ = y := hβidx y hy
    have key : fr H E r φ y = δ ⟨idx y, hidx_lt y hy⟩ := by
      rw [heq]
      calc htr.pull δ y = htr.pull δ (ι ⟨idx y, hidx_lt y hy⟩) := by rw [hy']
        _ = _ := htr.pull_iota δ _
    rw [key]; exact (hmem ⟨idx y, hidx_lt y hy⟩).1
  · intro ℓ hℓ
    have hy' : ι ⟨idx y, hidx_lt y hy⟩ = y := hβidx y hy
    have key : fr H E r φ y = δ ⟨idx y, hidx_lt y hy⟩ := by
      rw [heq]
      calc htr.pull δ y = htr.pull δ (ι ⟨idx y, hidx_lt y hy⟩) := by rw [hy']
        _ = _ := htr.pull_iota δ _
    rw [key] at hℓ
    exact (hmem ⟨idx y, hidx_lt y hy⟩).2 ℓ hℓ

open Classical in
/-- **Every call of FR-Dijkstra in FixConservationOnPath is realized by a run of `frProg`
within `cMach.fr (2k) (2k)` steps**, the size at which `SubCosts.fix` charges it: the faces along
the path are at most its `2k` darts (`cMach_fr_exec_fixPath_faces`). -/
theorem cMach_fr_exec_fixPath (C C₀ : ℕ) (hM : M.IsPlane) (hrot : M.RotTrans) (P : SPath M)
    (hk : 0 < P.k) {mssp : List D → (D → ℤ) → F → F → Option ℤ} (hmssp : MSSPSpecAt M mssp P)
    {c f₀ : D → ℤ} (hf₀ : IsPseudo M c f₀) (L : D → ℤ) {r : F} (hr : r ∈ P.faces)
    {φ : F → ℤ}
    (hpot : (DDG.union ⟨P.faces, mssp P.darts (c - f₀)⟩
      (explicitArcs (M.dualGraph L) P.darts)).IsPot φ)
    {fr : FRFun F} (hfr : FRSpec fr) (I : Input) :
    ∃ (Pr : Prm) (c₀ c' : Config) (steps : ℕ) (idx : F → ℕ),
      Exec I Pr.W frProg c₀ c' steps ∧ steps ≤ (cMach C C₀).fr (2 * P.k) (2 * P.k) ∧
      c'.output = c₀.output ∧
      ∀ y ∈ P.faces, idx y < Pr.N ∧
        (c'.nmem (Pr.sb + idx y) = 1 ↔
          fr ⟨P.faces, mssp P.darts (c - f₀)⟩ (explicitArcs (M.dualGraph L) P.darts) r φ y ≠
            none) ∧
        ∀ ℓ, fr ⟨P.faces, mssp P.darts (c - f₀)⟩ (explicitArcs (M.dualGraph L) P.darts) r φ y =
          some ℓ → c'.rmem (Pr.db + idx y) = ℓ := by
  obtain ⟨Pr, c₀, c', steps, idx, he, hs, hout, h⟩ :=
    cMach_fr_exec_fixPath_faces C C₀ hM hrot P hk hmssp hf₀ L hr hpot hfr I
  refine ⟨Pr, c₀, c', steps, idx, he, hs.trans ?_, hout, h⟩
  have h3 : P.faces.card ≤ 2 * P.k := by
    have : P.faces.card ≤ P.darts.length := by
      unfold SPath.faces
      exact (List.toFinset_card_le _).trans (by simp)
    rwa [P.length_darts] at this
  show 6300 * (P.faces.card * lg P.faces.card ^ 2 + 2 * P.k * lg P.faces.card) ≤
    6300 * (2 * P.k * lg (2 * P.k) ^ 2 + 2 * P.k * lg (2 * P.k))
  have hl := lg_mono h3
  gcongr

end BKMNW

end PlanarFlow
