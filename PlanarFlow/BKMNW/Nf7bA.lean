module

public import PlanarFlow.BKMNW.NfImU
public import PlanarFlow.BKMNW.NfArcs

/-!
# The stage loop of `fixP`, part A: the semantic glue of the FR run of a stage

* **`fr_corners_feas`** (the transfer part of `fr_corners_eq`): the prices of a stage are feasible
  for the machine input `mkPrm b b Dm pm (idx r) Es` (`Feas`, a hypothesis of `frRun_exec`);
  **`SW.feas`**: the same for the stage's `MsCall.frPrm … (2k)` (the image of the stage);
* **`frPrm_xb`**: `FrImgB` gives the bounds `XB` of FR-Dijkstra;
* **`frCfgN_frPrm_upd`**: two FR inputs `frPrm` with the same corners, matrix, arcs (tails and
  heads) have the same image memory except at the residues of the prices
  `[β + b², β + b² + b)` and of the sorted lengths `[β + lb, β + lb + mE)` (`β = W + 1`), whose
  values are given (`imU` writes exactly these cells).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap SPath WordRAM WordRAM.Machine Monge.FR

/-! ### Feasibility of the stage's input -/

section Feas

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The prices are feasible for the machine input** (the transfer part of `fr_corners_eq`). -/
theorem fr_corners_feas (P : SPath M)
    {mssp : List D → (D → ℤ) → F → F → Option ℤ} {c f₀ : D → ℤ} (L : D → ℤ) {r : F}
    (hr : r ∈ P.faces) {φ : F → ℤ}
    (hpot : (DDG.union ⟨P.faces, mssp P.darts (c - f₀)⟩
      (explicitArcs (M.dualGraph L) P.darts)).IsPot φ)
    {b : ℕ} {β : ℕ → F} {idx : F → ℕ} (hX : ∀ i < b, β i ∈ P.faces)
    (hinj : ∀ i < b, ∀ j < b, β i = β j → i = j) (hidx_lt : ∀ y ∈ P.faces, idx y < b)
    (hβidx : ∀ y ∈ P.faces, β (idx y) = y)
    (hsome : ∀ i < b, ∀ j < b, ∃ a,
      (⟨P.faces, mssp P.darts (c - f₀)⟩ : DDG F).len (β i) (β j) = some a)
    {Es : List (ℕ × ℕ × ℤ)}
    (hEsE : Es = (explicitArcs (M.dualGraph L) P.darts).map fun e => (idx e.1, idx e.2.1, e.2.2))
    {Dm : ℕ → ℕ → ℤ} (hDm : ∀ i < b, ∀ j < b,
      Dm i j = ((⟨P.faces, mssp P.darts (c - f₀)⟩ : DDG F).len (β i) (β j)).getD 0)
    {pm : ℕ → ℤ} (hpm : ∀ x < b, pm x = φ (β x)) :
    Monge.FR.Feas (mkPrm b b Dm pm (idx r) Es) := by
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
  exact feas_of_isPot hL ((isPot_ddgPlus_iff (fv_inj_corner hL)).2 hp)

/-- **The prices of a stage are feasible for the stage's FR image input.** -/
theorem SW.feas (w : SW) {c f₀ : D → ℤ} (hc : ∀ e, 0 ≤ c e) (hf₀ : IsPseudo M c f₀) {P : SPath M}
    {mssp : List D → (D → ℤ) → F → F → Option ℤ} (hmssp : MSSPSpecAt M mssp P) {b : ℕ}
    {β : ℕ → F} {idx : F → ℕ}
    (hw : w.OK P c f₀ b β idx) {s : (D → ℤ) × (F → ℤ)} (hs : SRep P f₀ b β s w.Fw w.Pw)
    (hinv : EffInv c f₀ P w.i s) (hsk : ¬ w.skip)
    (hinj : ∀ i < b, ∀ j < b, β i = β j → i = j)
    (hsome : ∀ i < b, ∀ j < b, ∃ a,
      (⟨P.faces, mssp P.darts (c - f₀)⟩ : DDG F).len (β i) (β j) = some a)
    {Dm : ℕ → ℕ → ℕ} (hDm : ∀ i < b, ∀ j < b,
      (Dm i j : ℤ) = ((⟨P.faces, mssp P.darts (c - f₀)⟩ : DDG F).len (β i) (β j)).getD 0)
    {pm : ℕ → ℤ} (hpm : ∀ x < b, pm x = s.2 (β x)) :
    Feas (MsCall.frPrm b Dm pm w.root
      (fun a => idx (M.face (dartAt P a))) (fun a => idx (M.face (M.rev (dartAt P a))))
      (fun a => w.lenD P c s.1 s.2 (dartAt P a)) (2 * P.k)) := by
  have hi := hw.hi
  have hd := P.d_mem w.i hi
  have hroot : β w.root ∈ P.faces := by
    unfold SW.root; split_ifs
    · rw [hw.ib, hw.β_idx _ (P.face_mem (P.rev_mem_darts hd))]
      exact P.face_mem (P.rev_mem_darts hd)
    · rw [hw.ia, hw.β_idx _ (P.face_mem hd)]; exact P.face_mem hd
  have hridx : idx (β w.root) = w.root := by
    have hr : w.root < b := by
      unfold SW.root; split_ifs
      · rw [hw.ib]; exact hw.idx_lt _ (P.face_mem (P.rev_mem_darts hd))
      · rw [hw.ia]; exact hw.idx_lt _ (P.face_mem hd)
    exact hinj _ (hw.idx_lt _ hroot) _ hr (hw.β_idx _ hroot)
  have hpot := w.isPot hc hf₀ hmssp hw hs hinv hsk
  have key := fr_corners_feas P (w.lenD P c s.1 s.2) hroot hpot hw.β_mem hinj hw.idx_lt
    hw.β_idx hsome rfl (Dm := fun i j => (Dm i j : ℤ)) hDm hpm
  rw [hridx, ← csList_stage] at key
  exact key

end Feas

/-! ### The bounds and the image of a stage -/

namespace MsCall

open NegSSSP FrFix

variable {b : ℕ} {Dm : ℕ → ℕ → ℕ} {pm pm' : ℕ → ℤ} {r r' mE : ℕ} {ET EH : ℕ → ℕ}
  {Lz Lz' : ℕ → ℤ} {L : ℕ}

/-- **`FrImgB` gives the bounds of FR-Dijkstra.** -/
theorem frPrm_xb (hb : FrImgB b Dm pm r mE ET EH Lz L) : XB (frPrm b Dm pm r ET EH Lz mE) L := by
  refine ⟨fun i j hi hj => ?_, fun y hy => hb.pm y hy, fun e he => ?_⟩
  · show |((Dm i j : ℕ) : ℤ)| ≤ L
    rw [abs_of_nonneg (by positivity)]; exact_mod_cast hb.dm i hi j hj
  · show |((arcList b (csList ET EH (fun _ => 1) Lz mE)).getD e (0, 0, 0)).2.2| ≤ L
    have he' : e < (arcList b (csList ET EH (fun _ => 1) Lz mE)).length := he
    rw [List.getD_eq_getElem _ _ he']
    have hm := (mem_arcList.1 (List.getElem_mem he')).1
    generalize (arcList b (csList ET EH (fun _ => 1) Lz mE))[e] = q at hm ⊢
    rw [csList_ones, List.mem_map] at hm
    obtain ⟨a, ha, h⟩ := hm
    rw [← h]
    exact hb.lz a (List.mem_range.1 ha)

/-- The sorted arc at the position `e` of the image. -/
noncomputable def sIdx (ET : ℕ → ℕ) (mE b e : ℕ) : ℕ := ((pre (fiL ET mE) b).getD e (0, 0, 0)).2.1

/-- The natural cells of two stage inputs agree. -/
theorem frNM_frPrm_eq (h : ∀ a < mE, ET a < b) (a : ℕ) :
    FrFix.frNM (frPrm b Dm pm' r' ET EH Lz' mE) a = FrFix.frNM (frPrm b Dm pm r ET EH Lz mE) a := by
  by_cases h1 : a < b * b + b
  · rw [frNM_lo h h1, frNM_lo h h1]
  by_cases h2 : a ≤ b * b + b + b
  · obtain ⟨x, rfl⟩ : ∃ x, a = b * b + b + x := ⟨a - (b * b + b), by omega⟩
    rw [frNM_off h (by omega), frNM_off h (by omega)]
  by_cases h3 : a < b * b + b + b + 1 + mE
  · obtain ⟨e, rfl⟩ : ∃ e, a = b * b + b + b + 1 + e := ⟨a - (b * b + b + b + 1), by omega⟩
    rw [frNM_dst h (by omega), frNM_dst h (by omega)]
  · rw [frNM_hi h (by omega), frNM_hi h (by omega)]

/-- **The image of the next stage**: the same memory except the residues of the prices and of
the sorted lengths. -/
theorem frCfgN_frPrm_upd (hb : FrImgB b Dm pm r mE ET EH Lz L)
    (hb' : FrImgB b Dm pm' r' mE ET EH Lz' L) (a : ℕ) :
    (frCfgN (frPrm b Dm pm' r' ET EH Lz' mE) L).nmem a =
      if (frPrm b Dm pm r ET EH Lz mE).W + 1 + b * b ≤ a ∧
          a < (frPrm b Dm pm r ET EH Lz mE).W + 1 + b * b + b then
        (pm' (a - ((frPrm b Dm pm r ET EH Lz mE).W + 1 + b * b)) %
          (frM (frPrm b Dm pm r ET EH Lz mE) L : ℤ)).toNat
      else if (frPrm b Dm pm r ET EH Lz mE).W + 1 + (b * b + b + b + 1 + mE) ≤ a ∧
          a < (frPrm b Dm pm r ET EH Lz mE).W + 1 + (b * b + b + b + 1 + mE) + mE then
        (Lz' (sIdx ET mE b (a - ((frPrm b Dm pm r ET EH Lz mE).W + 1 + (b * b + b + b + 1 + mE))))
          % (frM (frPrm b Dm pm r ET EH Lz mE) L : ℤ)).toNat
      else (frCfgN (frPrm b Dm pm r ET EH Lz mE) L).nmem a := by
  have het := hb.et
  rw [frCfgN_nmem (frPrm_lay hb'), frCfgN_nmem (frPrm_lay hb), frPrm_sb het, frPrm_sb het,
    frPrm_W het, frPrm_W het]
  have eM : frM (frPrm b Dm pm' r' ET EH Lz' mE) L = frM (frPrm b Dm pm r ET EH Lz mE) L := rfl
  have hWf : b * b + b + b + 1 + mE + mE + b + b ≤ fW b (b * b + b + b + 1 + mE + mE + b + b) := by
    unfold fW; omega
  have eFM : (frM (frPrm b Dm pm r ET EH Lz mE) L : ℤ) = (frM (frPrm b Dm pm r ET EH Lz mE) L : ℤ) :=
    rfl
  generalize fW b (b * b + b + b + 1 + mE + mE + b + b) = Wf at hWf ⊢
  by_cases h1 : a < b * b + b + b + 1 + mE + mE
  · simp only [h1, ↓reduceIte, show ¬ (Wf + 1 + b * b ≤ a ∧ a < Wf + 1 + b * b + b) by omega,
      show ¬ (Wf + 1 + (b * b + b + b + 1 + mE) ≤ a ∧
        a < Wf + 1 + (b * b + b + b + 1 + mE) + mE) by omega]
    exact frNM_frPrm_eq het a
  simp only [h1, ↓reduceIte]
  by_cases h2 : Wf + 1 ≤ a ∧ a < Wf + 1 + (b * b + b + b + 1 + mE + mE)
  · simp only [h2, and_self, ↓reduceIte]
    obtain ⟨x, rfl⟩ : ∃ x, a = Wf + 1 + x := ⟨a - (Wf + 1), by omega⟩
    rw [show Wf + 1 + x - (Wf + 1) = x by omega]
    by_cases h3 : x < b * b
    · simp only [show ¬ (Wf + 1 + b * b ≤ Wf + 1 + x ∧ Wf + 1 + x < Wf + 1 + b * b + b) by omega,
        show ¬ (Wf + 1 + (b * b + b + b + 1 + mE) ≤ Wf + 1 + x ∧
          Wf + 1 + x < Wf + 1 + (b * b + b + b + 1 + mE) + mE) by omega, ↓reduceIte]
      rw [frRS_D hb' h3, frRS_D hb h3]
    by_cases h4 : x < b * b + b
    · simp only [show (Wf + 1 + b * b ≤ Wf + 1 + x ∧ Wf + 1 + x < Wf + 1 + b * b + b) by omega,
        and_self, ↓reduceIte]
      obtain ⟨y, rfl⟩ : ∃ y, x = b * b + y := ⟨x - b * b, by omega⟩
      rw [frRS_p hb' (by omega), show Wf + 1 + (b * b + y) - (Wf + 1 + b * b) = y by omega]
      rfl
    by_cases h5 : x < b * b + b + b + 1 + mE
    · simp only [show ¬ (Wf + 1 + b * b ≤ Wf + 1 + x ∧ Wf + 1 + x < Wf + 1 + b * b + b) by omega,
        show ¬ (Wf + 1 + (b * b + b + b + 1 + mE) ≤ Wf + 1 + x ∧
          Wf + 1 + x < Wf + 1 + (b * b + b + b + 1 + mE) + mE) by omega, ↓reduceIte]
      rw [frRS_mid hb' (by omega) h5, frRS_mid hb (by omega) h5]
    · simp only [show ¬ (Wf + 1 + b * b ≤ Wf + 1 + x ∧ Wf + 1 + x < Wf + 1 + b * b + b) by omega,
        show (Wf + 1 + (b * b + b + b + 1 + mE) ≤ Wf + 1 + x ∧
          Wf + 1 + x < Wf + 1 + (b * b + b + b + 1 + mE) + mE) by omega, and_self, ↓reduceIte]
      obtain ⟨e, rfl⟩ : ∃ e, x = b * b + b + b + 1 + mE + e :=
        ⟨x - (b * b + b + b + 1 + mE), by omega⟩
      rw [frRS_len hb' (by omega),
        show Wf + 1 + (b * b + b + b + 1 + mE + e) - (Wf + 1 + (b * b + b + b + 1 + mE)) = e by
          omega]
      rfl
  · simp only [h2, ↓reduceIte, show ¬ (Wf + 1 + b * b ≤ a ∧ a < Wf + 1 + b * b + b) by omega,
      show ¬ (Wf + 1 + (b * b + b + b + 1 + mE) ≤ a ∧
        a < Wf + 1 + (b * b + b + b + 1 + mE) + mE) by omega]

end MsCall

end BKMNW

end PlanarFlow
