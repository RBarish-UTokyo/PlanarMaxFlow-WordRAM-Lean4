module

public import PlanarFlow.BKMNW.NfStage
public import PlanarFlow.BKMNW.NfFr
public import PlanarFlow.BKMNW.MsSpec

/-!
# The FR call of a stage on words: the explicit arcs, feasibility, the answers

* `flatMap_pair_eq`, `dartAt`, **`darts_eq`**: `P.darts = [d 0, rev d 0, d 1, …]` as a map over
  `range (2k)`;
* **`SW.lenD_d`**, **`SW.lenD_rev`**: the lengths of the explicit arcs of stage `i` in words;
* **`csList_stage`**: the arcs of the FR image `MsCall.frPrm … ET EH Lz (2k)` with
  `ET a = idx (face (dartAt a))`, `EH a = idx (face (rev (dartAt a)))`, `Lz a = lenD (dartAt a)`
  are the explicit arcs numbered by `idx`;
* `isPot_stage_gen` (from the proof of `dist_correct`), **`SW.pseudo2`** (after the clip and the
  push on `e`, the flow corrected by `Φ` is a pseudoflow for the capacities of stage `i + 1`:
  arithmetic on the words), **`SW.isPot`**: the prices `s.2` are feasible on the union of the dense
  distance graph and the explicit arcs with the lengths `lenD` (the hypothesis of `FRSpec`, of
  `fr_corners_eq` and, through `feas_of_isPot`, of `frCall_exec`);
* **`SW.dw_eq`**: the FR answers `w.dw` of the stage at the corners from the natural result
  `FResN` of `frPrm …` (flag `1` ⇒ `frDec` of the residue word, else `0`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap SPath

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-! ### The darts of the path in order -/

lemma flatMap_pair_eq {X : Type*} (g h : ℕ → X) (k : ℕ) :
    ((List.range k).flatMap fun j => [g j, h j]) =
      (List.range (2 * k)).map (fun a => if a % 2 = 0 then g (a / 2) else h (a / 2)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, ih, show 2 * (k + 1) = 2 * k + 1 + 1 by ring,
      List.range_succ, List.range_succ, List.map_append, List.map_append, List.append_assoc]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append]
    have h1 : 2 * k % 2 = 0 := by omega
    have h2 : 2 * k / 2 = k := by omega
    have h3 : (2 * k + 1) % 2 ≠ 0 := by omega
    have h4 : (2 * k + 1) / 2 = k := by omega
    simp only [h1, h2, h3, h4, ↓reduceIte]

/-- The `a`-th dart of `P.darts`. -/
def dartAt (P : SPath M) (a : ℕ) : D := if a % 2 = 0 then P.d (a / 2) else M.rev (P.d (a / 2))

lemma darts_eq (P : SPath M) : P.darts = (List.range (2 * P.k)).map (dartAt P) :=
  flatMap_pair_eq _ _ _

/-! ### The lengths of the explicit arcs in words -/

namespace SW

variable (w : SW)

lemma lenD_d {P : SPath M} (c g : D → ℤ) (φX : F → ℤ) (hi : w.i < P.k)
    (hcob : M.cob φX (P.d w.i) = w.cob) {l : ℕ} (hl : l < P.k) :
    w.lenD P c g φX (P.d l) =
      if ¬ w.bv < 0 ∧ l = w.i then |w.bv| - w.val0 + w.cob
      else P.cap c (4 * absSum c + 1) (w.i + 1) (P.d l) - (if l = w.i then w.f2 else g (P.d l)) := by
  unfold lenD eD
  rw [setPair_d P g hi hl]
  by_cases h : w.bv < 0
  · have : P.d l ≠ M.rev (P.d w.i) := P.d_ne_rev hl hi
    simp only [h, ↓reduceIte, this, not_true_eq_false, false_and]
  · simp only [h, ↓reduceIte, M.rev_rev, not_false_eq_true, true_and]
    by_cases hli : l = w.i
    · subst hli; simp only [↓reduceIte, hcob]
    · have : P.d l ≠ P.d w.i := fun e => hli (P.d_inj hl hi e)
      simp only [this, hli, ↓reduceIte]

lemma lenD_rev {P : SPath M} (c g : D → ℤ) (φX : F → ℤ) (hg : M.IsAntisymm g) (hi : w.i < P.k)
    (hcob : M.cob φX (P.d w.i) = w.cob) {l : ℕ} (hl : l < P.k) :
    w.lenD P c g φX (M.rev (P.d l)) =
      if w.bv < 0 ∧ l = w.i then |w.bv| - w.val0 - w.cob
      else P.cap c (4 * absSum c + 1) (w.i + 1) (M.rev (P.d l)) +
        (if l = w.i then w.f2 else g (P.d l)) := by
  unfold lenD eD
  have hsp : setPair M g (P.d w.i) w.f2 (M.rev (P.d l)) =
      -(if l = w.i then w.f2 else g (P.d l)) := by
    by_cases hli : l = w.i
    · subst hli; simp only [setPair_rev, ↓reduceIte]
    · have h1 : M.rev (P.d l) ≠ P.d w.i := fun e => P.d_ne_rev hi hl e.symm
      have h2 : M.rev (P.d l) ≠ M.rev (P.d w.i) := fun e =>
        hli (P.d_inj hl hi (M.rev_injective e))
      simp only [setPair_of_ne _ _ h1 h2, hli, ↓reduceIte]; exact hg _
  rw [hsp]
  by_cases h : w.bv < 0
  · simp only [h, ↓reduceIte, true_and]
    by_cases hli : l = w.i
    · subst hli
      simp only [↓reduceIte]; rw [M.cob_antisymm φX (P.d w.i), hcob]; ring
    · have : M.rev (P.d l) ≠ M.rev (P.d w.i) := fun e =>
        hli (P.d_inj hl hi (M.rev_injective e))
      simp only [this, hli, ↓reduceIte]; ring
  · have : M.rev (P.d l) ≠ M.rev (M.rev (P.d w.i)) := by
      rw [M.rev_rev]; exact fun e => P.d_ne_rev hi hl e.symm
    simp only [h, ↓reduceIte, this, false_and]; ring

end SW

/-! ### The arcs of the FR image -/

/-- **The arcs of the FR image of a stage** are the explicit arcs numbered by `idx`. -/
theorem csList_stage (P : SPath M) (L : D → ℤ) (idx : F → ℕ) :
    NegSSSP.csList (fun a => idx (M.face (dartAt P a))) (fun a => idx (M.face (M.rev (dartAt P a))))
        (fun _ => 1) (fun a => L (dartAt P a)) (2 * P.k) =
      (explicitArcs (M.dualGraph L) P.darts).map fun e => (idx e.1, idx e.2.1, e.2.2) := by
  rw [MsCall.csList_ones, explicitArcs, darts_eq, List.map_map, List.map_map]
  rfl

/-! ### Feasibility of the prices -/

/-- **The prices are feasible on the union** (from the proof of `dist_correct`). -/
theorem isPot_stage_gen {c f₀ : D → ℤ} {P : SPath M}
    {mssp : List D → (D → ℤ) → F → F → Option ℤ} (hmssp : MSSPSpecAt M mssp P)
    (hf₀ : IsPseudo M c f₀) {u f : D → ℤ} {Φ φX : F → ℤ}
    (hu : ∀ e, e ∉ P.darts → u e = c e) (hoff : ∀ e, e ∉ P.darts → f e = f₀ e)
    (hφ : ∀ y ∈ P.faces, φX y = Φ y) (hg : IsPseudo M u (f + M.cob Φ)) {e : D}
    (he : e ∈ P.darts) {x : ℤ} (hx : 0 ≤ x) :
    (DDG.union ⟨P.faces, mssp P.darts (c - f₀)⟩
      (explicitArcs (M.dualGraph fun e' =>
          if e' = M.rev e then x + M.cob φX (M.rev e) else u e' - f e') P.darts)).IsPot φX := by
  generalize hL : (fun e' => if e' = M.rev e then x + M.cob φX (M.rev e) else u e' - f e') = L
  have hre : M.rev e ∈ P.darts := P.rev_mem_darts he
  have hLeq : M.dualGraph L = (M.dualGraph (hassinLen M u (f + M.cob Φ) e x)).addPot Φ := by
    rw [← hL]
    simp only [CombMap.dualGraph, Digraph.addPot, Digraph.mk.injEq, true_and]
    funext e'
    simp only [hassinLen, Pi.add_apply]
    split_ifs with h1
    · subst h1; rw [cob_eq_of_faces hφ hre]; simp [cob]
    · simp [cob]; ring
  have hyp : DecompHyp (M.dualGraph L) (fun e' => e' ∉ P.darts) P.darts P.faces
      ⟨P.faces, mssp P.darts (c - f₀)⟩ := by
    refine ⟨fun a => by simp, fun a ha => P.face_mem ha,
      fun a ha => P.face_mem (P.rev_mem_darts ha),
      rfl, fun b hb => ?_⟩
    refine ⟨mssp P.darts (c - f₀) b, ?_, fun _ _ => rfl⟩
    have hres : (M.dualGraph L).restrict (fun e' => e' ∉ P.darts) =
        (M.dualGraph (c - f₀)).restrict (fun e' => e' ∉ P.darts) := by
      simp only [Digraph.restrict, CombMap.dualGraph, Digraph.mk.injEq, true_and]
      funext a
      rw [← hL]
      have h1 : a.1 ≠ M.rev e := fun h => a.2 (h ▸ hre)
      simp only [h1, ite_false, Pi.sub_apply, hu a.1 a.2, hoff a.1 a.2]
    rw [hres]
    exact hmssp (c - f₀) (fun e' _ => by simp only [Pi.sub_apply]; linarith [hf₀.le_cap e']) b hb
  have hpotΦ : (M.dualGraph L).IsPot Φ := by
    intro e'
    rw [hLeq]
    simp only [Digraph.addPot, CombMap.dualGraph]
    have : 0 ≤ hassinLen M u (f + M.cob Φ) e x e' := by
      unfold hassinLen; split_ifs
      · exact hx
      · linarith [hg.le_cap e']
    linarith
  exact isPot_congr (isPot_union hyp hpotΦ) fun a => by
    obtain ⟨h1, h2⟩ := union_ends rfl L a
    exact ⟨(hφ _ h1).symm, (hφ _ h2).symm⟩

namespace SW

variable (w : SW)

/-- **After the clip and the push on `e`, the true flow is a pseudoflow for the capacities of
stage `i + 1`** (arithmetic on the words). -/
theorem pseudo2 {c f₀ : D → ℤ} (hc : ∀ e, 0 ≤ c e) {P : SPath M} {b : ℕ} {β : ℕ → F}
    {idx : F → ℕ} (hw : w.OK P c f₀ b β idx) {s : (D → ℤ) × (F → ℤ)}
    (hs : SRep P f₀ b β s w.Fw w.Pw) {Φ : F → ℤ} (hφ : ∀ y ∈ P.faces, s.2 y = Φ y)
    (hg : IsPseudo M (P.cap c (4 * absSum c + 1) w.i) (s.1 + M.cob Φ)) :
    IsPseudo M (P.cap c (4 * absSum c + 1) (w.i + 1))
      (setPair M s.1 (P.d w.i) w.f2 + M.cob Φ) := by
  obtain ⟨hF, hanti, hoff, hph⟩ := hs
  have hi := hw.hi
  have hd := P.d_mem w.i hi
  have hcob : M.cob Φ (P.d w.i) = w.cob := by
    rw [← cob_eq_of_faces hφ hd]
    have hfa : M.face (P.d w.i) ∈ P.faces := P.face_mem hd
    have hfb : M.face (M.rev (P.d w.i)) ∈ P.faces := P.face_mem (P.rev_mem_darts hd)
    simp only [CombMap.cob, SW.cob]
    rw [← hph _ (by rw [hw.ib]; exact hw.idx_lt _ hfb), ← hph _ (by rw [hw.ia]; exact hw.idx_lt _ hfa),
      hw.ia, hw.ib, hw.β_idx _ hfa, hw.β_idx _ hfb]
  rw [setPair_add _ _ _ _ (M.cob_antisymm Φ), hcob]
  -- the arithmetic of the new value
  have hcw := hc (P.d w.i); have hcr := hc (M.rev (P.d w.i))
  rw [← hw.cw] at hcw; rw [← hw.cr] at hcr
  have hval : w.f2 + w.cob ≤ w.cw w.i ∧ -(w.f2 + w.cob) ≤ w.cr w.i := by
    have hm1 : w.f1 + w.cob ≤ w.cw w.i := by
      unfold SW.f1; have := min_le_right (w.Fw w.i + w.cob) (w.cw w.i); omega
    have hm2 : -w.cr w.i ≤ w.f1 + w.cob := by
      unfold SW.f1; have := le_max_right (min (w.Fw w.i + w.cob) (w.cw w.i)) (-w.cr w.i); omega
    have hv1 : w.val0 ≤ w.res := min_le_left _ _
    have hv0 : 0 ≤ w.val0 := by
      unfold SW.val0 SW.res
      split_ifs <;> exact le_min (by omega) (abs_nonneg _)
    unfold SW.f2
    unfold SW.res at hv1
    split_ifs at hv1 ⊢ <;> constructor <;> omega
  refine ⟨setPair_antisymm hg.antisymm _ _, fun e' => ?_⟩
  have hii : ¬ (w.i + 1 ≤ w.i) := by omega
  by_cases h1 : e' = P.d w.i
  · subst h1
    rw [setPair_self]; simp only [P.cap_d c _ hi, hii, ↓reduceIte, ← hw.cw]; exact hval.1
  · by_cases h2 : e' = M.rev (P.d w.i)
    · subst h2
      rw [setPair_rev]; simp only [P.cap_rev_d c _ hi, hii, ↓reduceIte, ← hw.cr]; exact hval.2
    · rw [setPair_of_ne _ _ h1 h2, P.cap_succ c _ hi h1 h2]; exact hg.le_cap e'

/-- **The prices are feasible for the FR call of a stage** (not skipped). -/
theorem isPot {c f₀ : D → ℤ} (hc : ∀ e, 0 ≤ c e) (hf₀ : IsPseudo M c f₀) {P : SPath M}
    {mssp : List D → (D → ℤ) → F → F → Option ℤ} (hmssp : MSSPSpecAt M mssp P) {b : ℕ}
    {β : ℕ → F} {idx : F → ℕ} (hw : w.OK P c f₀ b β idx) {s : (D → ℤ) × (F → ℤ)}
    (hs : SRep P f₀ b β s w.Fw w.Pw) (hinv : EffInv c f₀ P w.i s) (hsk : ¬ w.skip) :
    (DDG.union ⟨P.faces, mssp P.darts (c - f₀)⟩
      (explicitArcs (M.dualGraph (w.lenD P c s.1 s.2)) P.darts)).IsPot s.2 := by
  obtain ⟨Φ, hφ, -, -, hfp⟩ := hinv
  have hi := hw.hi
  have hd := P.d_mem w.i hi
  have he : w.eD P ∈ P.darts := by
    unfold SW.eD; split_ifs
    · exact hd
    · exact P.rev_mem_darts hd
  have hx : 0 ≤ |w.bv| - w.val0 := by unfold SW.skip at hsk; omega
  have hoff' : ∀ e, e ∉ P.darts → setPair M s.1 (P.d w.i) w.f2 e = f₀ e := fun e h => by
    rw [setPair_off hd h]; exact hs.2.2.1 e h
  exact isPot_stage_gen hmssp hf₀ (fun e h => P.cap_of_not_mem c _ _ h) hoff' hφ
    (w.pseudo2 hc hw hs hφ hfp.pseudo) he hx

/-- **The FR answers of a stage at the corners from the natural result** of the fixed program on
the image `frPrm b Dm pm (root) ET EH Lz (2k)` (`Dm`, `pm` agreeing with the dense distance graph
and the prices at the corners, the arcs of `csList_stage`, the crossing inequality). -/
theorem dw_eq {c f₀ : D → ℤ} (hc : ∀ e, 0 ≤ c e) (hf₀ : IsPseudo M c f₀) {P : SPath M}
    (hk : 0 < P.k) {mssp : List D → (D → ℤ) → F → F → Option ℤ} (hmssp : MSSPSpecAt M mssp P)
    {fr : FRFun F} (hfr : FRSpec fr) {b : ℕ} {β : ℕ → F} {idx : F → ℕ}
    (hw : w.OK P c f₀ b β idx) {s : (D → ℤ) × (F → ℤ)} (hs : SRep P f₀ b β s w.Fw w.Pw)
    (hinv : EffInv c f₀ P w.i s) (hsk : ¬ w.skip)
    (hinj : ∀ i < b, ∀ j < b, β i = β j → i = j)
    (hsome : ∀ i < b, ∀ j < b, ∃ a,
      (⟨P.faces, mssp P.darts (c - f₀)⟩ : DDG F).len (β i) (β j) = some a)
    {Dm : ℕ → ℕ → ℕ} (hDm : ∀ i < b, ∀ j < b,
      (Dm i j : ℤ) = ((⟨P.faces, mssp P.darts (c - f₀)⟩ : DDG F).len (β i) (β j)).getD 0)
    {pm : ℕ → ℤ} (hpm : ∀ x < b, pm x = s.2 (β x))
    (hDc : Monge.Crossing b fun i j => (Dm i j : ℤ))
    {L' K : ℕ} {v : ℕ → ℕ} {dd : ℕ → ℤ} {nm : ℕ → ℕ} {Fb Rb : ℕ}
    (hres : FrFix.FResN (MsCall.frPrm b Dm pm w.root
      (fun a => idx (M.face (dartAt P a))) (fun a => idx (M.face (M.rev (dartAt P a))))
      (fun a => w.lenD P c s.1 s.2 (dartAt P a)) (2 * P.k)) L' K v dd nm Fb Rb) :
    ∀ x < b, w.dw P c ⟨P.faces, mssp P.darts (c - f₀)⟩ fr β s x =
      if nm (Fb + x) = 1 then frDec (MsCall.frPrm b Dm pm w.root
        (fun a => idx (M.face (dartAt P a))) (fun a => idx (M.face (M.rev (dartAt P a))))
        (fun a => w.lenD P c s.1 s.2 (dartAt P a)) (2 * P.k)) L' (nm (Rb + x)) else 0 := by
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
  have hres' : FrFix.FResN (Monge.FR.mkPrm b b (fun i j => (Dm i j : ℤ)) pm (idx (β w.root))
      ((explicitArcs (M.dualGraph (w.lenD P c s.1 s.2)) P.darts).map
        fun e => (idx e.1, idx e.2.1, e.2.2))) L' K v dd nm Fb Rb := by
    rw [hridx, ← csList_stage]; exact hres
  have key := fr_corners_eq P hk (w.lenD P c s.1 s.2) hroot hpot hfr hw.β_mem hinj hw.idx_lt
    hw.β_idx hsome rfl (Dm := fun i j => (Dm i j : ℤ)) hDm hpm hDc hres'
  intro x hx
  have hy := hw.β_mem x hx
  have hxi : idx (β x) = x := hinj _ (hw.idx_lt _ hy) _ hx (hw.β_idx _ hy)
  obtain ⟨k1, k2⟩ := key (β x) hy
  rw [hxi] at k1 k2
  have k2' : ∀ ℓ, fr ⟨P.faces, mssp P.darts (c - f₀)⟩
      (explicitArcs (M.dualGraph (w.lenD P c s.1 s.2)) P.darts) (β w.root) s.2 (β x) = some ℓ →
      ℓ = frDec (MsCall.frPrm b Dm pm w.root
        (fun a => idx (M.face (dartAt P a))) (fun a => idx (M.face (M.rev (dartAt P a))))
        (fun a => w.lenD P c s.1 s.2 (dartAt P a)) (2 * P.k)) L' (nm (Rb + x)) := by
    intro ℓ hℓ
    have := k2 ℓ hℓ
    rw [hridx, ← csList_stage] at this
    exact this
  unfold SW.dw
  by_cases hf : nm (Fb + x) = 1
  · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 (k1.1 hf)
    simp only [hf, ↓reduceIte, hℓ, Option.getD_some]
    exact k2' ℓ hℓ
  · have : fr ⟨P.faces, mssp P.darts (c - f₀)⟩ (explicitArcs (M.dualGraph (w.lenD P c s.1 s.2))
        P.darts) (β w.root) s.2 (β x) = none := by
      by_contra hn; exact hf (k1.2 hn)
    simp only [hf, ↓reduceIte, this, Option.getD_none]

end SW

end BKMNW

end PlanarFlow
