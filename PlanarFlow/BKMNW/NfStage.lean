module

public import PlanarFlow.BKMNW.NfBound

/-!
# One stage of FixConservationOnPath on words

A machine program keeps the explicit flow of `fixPath` on the darts of the path (`Fw l` the flow on
`P.d l`; the reverse darts by antisymmetry, the other darts are `f₀`) and the prices at the corners
(`Pw x` the price of the face `β x`). This file writes one stage `fpStep` as arithmetic on these
words and the fixed data of the path (capacities `cw l = c (d l)`, `cr l = c (rev (d l))`, the
initial flow `f0w l = f₀ (d l)`, the corner numbers `ia l`, `ib l` of the faces of `d l` and of
`rev (d l)`, the net outflow `dv` of `f₀` at `p i`):

* `div_path_at`: the net outflow at `p i` of a flow agreeing with `h` off the path is that of `h`
  plus the changes on `d i` and on `rev (d (i - 1))` (the only darts of the path leaving `p i`);
* `setPair_setPair_self`, `setPair_setPair_rev`;
* `SW` (the words of a stage), `SW.cob`, `SW.f1`, `SW.bv`, `SW.res`, `SW.val0`, `SW.f2`,
  `SW.skip`, `SW.root`, `SW.ef`, `SW.ph`, `SW.f3`; `SW.eD` (the dart `e` of the stage), `SW.lenD`
  (the lengths of the explicit arcs, as a function on the darts);
* **`fpStep_words`**: with `SRep` (the words represent the state), `fpStep` is
  `(setPair s.1 (d i) f2, s.2)` when `skip`, otherwise
  `(setPair s.1 (d i) (f3 δw), s.2 + φi on the faces along the path)` with `δ` the answer of `fr`
  on the explicit arcs `P.darts.map (face, face ∘ rev, lenD)` from the face `β root` with the
  prices `s.2`, and `δw x = (δ (β x)).getD 0`;
* **`SRep.step`**: the words of the next state.
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

/-! ### The net outflow at a vertex of the path -/

/-- **The net outflow at `p i`** of a flow `g` agreeing with `h` off the path: that of `h` plus the
changes on `d i` and (for `i > 0`) on `rev (d (i - 1))`. -/
lemma div_path_at (P : SPath M) {g h : D → ℤ} (hoff : ∀ e, e ∉ P.darts → g e = h e) {i : ℕ}
    (hi : i < P.k) :
    M.div g (P.p i) = M.div h (P.p i) + (g (P.d i) - h (P.d i)) +
      (if 0 < i then g (M.rev (P.d (i - 1))) - h (M.rev (P.d (i - 1))) else 0) := by
  classical
  set S := univ.filter fun e => M.tail e = P.p i with hS
  have hdiv : M.div g (P.p i) - M.div h (P.p i) = ∑ e ∈ S, (g e - h e) := by
    simp only [CombMap.div, hS, sum_sub_distrib]
  have hmem : ∀ e ∈ S, e ∈ P.darts → e = P.d i ∨ (0 < i ∧ e = M.rev (P.d (i - 1))) := by
    intro e he hd
    have ht : M.tail e = P.p i := (mem_filter.1 he).2
    obtain ⟨l, hl, h1 | h1⟩ := P.mem_darts.1 hd
    · subst h1
      rw [P.tail_d l hl] at ht
      have := P.inj l (by omega) i (by omega) ht
      subst this; exact Or.inl rfl
    · subst h1
      have : M.tail (M.rev (P.d l)) = P.p (l + 1) := P.head_d l hl
      rw [this] at ht
      have := P.inj (l + 1) (by omega) i (by omega) ht
      subst this
      exact Or.inr ⟨by omega, by simp⟩
  have hdi : P.d i ∈ S := mem_filter.2 ⟨mem_univ _, P.tail_d i hi⟩
  by_cases h0 : 0 < i
  · have hri : M.rev (P.d (i - 1)) ∈ S := mem_filter.2 ⟨mem_univ _, by
      have := P.head_d (i - 1) (by omega)
      rw [show i - 1 + 1 = i by omega] at this; exact this⟩
    have hne : P.d i ≠ M.rev (P.d (i - 1)) := P.d_ne_rev hi (by omega)
    have hsub : ({P.d i, M.rev (P.d (i - 1))} : Finset D) ⊆ S := by
      intro e he; simp only [mem_insert, mem_singleton] at he
      rcases he with rfl | rfl
      · exact hdi
      · exact hri
    have hsum := sum_subset hsub (f := fun e => g e - h e) fun e he hT => by
      by_cases hd : e ∈ P.darts
      · rcases hmem e he hd with rfl | ⟨-, rfl⟩
        · simp at hT
        · simp at hT
      · simp [hoff e hd]
    rw [sum_pair hne] at hsum
    simp only [h0, ↓reduceIte]
    linarith
  · have hsub : ({P.d i} : Finset D) ⊆ S := by
      intro e he; rw [mem_singleton.1 he]; exact hdi
    have hsum := sum_subset hsub (f := fun e => g e - h e) fun e he hT => by
      by_cases hd : e ∈ P.darts
      · rcases hmem e he hd with rfl | ⟨h1, -⟩
        · simp at hT
        · exact absurd h1 h0
      · simp [hoff e hd]
    rw [sum_singleton] at hsum
    simp only [h0, ↓reduceIte]
    linarith

/-! ### `setPair` twice -/

lemma setPair_setPair_self (g : D → ℤ) (e : D) (a a' : ℤ) :
    setPair M (setPair M g e a) e a' = setPair M g e a' := by
  funext e'
  simp only [setPair]
  split_ifs <;> rfl

lemma setPair_setPair_rev (g : D → ℤ) (e : D) (a a' : ℤ) :
    setPair M (setPair M g e a) (M.rev e) a' = setPair M g e (-a') := by
  funext e'
  have hne : M.rev e ≠ e := M.rev_ne e
  simp only [setPair, M.rev_rev]
  by_cases h1 : e' = M.rev e
  · subst h1; simp [hne]
  · by_cases h2 : e' = e
    · subst h2; simp [hne.symm]
    · simp [h1, h2]

/-! ### The words of a stage -/

/-- **The words of stage `i`**: the flows `Fw` on the darts of the path, the prices `Pw` at the
corners, the capacities `cw`, `cr` of `d l` and `rev (d l)`, the initial flow `f0w` on `d l`, the
corner numbers `ia`, `ib` of the faces of `d l` and `rev (d l)`, the net outflow `dv` of `f₀` at
`p i`. -/
structure SW where
  i : ℕ
  Fw : ℕ → ℤ
  Pw : ℕ → ℤ
  cw : ℕ → ℤ
  cr : ℕ → ℤ
  f0w : ℕ → ℤ
  ia : ℕ → ℕ
  ib : ℕ → ℕ
  dv : ℤ

namespace SW

variable (w : SW)

/-- `cob φX (d i)`. -/
def cob : ℤ := w.Pw (w.ib w.i) - w.Pw (w.ia w.i)

/-- The clipped flow on `d i`. -/
def f1 : ℤ := max (min (w.Fw w.i + w.cob) (w.cw w.i)) (-w.cr w.i) - w.cob

/-- The net outflow at `p i` after the clip. -/
def bv : ℤ := w.dv + (w.f1 - w.f0w w.i) -
  (if 0 < w.i then w.Fw (w.i - 1) - w.f0w (w.i - 1) else 0)

/-- The residual capacity of `e` (`d i` if `bv < 0`, else `rev (d i)`) for the true flow. -/
def res : ℤ := if w.bv < 0 then w.cw w.i - w.f1 - w.cob else w.cr w.i + w.f1 + w.cob

/-- The push on `e` itself. -/
def val0 : ℤ := min w.res |w.bv|

/-- The flow on `d i` after the push on `e`. -/
def f2 : ℤ := if w.bv < 0 then w.f1 + w.val0 else w.f1 - w.val0

/-- No Hassin step. -/
def skip : Prop := |w.bv| - w.val0 ≤ 0

instance : Decidable w.skip := by unfold skip; infer_instance

/-- The corner of the root `face (rev e)`. -/
def root : ℕ := if w.bv < 0 then w.ib w.i else w.ia w.i

/-- The corner of `face e`. -/
def ef : ℕ := if w.bv < 0 then w.ia w.i else w.ib w.i

/-- The increase of the price of the corner `x` from the FR answers `δw`. -/
def ph (δw : ℕ → ℤ) (x : ℕ) : ℤ := δw x - w.Pw x + w.Pw w.root

/-- The flow on `d i` after Hassin's step. -/
def f3 (δw : ℕ → ℤ) : ℤ := if w.bv < 0 then w.f2 + w.ph δw (w.ia w.i) else w.f2 - w.ph δw (w.ib w.i)

/-- The dart `e` of the stage. -/
def eD (P : SPath M) : D := if w.bv < 0 then P.d w.i else M.rev (P.d w.i)

/-- The lengths of the explicit arcs of Hassin's step, on the darts. -/
noncomputable def lenD (P : SPath M) (c : D → ℤ) (g : D → ℤ) (φX : F → ℤ) (e' : D) : ℤ :=
  if e' = M.rev (w.eD P) then (|w.bv| - w.val0) + M.cob φX (M.rev (w.eD P))
  else P.cap c (4 * absSum c + 1) (w.i + 1) e' - setPair M g (P.d w.i) w.f2 e'

end SW

/-- **The words represent the state**: the flow on the darts of the path, antisymmetry, `f₀` off
the path, the prices at the corners. -/
def SRep (P : SPath M) (f₀ : D → ℤ) (b : ℕ) (β : ℕ → F) (s : (D → ℤ) × (F → ℤ))
    (Fw Pw : ℕ → ℤ) : Prop :=
  (∀ l < P.k, s.1 (P.d l) = Fw l) ∧ M.IsAntisymm s.1 ∧ (∀ e, e ∉ P.darts → s.1 e = f₀ e) ∧
    ∀ x < b, s.2 (β x) = Pw x

/-- The fixed data of the stage words. -/
structure SW.OK (w : SW) (P : SPath M) (c f₀ : D → ℤ) (b : ℕ) (β : ℕ → F) (idx : F → ℕ) :
    Prop where
  hi : w.i < P.k
  cw : w.cw w.i = c (P.d w.i)
  cr : w.cr w.i = c (M.rev (P.d w.i))
  f0 : ∀ l ≤ w.i, w.f0w l = f₀ (P.d l)
  ia : w.ia w.i = idx (M.face (P.d w.i))
  ib : w.ib w.i = idx (M.face (M.rev (P.d w.i)))
  dv : w.dv = M.div f₀ (P.p w.i)
  anti0 : M.IsAntisymm f₀
  β_mem : ∀ x < b, β x ∈ P.faces
  idx_lt : ∀ y ∈ P.faces, idx y < b
  β_idx : ∀ y ∈ P.faces, β (idx y) = y

/-! ### One stage on words -/

theorem fpStep_words {c f₀ : D → ℤ} {P : SPath M} (Dst : DDG F) (fr : FRFun F) {b : ℕ}
    {β : ℕ → F} {idx : F → ℕ} (w : SW) (hw : w.OK P c f₀ b β idx) {s : (D → ℤ) × (F → ℤ)}
    (hs : SRep P f₀ b β s w.Fw w.Pw) :
    fpStep M c P Dst fr w.i s =
      if w.skip then (setPair M s.1 (P.d w.i) w.f2, s.2) else
        (setPair M s.1 (P.d w.i) (w.f3 fun x => ((fr Dst (explicitArcs
            (M.dualGraph (w.lenD P c s.1 s.2)) P.darts) (β w.root) s.2) (β x)).getD 0),
         fun y => if y ∈ P.faces then s.2 y + (((fr Dst (explicitArcs
            (M.dualGraph (w.lenD P c s.1 s.2)) P.darts) (β w.root) s.2) y).getD 0 - s.2 y +
              s.2 (β w.root)) else s.2 y) := by
  obtain ⟨f, φX⟩ := s
  obtain ⟨hF, hanti, hoff, hph⟩ := hs
  simp only at hF hanti hoff hph ⊢
  have hi := hw.hi
  have hd := P.d_mem w.i hi
  have hfa : M.face (P.d w.i) ∈ P.faces := P.face_mem hd
  have hfb : M.face (M.rev (P.d w.i)) ∈ P.faces := P.face_mem (P.rev_mem_darts hd)
  have hβa : β (w.ia w.i) = M.face (P.d w.i) := by rw [hw.ia]; exact hw.β_idx _ hfa
  have hβb : β (w.ib w.i) = M.face (M.rev (P.d w.i)) := by rw [hw.ib]; exact hw.β_idx _ hfb
  have hφa : φX (M.face (P.d w.i)) = w.Pw (w.ia w.i) := by
    rw [← hph _ (by rw [hw.ia]; exact hw.idx_lt _ hfa), hβa]
  have hφb : φX (M.face (M.rev (P.d w.i))) = w.Pw (w.ib w.i) := by
    rw [← hph _ (by rw [hw.ib]; exact hw.idx_lt _ hfb), hβb]
  have hcob : M.cob φX (P.d w.i) = w.cob := by
    simp only [CombMap.cob, SW.cob, hφa, hφb]
  have hg1 : max (min (f (P.d w.i) + M.cob φX (P.d w.i)) (c (P.d w.i))) (-c (M.rev (P.d w.i))) -
      M.cob φX (P.d w.i) = w.f1 := by
    rw [hcob, hF _ hi, ← hw.cw, ← hw.cr]; rfl
  have hb : M.div (setPair M f (P.d w.i) w.f1) (P.p w.i) = w.bv := by
    have hoff' : ∀ e, e ∉ P.darts → setPair M f (P.d w.i) w.f1 e = f₀ e := fun e he => by
      rw [setPair_off hd he]; exact hoff e he
    rw [div_path_at P hoff' hi, setPair_self, ← hw.dv]
    unfold SW.bv
    rw [hw.f0 _ le_rfl]
    by_cases h0 : 0 < w.i
    · have hne1 : M.rev (P.d (w.i - 1)) ≠ P.d w.i := fun h =>
        P.d_ne_rev hi (by omega) h.symm
      have hne2 : M.rev (P.d (w.i - 1)) ≠ M.rev (P.d w.i) := fun h => by
        have := P.d_inj (by omega) hi (M.rev_injective h); omega
      simp only [h0, ↓reduceIte]
      rw [setPair_of_ne _ _ hne1 hne2, hanti, hw.anti0, hF _ (by omega), hw.f0 _ (by omega)]
      ring
    · simp only [h0, ↓reduceIte]; ring
  have heD : (if w.bv < 0 then P.d w.i else M.rev (P.d w.i)) = w.eD P := rfl
  have hii : ¬ (w.i + 1 ≤ w.i) := by omega
  have hres : P.cap c (4 * absSum c + 1) (w.i + 1) (w.eD P) - setPair M f (P.d w.i) w.f1 (w.eD P) -
      M.cob φX (w.eD P) = w.res := by
    unfold SW.eD SW.res
    by_cases h : w.bv < 0
    · simp only [h, ↓reduceIte, P.cap_d c _ hi, hii, setPair_self, hcob, ← hw.cw]
    · simp only [h, ↓reduceIte, P.cap_rev_d c _ hi, hii, setPair_rev, ← hw.cr]
      rw [M.cob_antisymm φX (P.d w.i), hcob]
      ring
  have hval : min w.res |w.bv| = w.val0 := rfl
  have hpush : ∀ t : ℤ, setPair M (setPair M f (P.d w.i) w.f1) (w.eD P)
      (setPair M f (P.d w.i) w.f1 (w.eD P) + t) =
        setPair M f (P.d w.i) (if w.bv < 0 then w.f1 + t else w.f1 - t) := fun t => by
    unfold SW.eD
    by_cases h : w.bv < 0
    · simp only [h, ↓reduceIte, setPair_self, setPair_setPair_self]
    · simp only [h, ↓reduceIte, setPair_rev, setPair_setPair_rev]
      congr 1; ring
  have hf2 : (if w.bv < 0 then w.f1 + w.val0 else w.f1 - w.val0) = w.f2 := rfl
  have hpush2 : ∀ t : ℤ, setPair M (setPair M f (P.d w.i) w.f2) (w.eD P)
      (setPair M f (P.d w.i) w.f2 (w.eD P) + t) =
        setPair M f (P.d w.i) (if w.bv < 0 then w.f2 + t else w.f2 - t) := fun t => by
    unfold SW.eD
    by_cases h : w.bv < 0
    · simp only [h, ↓reduceIte, setPair_self, setPair_setPair_self]
    · simp only [h, ↓reduceIte, setPair_rev, setPair_setPair_rev]
      congr 1; ring
  have hroot_lt : w.root < b := by
    unfold SW.root; split_ifs
    · rw [hw.ib]; exact hw.idx_lt _ hfb
    · rw [hw.ia]; exact hw.idx_lt _ hfa
  have hr : M.face (M.rev (w.eD P)) = β w.root := by
    unfold SW.eD SW.root
    split_ifs
    · exact hβb.symm
    · rw [M.rev_rev]; exact hβa.symm
  simp only [fpStep, hg1, hb, heD, hres, hval, hpush, hf2, hpush2, hr]
  have hlen : (fun e' => if e' = M.rev (w.eD P) then |w.bv| - w.val0 + M.cob φX (M.rev (w.eD P))
      else P.cap c (4 * absSum c + 1) (w.i + 1) e' - setPair M f (P.d w.i) w.f2 e') =
      w.lenD P c f φX := rfl
  rw [hlen]
  generalize fr Dst (explicitArcs (M.dualGraph (w.lenD P c f φX)) P.darts) (β w.root) φX = δ
  have hφr : φX (β w.root) = w.Pw w.root := hph _ hroot_lt
  by_cases hsk : |w.bv| - w.val0 ≤ 0
  · have : w.skip := hsk
    simp only [hsk, this, ↓reduceIte]
  · have : ¬ w.skip := hsk
    simp only [hsk, this, ↓reduceIte]
    refine Prod.ext ?_ rfl
    show setPair M f (P.d w.i) _ = setPair M f (P.d w.i) _
    congr 1
    unfold SW.f3 SW.ph SW.eD
    by_cases h : w.bv < 0
    · simp only [h, ↓reduceIte, hφr, hβa, hφa]
    · simp only [h, ↓reduceIte, hφr, hβb, hφb]

/-- The FR answers of the stage at the corners. -/
noncomputable def SW.dw (w : SW) (P : SPath M) (c : D → ℤ) (Dst : DDG F) (fr : FRFun F)
    (β : ℕ → F) (s : (D → ℤ) × (F → ℤ)) (x : ℕ) : ℤ :=
  ((fr Dst (explicitArcs (M.dualGraph (w.lenD P c s.1 s.2)) P.darts) (β w.root) s.2)
    (β x)).getD 0

/-- `setPair` on the dart `d i` read on `d l`. -/
lemma setPair_d (P : SPath M) (g : D → ℤ) {i l : ℕ} (hi : i < P.k) (hl : l < P.k) (a : ℤ) :
    setPair M g (P.d i) a (P.d l) = if l = i then a else g (P.d l) := by
  by_cases h : l = i
  · subst h; simp only [↓reduceIte]; exact setPair_self _ _ _
  · simp only [h, ↓reduceIte]
    exact setPair_of_ne _ _ (fun e => h (P.d_inj hl hi e)) (P.d_ne_rev hl hi)

/-- **The words of the next state.** -/
theorem SRep.step {c f₀ : D → ℤ} {P : SPath M} (Dst : DDG F) (fr : FRFun F) {b : ℕ}
    {β : ℕ → F} {idx : F → ℕ} (w : SW) (hw : w.OK P c f₀ b β idx) {s : (D → ℤ) × (F → ℤ)}
    (hs : SRep P f₀ b β s w.Fw w.Pw) :
    SRep P f₀ b β (fpStep M c P Dst fr w.i s)
      (fun l => if l = w.i then (if w.skip then w.f2 else w.f3 (w.dw P c Dst fr β s)) else w.Fw l)
      (if w.skip then w.Pw else fun x => w.Pw x + w.ph (w.dw P c Dst fr β s) x) := by
  rw [fpStep_words Dst fr w hw hs]
  obtain ⟨hF, hanti, hoff, hph⟩ := hs
  have hd := P.d_mem w.i hw.hi
  have hflow : ∀ a : ℤ, (∀ l < P.k, setPair M s.1 (P.d w.i) a (P.d l) =
      if l = w.i then a else w.Fw l) ∧ M.IsAntisymm (setPair M s.1 (P.d w.i) a) ∧
      ∀ e, e ∉ P.darts → setPair M s.1 (P.d w.i) a e = f₀ e := fun a =>
    ⟨fun l hl => by rw [setPair_d P _ hw.hi hl]; split_ifs <;> simp_all,
      setPair_antisymm hanti _ _, fun e he => by rw [setPair_off hd he]; exact hoff e he⟩
  by_cases hsk : w.skip
  · simp only [hsk, ↓reduceIte]
    obtain ⟨h1, h2, h3⟩ := hflow w.f2
    exact ⟨h1, h2, h3, hph⟩
  · simp only [hsk, ↓reduceIte]
    obtain ⟨h1, h2, h3⟩ := hflow (w.f3 (w.dw P c Dst fr β s))
    refine ⟨h1, h2, h3, fun x hx => ?_⟩
    simp only [hw.β_mem x hx, ↓reduceIte, SW.ph, SW.dw, hph x hx]
    have hr : w.root < b := by
      unfold SW.root; split_ifs
      · rw [hw.ib]; exact hw.idx_lt _ (P.face_mem (P.rev_mem_darts hd))
      · rw [hw.ia]; exact hw.idx_lt _ (P.face_mem hd)
    rw [hph _ hr]

end BKMNW

end PlanarFlow
