module

public import PlanarFlow.BKMNW.NsLay

/-!
# The negSSSP step at a max-flow call; the identifiers of the calls chosen from `gid`

The frame of a max-flow call (`Lay`) numbers the darts of the piece map by **increasing global
numbers** `gid`. Such a numbering is unique (`gOrd_unique`), so the identifiers of the call used by
the machine (`nsIds` of the frame order) are a function of the call and of `gid` alone, not of the
memory:

* `GOrd gid x h en` (a normalized dart order of the piece map, increasing in `gid`, `EnumOK`),
  **`gOrd_unique`**, `lay_gOrd` (the frame's order `layEn` is one);
* **`negLay gid I x h`**: `negMach` with the identifiers `nsIds` of the `gid`-order of the call
  (when the piece map has a dart and transitive faces; otherwise `negSSSPImpl`), `negLay_spec`;
  **`machMOL gid I`** (the subroutines of the calls: Klein's MSSP, `frRef`, `negLay`,
  `pstflowW`), **`oSpecOn_machMOL`**;
* **`negLay_lay`**: at a call with a frame `Lay … x m en d mem`, `negLay gid I x h` is the machine
  outcome `negMach (layIds …)` for the identifiers of the frame order;
* **`negStep_lay_exec`**: `negStep_exec` restated at a max-flow call: the index arrays of the
  reverse and the rotation are the frame's `RV = d + 4 + m` and `SG = d + 4 + 2 m`; the outcome in
  the copy at `Ob` is **`negLay gid I x h ℓ`**.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace PlanarFlow

namespace BKMNW

namespace NsStep

open Finset Function Equiv Orbit CombMap NegSSSP NegSSSP.Frame OrbLab WordRAM WordRAM.Machine
  MfDrv

universe w

/-! ### Increasing orders are unique -/

/-- **Two orders of the same set increasing in the same key agree on `[0, m)`.** -/
theorem incr_unique {α : Type*} (key : α → ℕ) {m : ℕ} {e₁ e₂ : ℕ → α}
    (i₁ : ∀ i < m, ∀ j < m, e₁ i = e₁ j → i = j) (i₂ : ∀ i < m, ∀ j < m, e₂ i = e₂ j → i = j)
    (s₁ : ∀ y, ∃ i < m, e₁ i = y) (s₂ : ∀ y, ∃ i < m, e₂ i = y)
    (m₁ : ∀ i j, i < j → j < m → key (e₁ i) < key (e₁ j))
    (m₂ : ∀ i j, i < j → j < m → key (e₂ i) < key (e₂ j)) :
    ∀ i < m, e₁ i = e₂ i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨j, hj, ej⟩ := s₂ (e₁ i)
    obtain ⟨j', hj', ej'⟩ := s₁ (e₂ i)
    have hji : i ≤ j := by
      by_contra hc
      have := ih j (by omega) hj
      rw [← this] at ej
      have := i₁ j hj i hi ej
      omega
    have hj'i : i ≤ j' := by
      by_contra hc
      have := ih j' (by omega) hj'
      rw [this] at ej'
      have := i₂ j' hj' i hi ej'
      omega
    rcases Nat.eq_or_lt_of_le hji with e | hlt
    · subst e; exact ej.symm
    rcases Nat.eq_or_lt_of_le hj'i with e' | hlt'
    · subst e'; exact ej'
    have a1 := m₂ i j hlt hj
    have a2 := m₁ i j' hlt' hj'
    rw [ej] at a1
    rw [ej'] at a2
    omega

section Fam

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **A normalized dart order of the piece map of a call, increasing in `gid`.** -/
structure GOrd (gid : D → ℕ) (x : MCall M) (h : PieceInv M x.1.piece x.2.1 x.2.2)
    (en : ℕ → SDart (pdarts M x.1.piece x.2.1)) : Prop where
  pos : 0 < (pdarts M x.1.piece x.2.1).card
  enum : EnumOK (pmap h) en (pdarts M x.1.piece x.2.1).card
  mono : ∀ i j, i < j → j < (pdarts M x.1.piece x.2.1).card → gid (en i).1 < gid (en j).1
  norm : ∀ i, (pdarts M x.1.piece x.2.1).card ≤ i → en i = en 0

/-- **The increasing order is unique.** -/
theorem gOrd_unique {gid : D → ℕ} {x : MCall M} {h : PieceInv M x.1.piece x.2.1 x.2.2}
    {e₁ e₂ : ℕ → SDart (pdarts M x.1.piece x.2.1)} (h₁ : GOrd gid x h e₁) (h₂ : GOrd gid x h e₂) :
    e₁ = e₂ := by
  have hu := incr_unique (fun y : SDart (pdarts M x.1.piece x.2.1) => gid y.1) h₁.enum.inj
    h₂.enum.inj h₁.enum.surj h₂.enum.surj h₁.mono h₂.mono
  funext i
  by_cases hi : i < (pdarts M x.1.piece x.2.1).card
  · exact hu i hi
  · rw [h₁.norm i (by omega), h₂.norm i (by omega)]
    exact hu 0 h₁.pos

lemma nsIds_congr {D' V' F' : Type w} [Fintype D'] [DecidableEq D'] [Fintype V']
    [DecidableEq V'] [Fintype F'] [DecidableEq F'] {M' : CombMap D' V' F'} {en en' : ℕ → D'}
    {m : ℕ} (h : EnumOK M' en m) (h' : EnumOK M' en' m) (e : en = en') {d d' : D'} (ed : d = d') :
    nsIds M' h d = nsIds M' h' d' := by
  subst e ed; rfl

open Classical in
/-- **The machine's negative-length shortest paths at a call, identifiers from `gid`**: `negMach`
with the identifiers `nsIds` of the `gid`-increasing dart order of the piece map (when the piece
map has a dart and its faces are transitive), otherwise the reference `negSSSPImpl`. -/
noncomputable def negLay (gid : D → ℕ) (I : Input) (x : MCall M)
    (h : PieceInv M x.1.piece x.2.1 x.2.2) :
    (SDart (pdarts M x.1.piece x.2.1) → ℤ) →
      Option (SFace x.2.2 (pdarts M x.1.piece x.2.1) (revPerm M) → ℤ) :=
  if hx : ∃ en, GOrd gid x h en then
    negMach (nsIds (pmap h) hx.choose_spec.enum (hx.choose 0)) (pmap h) I
  else negSSSPImpl (fun X => frRef X) (pmap h)

/-- `negLay` meets the specification of negative-length shortest paths. -/
theorem negLay_spec (gid : D → ℕ) (I : Input) (x : MCall M)
    (h : PieceInv M x.1.piece x.2.1 x.2.2) : NegSSSPSpec (pmap h) (negLay gid I x h) := by
  unfold negLay
  split_ifs with hx
  · exact negMach_spec _ _ _
  · intro ℓ
    exact negSSSPImpl_spec (fun X => frRef X) (fun X => frRef_spec X) (pmap h) ℓ

/-- **The subroutines of the calls, identifiers from `gid`**: Klein's MSSP, `frRef`, `negLay`,
`pstflowW`. -/
noncomputable def machMOL (gid : D → ℕ) (I : Input) : MOFam M :=
  fun x h => ⟨Klein.msspPlaneK (pmap h), frRef _, negLay gid I x h, STFlow.pstflowW (pmap h)⟩

/-- **They meet their specifications at every call.** -/
theorem oSpecOn_machMOL (gid : D → ℕ) (I : Input) (Reach : MCall M → Prop) :
    OSpecOn M (machMOL gid I) Reach :=
  fun x _ h hpl hrot hface => ⟨Klein.msspPlaneK_spec hpl hrot hface, frRef_spec _,
    negLay_spec _ _ _ _, STFlow.pstflowW_spec hpl⟩

end Fam

section Lay

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {x : MCall M} {m : ℕ} {en : ℕ → D}
  {d : ℕ} {mem : ℕ → ℕ} {W : ℕ}

/-- The identifiers of the frame order of a call. -/
noncomputable abbrev layIds (hP : PieceInv M x.1.piece x.2.1 x.2.2)
    (hl : Lay M gid u S T Z x m en d mem) (hm : 0 < m) (hft : (pmap hP).FaceTrans) :
    GIds (SDart (pdarts M x.1.piece x.2.1)) (SFace x.2.2 (pdarts M x.1.piece x.2.1) (revPerm M)) :=
  nsIds (pmap hP) (lay_enumOK hP hl hm hft) (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm 0)

/-- The frame has `|pdarts|` darts. -/
lemma lay_card (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hl : Lay M gid u S T Z x m en d mem)
    (hm : 0 < m) (hft : (pmap hP).FaceTrans) : m = (pdarts M x.1.piece x.2.1).card := by
  have := card_eq_m (lay_enumOK hP hl hm hft)
  rw [Fintype.card_coe] at this
  exact this.symm

/-- **The frame order is the `gid`-order.** -/
theorem lay_gOrd (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hl : Lay M gid u S T Z x m en d mem)
    (hm : 0 < m) (hft : (pmap hP).FaceTrans) (hc : m = (pdarts M x.1.piece x.2.1).card) :
    GOrd gid x hP (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm) := by
  have he := lay_enumOK hP hl hm hft
  subst hc
  refine ⟨hm, he, fun i j hij hj => ?_, fun i hi => ?_⟩
  · rw [layEn_val (by omega), layEn_val hj]; exact hl.en_mono i j hij hj
  · unfold layEn; simp only [show ¬ i < (pdarts M x.1.piece x.2.1).card by omega, hm,
      ↓reduceDIte]

/-- **At a call with a frame, `negLay` is the machine outcome for the frame's identifiers.** -/
theorem negLay_lay (I : Input) (hP : PieceInv M x.1.piece x.2.1 x.2.2)
    (hl : Lay M gid u S T Z x m en d mem) (hm : 0 < m) (hft : (pmap hP).FaceTrans) :
    negLay gid I x hP = negMach (layIds hP hl hm hft) (pmap hP) I := by
  have hc := lay_card hP hl hm hft
  have hg := lay_gOrd hP hl hm hft hc
  have hx : ∃ en', GOrd gid x hP en' := ⟨_, hg⟩
  unfold negLay
  rw [dite_cond_eq_true (eq_true hx)]
  have e := gOrd_unique hx.choose_spec hg
  congr 1
  subst hc
  exact nsIds_congr _ _ e (by rw [e])

open MfDrv in
/-- **The negSSSP step at a max-flow call** (`negStep_exec` with the frame's dart order): from a
frame `Lay … x m en d (c.nmem)` of the call (`RV` at `d + 4 + m`, `SG` at `d + 4 + 2 m`), the
lengths `LN = ℓ + K` at `LNb`, and the zero memory `≤ Wz`, `negStep` runs within
`300 m + 200 + (9 negT C C₀ m + 12 fsz + 7 fin + 3291 + (12 m + 4628))` steps; the copy at `Ob`
holds **`negLay gid I x hP ℓ`** (`Res` for the identifiers `layIds` of the frame order); the
memory `≤ Wz` zero again; the memory above `Wz` outside the frame at `A`, the copy at `Ob` and the
log at `p` kept (the max-flow frame at `d` in particular); the driver registers `3000 … 3012`
kept. -/
theorem negStep_lay_exec (C C₀ : ℕ) (hC : 200000 ≤ C) (hP : PieceInv M x.1.piece x.2.1 x.2.2)
    (ℓ : SDart (pdarts M x.1.piece x.2.1) → ℤ) (hpre : NegPre (pmap hP) ℓ) (I P' : Input)
    (c : Config) (hc : WordsBounded W c) (hl : Lay M gid u S T Z x m en d c.nmem) (hm : 0 < m)
    {LNb K S' A Wz Ob p : ℕ} (r00 : c.nreg 7500 = m) (r01 : c.nreg 7501 = d + 4 + m)
    (r02 : c.nreg 7502 = d + 4 + 2 * m) (r03 : c.nreg 7503 = LNb) (r04 : c.nreg 7504 = K)
    (r05 : c.nreg 7505 = S') (r06 : c.nreg 7506 = A) (r22 : c.nreg 7322 = Ob)
    (r24 : c.nreg 7324 = p)
    (hLN : ∀ i < m, c.nmem (LNb + i) =
      (ℓ (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm i) + K).toNat)
    (hK : ∀ i < m, |ℓ (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm i)| ≤ K)
    (hzW : ∀ a ≤ Wz, c.nmem a = 0) (hS : S' + 9 * m + 1 + tsz m ≤ Wz + 1)
    (sR : Wz < d) (sN : Wz < LNb) (hA : Wz < A)
    (dR : d + 4 + m + m ≤ A ∨ A + 6 + 10 * m ≤ d + 4 + m) (wR : d + 4 + 3 * m ≤ W)
    (wN : LNb + m ≤ W) (wA : A + 6 + 10 * m ≤ W)
    (wL : 2 * K + rtL (pmap hP) ℓ ≤ W) (hWz : rtW m (rtL (pmap hP) ℓ) m ≤ Wz)
    (hAO : A + Frame.fsz (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd).card
      (ck (pmap hP).dual (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd)) ≤ Ob)
    (hOp : Ob + Frame.fsz (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd).card
      (ck (pmap hP).dual (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd)) ≤ p)
    (hpW : p + negT C C₀ m ≤ W) (hw2 : spWs m + 205 ≤ W) (hw3 : fxWB m (rtL (pmap hP) ℓ) ≤ W) :
    ∃ d' t, Exec P' W negStep c d' t ∧
      t ≤ 300 * m + 200 + (9 * negT C C₀ m +
        12 * Frame.fsz (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd).card
          (ck (pmap hP).dual (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd)) +
        7 * Frame.fin (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd).card
          (ck (pmap hP).dual (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd)) + 3291 +
        (12 * m + 4628)) ∧
      (∀ a ≤ Wz, d'.nmem a = 0) ∧
      Res (layIds hP hl hm hpre.2.2.1) (pmap hP).dual (rtL (pmap hP) ℓ)
        (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd)
        (negLay gid I x hP ℓ) Ob
        (Ob + Frame.fsz (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd).card
          (ck (pmap hP).dual (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd))) d' ∧
      (∀ a, Wz < a →
        (a < A ∨ A + Frame.fsz (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd).card
          (ck (pmap hP).dual (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd)) ≤ a) →
        (a < Ob ∨ Ob + Frame.fsz (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd).card
          (ck (pmap hP).dual (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd)) ≤ a) →
        (a < p ∨ p + negT C C₀ m ≤ a) → d'.nmem a = c.nmem a) ∧
      (∀ r, 3000 ≤ r → r ≤ 3012 → d'.nreg r = c.nreg r) ∧
      (∀ r, ¬ ncScr r → ¬ NsScr r → d'.nreg r = c.nreg r) ∧
      d'.rreg = c.rreg ∧ d'.rmem = c.rmem ∧ d'.output = c.output := by
  rw [negLay_lay I hP hl hm hpre.2.2.1]
  exact negStep_exec C C₀ hC (lay_enumOK hP hl hm hpre.2.2.1) _ ℓ hpre I P' c hc r00 r01 r02 r03
    r04 r05 r06 r22 r24 (fun i hi => lay_rv hP hl hm hpre.2.2.1 hi)
    (fun i hi => lay_rt hP hl hm hpre.2.2.1 hi) hLN hK hzW hS (by omega) (by omega) sN hA dR
    (by omega) (by omega) wN wA wL hWz hAO hOp hpW hw2 hw3

end Lay

end NsStep

end BKMNW

end PlanarFlow
