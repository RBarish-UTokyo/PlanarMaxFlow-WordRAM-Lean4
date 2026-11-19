module

public import PlanarFlow.BKMNW.LrU

/-!
# The children's records and tags of the large split

**`lrecT s = smXA0 ; lrIni ; lrSetL ; lrTag s ; lrOne ; lrSetR ; lrTag s ; lrOne ; lrFin`**,
**`lrecT_rec`**: `lrec_rec` plus the tags `ntag l`, `ntag r` at `Sb + 3 m + k`, `+ 1` (a large child
is a node: hypotheses `ds.s < #l.piece → ntag l = 1`, the same for `r`), within
`1600 n + 100 k + 1300` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable {gid : D → ℕ} {ν : V → ℕ} {S T : Finset V} {ds : DSys M}

/-- **The children's records and tags of the large split.** -/
def lrecT (s : ℕ) : Stmt := .seq smXA0 (.seq lrIni (.seq lrSetL (.seq (lrTag s) (.seq lrOne
  (.seq lrSetR (.seq (lrTag s) (.seq lrOne lrFin)))))))

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 8000000 in
/-- **The children's records and tags of the large split** (see the module docstring). -/
theorem lrecT_rec (c : Config) (hc : WordsBounded W c) {l r : ADec M} {π : HSep M}
    {Hs : List (Finset V)} {σ st : Perm D} {g : ℕ → D}
    {d m k R n Sb LFb CVb HMb PFb CCb hb : ℕ}
    (r4 : c.nreg 3004 = d) (r50 : c.nreg 6500 = Sb) (hm : c.nmem d = m)
    (hk : c.nmem (d + 1) = k) (hR : c.nmem (d + 7 * m + 4) = R) (hn : c.nmem R = n)
    (o1 : R + 3 + 6 * n + m ≤ Sb) (o2 : d + 7 * m + 4 < R)
    (r00 : c.nreg 8500 = LFb) (r01 : c.nreg 8501 = CVb) (r02 : c.nreg 8502 = HMb)
    (r03 : c.nreg 8503 = PFb) (r04 : c.nreg 8504 = CCb) (r05 : c.nreg 8505 = hb)
    (oL : Sb + 21 * m + 38 * n + 8 * k + 24 ≤ LFb) (oV : Sb + 21 * m + 38 * n + 8 * k + 24 ≤ CVb)
    (oH : Sb + 21 * m + 38 * n + 8 * k + 24 ≤ HMb) (oP : Sb + 21 * m + 38 * n + 8 * k + 24 ≤ PFb)
    (oC : Sb + 21 * m + 38 * n + 8 * k + 24 ≤ CCb)
    (wL : LFb + n ≤ W) (wV : CVb + n ≤ W) (wH : HMb + k ≤ W) (wP : PFb + n ≤ W)
    (wC : CCb + n ≤ W) (hW : 21 ≤ W)
    (arr : RArr M gid ν S T (.node l r π, Hs, σ) m n R g c.nmem)
    (hk' : Hs.length = k) (pw : Hs.Pairwise Disjoint)
    (hSC : Disjoint S π.path.mverts) (hTC : Disjoint T π.path.mverts)
    (hSA : Disjoint S (hunion Hs))
    (stab : Stable st (pdarts M (core M ds.Q (l.piece ∪ r.piece)) Hs))
    (sp : ∀ i < n, g i ∈ pdarts M (core M ds.Q (l.piece ∪ r.piece)) Hs →
      c.nmem (R + 3 + 5 * n + i) < n ∧ g (c.nmem (R + 3 + 5 * n + i)) = st (g i))
    (hLF : ∀ i < n, c.nmem (LFb + i) = bf (g i ∈ l.piece))
    (hCV : ∀ i < n, c.nmem (CVb + i) = bf (M.tail (g i) ∈ π.path.mverts))
    (hHM : ∀ j < Hs.length, c.nmem (HMb + j) = bf (¬ Disjoint (Hs.getD j ∅) π.path.mverts))
    (hPF : ∀ i < n, c.nmem (PFb + i) = bf (g i ∈ π.path.darts.toFinset))
    (hCC : ∀ i < n, c.nmem (CCb + i) =
      bf (g i ∈ pdarts M (core M ds.Q (l.piece ∪ r.piece)) Hs))
    (hlr : ∀ i < n, g i ∈ r.piece ↔ g i ∉ l.piece)
    (hlrev : ∀ d ∈ l.piece, M.rev d ∈ l.piece) (hrrev : ∀ d ∈ r.piece, M.rev d ∈ r.piece)
    (hl : l = ds.dec S T l.piece (childHoles Hs π.path.mverts)
      (childRot M st (pdarts M (core M ds.Q (l.piece ∪ r.piece)) Hs) π.path.darts
        (pdarts M (core M ds.Q l.piece) (childHoles Hs π.path.mverts))) (decide (1 - hb = 1)))
    (hr : r = ds.dec S T r.piece (childHoles Hs π.path.mverts)
      (childRot M st (pdarts M (core M ds.Q (l.piece ∪ r.piece)) Hs) π.path.darts
        (pdarts M (core M ds.Q r.piece) (childHoles Hs π.path.mverts))) (decide (1 - hb = 1)))
    {s : ℕ} (hν : Injective ν) (hpk : PkMin gid ds.pk) (hloop : ∀ d, M.head d ≠ M.tail d)
    (hs : ds.s = s) (hsW : s ≤ W) (hlargeL : ds.s < l.piece.card → ntag l = 1)
    (hlargeR : ds.s < r.piece.card → ntag r = 1) :
    ∃ c' t, Exec I W (lrecT s) c c' t ∧ t ≤ 1600 * n + 100 * k + 1300 ∧
      c'.nmem (Sb + 3 * m + k) = ntag l ∧ c'.nmem (Sb + 3 * m + k + 1) = ntag r ∧
      RecsOut M ds gid ν S T l r π Hs σ (Sb + 21 * m + 4 * k + 2)
        (Sb + 21 * m + 38 * n + 8 * k + 24) (c'.nreg 6501) c'.nmem ∧
      (∀ a, (a < Sb ∨ Sb + 21 * m + 38 * n + 8 * k + 24 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 3013 ∨ 8540 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hmn : m ≤ n := by
    rw [arr.card_m, arr.card]; exact card_le_card (pdarts_subset _ _)
  set A := Sb + 21 * m + 4 * k + 2 with hA
  set Y := A + 16 * n + 4 * k + 2 with hY
  set E := Sb + 21 * m + 38 * n + 8 * k + 24 with hE
  set P := l.piece ∪ r.piece with hP
  -- the registers of stage B
  obtain ⟨c₁, t₁, e₁, ht₁, hR1, s21, -, -, -, -, -, -, -, -, -, m1, n1, rr1, rm1, o1'⟩ :=
    smXA0_exec' (I := I) c hc r4 r50 hm hk hR hn o1 o2 (by omega) hW
  have q1 : ∀ x, (x < 3013 ∨ 8000 ≤ x) → c₁.nreg x = c.nreg x := n1
  have M1 : ∀ a, (a < A ∨ A + n ≤ a) → c₁.nmem a = c.nmem a := m1
  -- the set-up
  obtain ⟨c₂, t₂, e₂, ht₂, hR2, u21, v06, v07, v13, v16, v17, CV2, HM2, SG2, RV2, PF2, m2, n2,
    rr2, rm2, o2'⟩ := lrIni_exec (I := I) c₁ e₁.wb_right hR1 s21
      ((q1 _ (by decide)).trans r01) ((q1 _ (by decide)).trans r02)
      ((q1 _ (by decide)).trans r03) ((q1 _ (by decide)).trans r04) o1 (by omega) (by omega)
      (by omega) (by omega) wV wH wP wC (by omega) hW
      (fun i hi => by rw [M1 _ (Or.inr (by omega)), hCC i hi]; exact bf_le_one _)
  have q2 : ∀ x, (x < 4910 ∨ (4916 < x ∧ x < 6520) ∨ (6529 < x ∧ x < 8506) ∨ 8519 < x) →
      c₂.nreg x = c₁.nreg x := n2
  have M2 : ∀ a, (a < A + 3 * n ∨ (A + 4 * n + k ≤ a ∧ a < Y) ∨ Y + 3 * n ≤ a) →
      c₂.nmem a = c₁.nmem a := fun a ha => m2 a (by omega) (by omega)
  -- the left child's parameters
  obtain ⟨c₃, t₃, e₃, ht₃, p08, p09, n3, m3, rr3, rm3, o3⟩ := lrSetL_exec (I := I) c₂ e₂.wb_right
  have q3 : ∀ x, (x < 8508 ∨ 8509 < x) → c₃.nreg x = c₂.nreg x := n3
  have M31 : ∀ a, (a < A ∨ E ≤ a) → c₃.nmem a = c.nmem a := fun a ha => by
    rw [m3, M2 a (by omega), M1 a (by omega)]
  have hIn3 : LrIn M gid ν S T ds c₃ (.node l r π, Hs, σ) P Hs π.path st g d m k R n Sb A Y
      LFb CCb W := by
    refine ⟨hR2.congr fun x hx => q3 x (by unfold smReg at hx; omega),
      by rw [q3 _ (by decide)]; exact u21,
      by rw [q3 _ (by decide), q2 _ (by decide), q1 _ (by decide)]; exact r00,
      by rw [q3 _ (by decide), q2 _ (by decide), q1 _ (by decide)]; exact r04,
      by rw [q3 _ (by decide)]; exact v06, by rw [q3 _ (by decide)]; exact v16,
      by rw [q3 _ (by decide)]; exact v17, rfl, o1, by omega, by omega, by omega, wL, wC, hW,
      arr.congr fun a a1 a2 => M31 a (Or.inl (by omega)), rfl, rfl, hk', pw, hSC, hTC, hSA,
      stab, fun i hi => ?_, fun i hi => ?_, fun j hj => ?_, fun i hi => ?_, fun i hi => ?_,
      fun i hi => ?_, fun i hi => ?_⟩
    · rw [M31 _ (Or.inl (by omega))]; exact sp i hi
    · rw [m3, CV2 i hi, M1 _ (Or.inr (by omega))]; exact hCV i hi
    · rw [m3, HM2 j (by omega), M1 _ (Or.inr (by omega))]; exact hHM j hj
    · rw [m3, SG2 i hi, M2 (CCb + i) (Or.inr (Or.inr (by omega))),
        M2 (R + 3 + 5 * n + i) (Or.inl (by omega))]
    · rw [m3, RV2 i hi, M2 (R + 3 + n + i) (Or.inl (by omega))]
    · rw [m3, PF2 i hi, M1 _ (Or.inr (by omega))]; exact hPF i hi
    · rw [M31 _ (Or.inr (by omega))]; exact hCC i hi
  -- the left child's tag
  obtain ⟨c₃t, t₃t, e₃t, ht₃t, tgL, hIn3t, mfT, rfT, rrT, rmT, oT⟩ := lrTag_rec (I := I) c₃
    e₃.wb_right (y := chL M l r π Hs σ) (X := l.piece) (t := 0) (s := s) hIn3 p08 (by omega)
    subset_union_left (fun i hi => by rw [M31 _ (Or.inr (by omega)), hLF i hi]; simp) hν hpk
    hloop hs hsW hl hlargeL
  have qT : ∀ x, (x < 3013 ∨ (8000 ≤ x ∧ x < 8522) ∨ 8540 < x) → c₃t.nreg x = c₃.nreg x := rfT
  -- the left child
  obtain ⟨c₄, t₄, e₄, ht₄, recL, zl4, hIn4, mf4, rf4, rr4, rm4, o4⟩ := lrOne_rec (I := I) c₃t
    e₃t.wb_right (y := chL M l r π Hs σ) (X := l.piece) (t := 0) (XX := A + 24 * n + 4 * k + 2)
    (hb := hb) hIn3t (by rw [qT _ (by decide)]; exact p08)
    (by rw [qT _ (by decide), p09, v07]; ring)
    (by rw [qT _ (by decide), q3 _ (by decide), q2 _ (by decide), q1 _ (by decide)]; exact r05)
    (by omega) (by omega) subset_union_left hlrev
    (fun i hi => by
      rw [mfT _ (by omega) (Or.inr (Or.inr ⟨by omega, by omega⟩)), M31 _ (Or.inr (by omega)),
        hLF i hi]; simp) rfl rfl hl
  set zl := c₄.nreg 8510 with hzl
  have q4 : ∀ x, (x < 3013 ∨ (8000 ≤ x ∧ x ≠ 8510)) → c₄.nreg x = c₃t.nreg x := rf4
  have r07' : c₄.nreg 8507 = A + 24 * n + 4 * k + 2 := by
    rw [q4 _ (by decide), qT _ (by decide), q3 _ (by decide), v07]; ring
  -- the right child's parameters
  obtain ⟨c₅, t₅, e₅, ht₅, p11, p08', p09', n5, m5, rr5, rm5, o5⟩ := lrSetR_exec (I := I) c₄
    e₄.wb_right (by rw [r07']; omega) (by omega)
  have q5 : ∀ x, (x < 8508 ∨ (8509 < x ∧ x ≠ 8511)) → c₅.nreg x = c₄.nreg x := n5
  have hIn5 : LrIn M gid ν S T ds c₅ (.node l r π, Hs, σ) P Hs π.path st g d m k R n Sb A Y
      LFb CCb W :=
    hIn4.congr (hIn4.regs.congr fun x hx => q5 x (by unfold smReg at hx; omega))
      (by rw [q5 _ (by decide)]; exact hIn4.r21) (fun x hx => q5 x (by omega))
      (fun a ha => by rw [m5])
  have hLFr : ∀ i < n, c₅.nmem (LFb + i) = bf (g i ∈ l.piece) := fun i hi => by
    rw [m5, mf4 _ (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))),
      mfT _ (by omega) (Or.inr (Or.inr ⟨by omega, by omega⟩)), M31 _ (Or.inr (by omega)), hLF i hi]
  have hLFr' : ∀ i < n, (1 - c₅.nmem (LFb + i)) + (c₅.nmem (LFb + i) - 1) = bf (g i ∈ r.piece) :=
    fun i hi => by
      rw [hLFr i hi]
      by_cases h : g i ∈ l.piece
      · have : g i ∉ r.piece := fun h' => (hlr i hi).1 h' h
        simp [bf, h, this]
      · have : g i ∈ r.piece := (hlr i hi).2 h
        simp [bf, h, this]
  -- the right child's tag
  obtain ⟨c₅t, t₅t, e₅t, ht₅t, tgR, hIn5t, mfT', rfT', rrT', rmT', oT'⟩ := lrTag_rec (I := I) c₅
    e₅.wb_right (y := chR M l r π Hs σ) (X := r.piece) (t := 1) (s := s) hIn5 p08' le_rfl
    subset_union_right hLFr' hν hpk hloop hs hsW hr hlargeR
  have qT' : ∀ x, (x < 3013 ∨ (8000 ≤ x ∧ x < 8522) ∨ 8540 < x) → c₅t.nreg x = c₅.nreg x := rfT'
  -- the right child
  obtain ⟨c₆, t₆, e₆, ht₆, recR, zr6, hIn6, mf6, rf6, rr6, rm6, o6⟩ := lrOne_rec (I := I) c₅t
    e₅t.wb_right (y := chR M l r π Hs σ) (X := r.piece) (t := 1)
    (XX := A + 24 * n + 4 * k + 2 + zl) (hb := hb) hIn5t (by rw [qT' _ (by decide)]; exact p08')
    (by rw [qT' _ (by decide), p09', r07'])
    (by rw [qT' _ (by decide), q5 _ (by decide), q4 _ (by decide), qT _ (by decide),
      q3 _ (by decide), q2 _ (by decide), q1 _ (by decide)]; exact r05) (by omega) (by omega)
      subset_union_right hrrev
    (fun i hi => by
      rw [mfT' _ (by omega) (Or.inr (Or.inr ⟨by omega, by omega⟩)), hLFr' i hi]) rfl rfl hr
  set zr := c₆.nreg 8510 with hzr
  have q6 : ∀ x, (x < 3013 ∨ (8000 ≤ x ∧ x ≠ 8510)) → c₆.nreg x = c₅t.nreg x := rf6
  -- the sizes
  obtain ⟨c₇, t₇, e₇, ht₇, f0, f1, f6501, m7, n7, rr7, rm7, o7⟩ := lrFin_exec (I := I) c₆
    e₆.wb_right (Xb := A + 24 * n + 4 * k + 2) (zl := zl) (zr := zr)
    (by rw [q6 _ (by decide), qT' _ (by decide), q5 _ (by decide), r07'])
    (by rw [q6 _ (by decide), qT' _ (by decide), p11]) rfl (by omega)
  have ht : t₁ + (t₂ + (t₃ + (t₃t + (t₄ + (t₅ + (t₅t + (t₆ + t₇))))))) ≤
      1600 * n + 100 * k + 1300 := by
    clear * - ht₁ ht₂ ht₃ ht₃t ht₄ ht₅ ht₅t ht₆ ht₇; omega
  have tL : c₇.nmem (Sb + 3 * m + k) = ntag l := by
    rw [m7 _ (Or.inl (by omega)), mf6 _ (Or.inl (by omega)),
      mfT' _ (by omega) (Or.inl (by omega)), m5, mf4 _ (Or.inl (by omega))]
    have := tgL; simp only [add_zero] at this; exact this
  have tR : c₇.nmem (Sb + 3 * m + k + 1) = ntag r := by
    rw [m7 _ (Or.inl (by omega)), mf6 _ (Or.inl (by omega))]
    exact tgR
  refine ⟨c₇, _, by
      unfold lrecT
      exact .seq e₁ (.seq e₂ (.seq e₃ (.seq e₃t (.seq e₄ (.seq e₅ (.seq e₅t (.seq e₆ e₇))))))),
    ht, tL, tR,
    ⟨by rw [f6501]; omega, by rw [f6501, f0, f1]; omega, ?_, ?_⟩, fun a ha => ?_, fun x hx => ?_,
    by rw [rr7, rr6, rrT', rr5, rr4, rrT, rr3, rr2, rr1],
    by rw [rm7, rm6, rmT', rm5, rm4, rmT, rm3, rm2, rm1],
    by rw [o7, o6, oT', o5, o4, oT, o3, o2', o1']⟩
  · rw [f6501, f0]
    refine recL.congr fun a a1 a2 => ?_
    rw [m7 a (Or.inr (by omega)), mf6 a (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))),
      mfT' a (by omega) (Or.inr (Or.inr ⟨by omega, by omega⟩)), m5]
  · rw [f6501, f0, f1]
    have e : A + 24 * n + 4 * k + 2 + 2 + zl = A + 24 * n + 4 * k + 2 + zl + 2 := by ring
    rw [e]
    exact recR.congr fun a a1 a2 => m7 a (Or.inr (by omega))
  · rw [m7 a (by omega)]
    rcases ha with ha | ha
    · rw [mf6 a (Or.inl (by omega)), mfT' a (by omega) (Or.inl (by omega)), m5,
        mf4 a (Or.inl (by omega)), mfT a (by omega) (Or.inl (by omega)),
        M31 a (Or.inl (by omega))]
    · rw [mf6 a (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))),
        mfT' a (by omega) (Or.inr (Or.inr ⟨by omega, by omega⟩)), m5,
        mf4 a (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))),
        mfT a (by omega) (Or.inr (Or.inr ⟨by omega, by omega⟩)), M31 a (Or.inr ha)]
  · rw [n7 x (by omega), q6 x (by omega), qT' x (by omega), q5 x (by omega), q4 x (by omega),
      qT x (by omega), q3 x (by omega), q2 x (by omega), q1 x (by omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
