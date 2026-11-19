module

public import PlanarFlow.BKMNW.LrT

/-!
# The tags of the large split: one child (the run and its meaning)

* `dec_small` (a small piece: `ds.dec = smD`);
* **`lrTag_rec`**: from `LrIn` and the flags `|t - LF[i]| = bf (g i ∈ X)` of a child `X ⊆ P`,
  for a call `y` with `y.1 = ds.dec S T X (childHoles Hs ρ.mverts) st' b'` and a hypothesis that a
  large child (`ds.s < #X`) has the tag `1`: within `320 n + 21 k + 200` steps
  `mem (Sb + 3 m + k + t) = ntag y.1` (`PkMin`, `ν` injective, a loopless map), `LrIn` again.
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

/-- A small piece: the decomposition is `smD`. -/
lemma dec_small {X : Finset D} {Hs : List (Finset V)} {st : Perm D} {b : Bool}
    (hs : X.card ≤ ds.s) : ds.dec S T X Hs st b = smD M ds.pk S T X Hs := by
  unfold DSys.dec; rw [decS_small hs]

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 8000000 in
/-- **The tag of one child of the large split** (see the module docstring). -/
theorem lrTag_rec (c : Config) (hc : WordsBounded W c) {x y : MCall M} {P X : Finset D}
    {Hs : List (Finset V)} {ρ : HPath M} {st st' : Perm D} {b' : Bool} {g : ℕ → D}
    {d m k R n Sb A Y LFb CCb t s : ℕ}
    (h : LrIn M gid ν S T ds c x P Hs ρ st g d m k R n Sb A Y LFb CCb W)
    (r08 : c.nreg 8508 = t) (ht1 : t ≤ 1) (hXP : X ⊆ P)
    (hLF : ∀ i < n, (t - c.nmem (LFb + i)) + (c.nmem (LFb + i) - t) = bf (g i ∈ X))
    (hν : Injective ν) (hpk : PkMin gid ds.pk) (hloop : ∀ d, M.head d ≠ M.tail d)
    (hs : ds.s = s) (hsW : s ≤ W)
    (hph : y.1 = ds.dec S T X (childHoles Hs ρ.mverts) st' b')
    (hlarge : ds.s < X.card → ntag y.1 = 1) :
    ∃ c' t', Exec I W (lrTag s) c c' t' ∧ t' ≤ 320 * n + 21 * k + 200 ∧
      c'.nmem (Sb + 3 * m + k + t) = ntag y.1 ∧
      LrIn M gid ν S T ds c' x P Hs ρ st g d m k R n Sb A Y LFb CCb W ∧
      (∀ a, a ≠ Sb + 3 * m + k + t → (a < A + n ∨ (A + 2 * n ≤ a ∧ a < A + 4 * n + k + 2) ∨
        (A + 16 * n + 4 * k + 2 ≤ a ∧ ¬ (Y + 3 * n ≤ a ∧ a < Y + 4 * n))) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 3013 ∨ (8000 ≤ x ∧ x < 8522) ∨ 8540 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨x1, x2, x3⟩ := x
  have hHs := h.hHs
  simp only at hHs
  subst hHs
  have hA := h.regs.hA
  have hY := h.hY
  have oR := h.oR
  have oL := h.oL
  have oC := h.oC
  have wL := h.wL
  have hk := h.hk
  have arr := h.arr
  have hP := h.hP
  simp only at hP
  set Hs' : List (Finset V) := childHoles x2 ρ.mverts with hHs'
  -- stage B with the child's flags
  obtain ⟨c₁, t₁, mem₁, e₁, ht₁, hR1, s21, s33, s34, f1, M1, MM1, KC, HC, s40, CIX, s41, IX2,
    BCm, lo1, mid1, hi1, rg1, rr1, rm1, o1⟩ := lrOneA_exec (I := I) c hc h.regs h.r21 h.r00 r08
      h.r84 h.r16 (fun i hi => (arr.rp i hi).1)
      (fun i hi => by rw [arr.hp i hi, ← hk]; exact hlab_le _ _) oR (by omega)
      (by omega) (by omega) h.wA (by omega) wL h.wC h.hW
  have hA1 : RArr M gid ν S T (x1, x2, x3) m n R g mem₁ :=
    arr.congr fun a a1 a2 => M1 a (by clear * - a2 hA oR; omega)
  obtain ⟨VHC, VKC, -⟩ := smSem_vals (x := (x1, x2, x3)) (L := X) (C := ρ.mverts) (A := A)
    hA1 h.pw h.hSC h.hTC h.hSA
    (fun i hi => by rw [f1 i hi]; exact hLF i hi)
    (fun i hi => by rw [M1 _ (by clear * - hi; omega)]; exact h.cv i hi)
    (fun j hj => by rw [M1 _ (by clear * - hj; omega)]; exact h.hm j hj)
  simp only at VHC VKC
  rw [hk] at VHC
  have LPv : ∀ i < n, mem₁ (A + n + i) = bf (g i ∈ X) := fun i hi => by rw [f1 i hi]; exact hLF i hi
  have q1 : ∀ x, (x < 3013 ∨ 8000 ≤ x) → c₁.nreg x = c.nreg x := rg1
  -- the inputs of the scan
  obtain ⟨c₂, t₂, e₂, ht₂, a00, a01, a02, a03, a04, a05, a22, n2, m2, rr2, rm2, o2⟩ :=
    lrTgR_exec (I := I) c₁ e₁.wb_right hR1 (by omega) h.hW
  rw [s34] at a03; rw [s33] at a04
  have q2 : ∀ x, (x < 5300 ∨ (5305 < x ∧ x < 8522) ∨ (8522 < x ∧ x < 8530) ∨ 8531 < x) →
      c₂.nreg x = c₁.nreg x := n2
  have N2 : ∀ a, a < A + 4 * n + k + 2 → c₂.nmem a = mem₁ a := fun a ha => by
    rw [m2, MM1 a ha]
  -- the scan
  obtain ⟨c₃, t₃, e₃, ht₃, hAo, b10, b11, b13, b14, n3, m3, rr3, rm3, o3⟩ := smA_exec (P := I) c₂
    e₂.wb_right a00 a01 a02 a03 a04 a05 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (fun i hi => by rw [N2 _ (by omega)]; exact (hA1.rp i hi).1)
  have q3 : ∀ x, (x < 5310 ∨ 5353 < x) → c₃.nreg x = c₂.nreg x := n3
  -- the arrays of the child
  have hpw' : Hs'.Pairwise Disjoint := pairwise_childHoles h.pw
  have hSm : SmArr M c₂.nmem n (A + n) (R + 3 + n) (A + 4 * n + k + 2 + 4 * n)
      (A + 4 * n + k + 2 + 3 * n) (R + 3 + 4 * n) g X Hs' S T ν := by
    refine ⟨fun i hi j hj e => arr.g_inj hi hj e, fun d hd => ?_, fun i hi => ?_, fun i hi => ?_,
      fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, hν, hpw'⟩
    · obtain ⟨i, hi, e⟩ := arr.g_surj d (hP ▸ hXP hd); exact ⟨i, hi, e⟩
    · rw [N2 _ (by omega), LPv i hi, bf_ne_zero]
    · rw [N2 _ (by omega)]; exact hA1.rp i hi
    · rw [m2, HC i hi, VHC i hi]
    · rw [m2, KC i hi, VKC i hi]
    · rw [N2 _ (by omega)]; exact hA1.vp i hi
  have hpkX : ∀ X' ⊆ X, ∀ i < n, g i ∈ X' → (∀ j < i, g j ∉ X') → ds.pk X' = g i :=
    fun X' hX' => pk_first arr hpk X' (hP ▸ hX'.trans hXP)
  have hnode := hSm.node hpkX (fun X' hX' => (hpk X' hX').1) hloop hAo
  have hcP : c₃.nreg 5315 = X.card := by
    rw [hAo.cp, ← hSm.sum_card subset_rfl]
    exact sum_congr rfl fun j hj => hSm.pv (mem_range.1 hj)
  -- the tag
  have r08' : c₃.nreg 8508 = t := by
    rw [q3 _ (by decide), q2 _ (by decide), q1 _ (by decide)]; exact r08
  obtain ⟨c₄, t₄, e₄, ht₄, tg, m4, n4, rr4, rm4, o4⟩ := lrTgB_exec (I := I) c₃ e₃.wb_right
    (s := s) (a := Sb + 3 * m + k) rfl rfl rfl rfl rfl (by rw [q3 _ (by decide)]; exact a22) r08' hAo.fx.1 hAo.fy.1
    hAo.fb.1 hsW (by omega) h.hW
  have hval : tgV s (c₃.nreg 5315) (c₃.nreg 5316) (c₃.nreg 5317) (c₃.nreg 5323)
      (c₃.nreg 5327) = ntag y.1 := by
    rw [tgV_eq, hnode, hcP, ← hs]
    split_ifs with hl
    · exact (hlarge hl).symm
    · rw [hph, dec_small (by omega)]
  have q4 : ∀ x, (x < 8524 ∨ (8524 < x ∧ x < 8530) ∨ 8540 < x) → c₄.nreg x = c₃.nreg x := n4
  have Q : ∀ x, (x < 3013 ∨ (8000 ≤ x ∧ x < 8522) ∨ 8540 < x) → c₄.nreg x = c.nreg x :=
    fun x hx => by rw [q4 x (by omega), q3 x (by omega), q2 x (by omega), q1 x (by omega)]
  have hR4 : SmRegs c₄ d m k R n Sb A := hR1.congr fun x hx => by
    rw [q4 x (by unfold smReg at hx; omega), q3 x (by unfold smReg at hx; omega),
      q2 x (by unfold smReg at hx; omega)]
  have MM : ∀ a, a ≠ Sb + 3 * m + k + t → (a < A + n ∨ (A + 2 * n ≤ a ∧ a < A + 4 * n + k + 2) ∨
      (A + 16 * n + 4 * k + 2 ≤ a ∧ ¬ (Y + 3 * n ≤ a ∧ a < Y + 4 * n))) →
      c₄.nmem a = c.nmem a := fun a hne ha => by
    rw [m4 a hne, m3, m2]
    rcases ha with ha | ha | ha
    · exact lo1 a ha
    · exact mid1 a ha.1 ha.2
    · exact hi1 a ha.1 ha.2
  have ht : t₁ + (t₂ + (t₃ + t₄)) ≤ 320 * n + 21 * k + 200 := by
    clear * - ht₁ ht₂ ht₃ ht₄; omega
  refine ⟨c₄, _, .seq e₁ (.seq e₂ (.seq e₃ e₄)), ht, by rw [tg, hval], ?_, MM, Q,
    by rw [rr4, rr3, rr2, rr1], by rw [rm4, rm3, rm2, rm1], by rw [o4, o3, o2, o1]⟩
  refine h.congr hR4 (by rw [q4 _ (by decide), q3 _ (by decide), q2 _ (by decide)]; exact s21)
    (fun x hx => Q x (by omega)) fun a ha => MM a (by omega) (by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
      · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
      · exact Or.inr (Or.inr ⟨by omega, by omega⟩))

end Exec

end MfDrv

end BKMNW

end PlanarFlow
