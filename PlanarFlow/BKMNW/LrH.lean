module

public import PlanarFlow.BKMNW.LrG
public import PlanarFlow.BKMNW.SmXD

/-!
# The children's records of the large split: one child composed (the run)

**`lrOne_rec`** (see `LrG.lean`): `lrOne = lrOneA ; lrCr ; lrOneB` writes the record `RecAt` of a
child call at `XX + 2`, within `400 n + 21 k + 310` steps, and keeps `LrIn`.
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

lemma bf_mul_bf (p q : Prop) [Decidable p] [Decidable q] : bf p * bf q = bf (p ∧ q) := by
  unfold bf; by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- The extension of a stable state by the identity is stable on any superset. -/
lemma stable_ret_sup {st : Perm D} {B P : Finset D} (hBP : B ⊆ P) : Stable (ret st B) P :=
  fun x hx => by
    by_cases h : x ∈ B
    · exact hBP (ret_mem h)
    · rw [ret_apply_of_not_mem h]; exact hx

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 8000000 in
/-- **One child's record on the machine** (see the module docstring). -/
theorem lrOne_rec (c : Config) (hc : WordsBounded W c) {x y : MCall M} {P X : Finset D}
    {Hs : List (Finset V)} {ρ : HPath M} {st : Perm D} {g : ℕ → D}
    {d m k R n Sb A Y LFb CCb XX t hb : ℕ}
    (h : LrIn M gid ν S T ds c x P Hs ρ st g d m k R n Sb A Y LFb CCb W)
    (r08 : c.nreg 8508 = t) (r09 : c.nreg 8509 = XX) (r05 : c.nreg 8505 = hb)
    (oX1 : Y + 8 * n ≤ XX) (oX2 : XX + 7 * n + 8 ≤ Y + 22 * n + 20)
    (hXP : X ⊆ P) (hXr : ∀ d ∈ X, M.rev d ∈ X)
    (hLF : ∀ i < n, (t - c.nmem (LFb + i)) + (c.nmem (LFb + i) - t) = bf (g i ∈ X))
    (hyX : y.1.piece = X) (hyH : y.2.1 = childHoles Hs ρ.mverts)
    (hph : y.1 = ds.dec S T X y.2.1 (childRot M st (pdarts M (core M ds.Q P) Hs) ρ.darts
      (pdarts M (core M ds.Q X) y.2.1)) (decide (1 - hb = 1))) :
    ∃ c' t', Exec I W lrOne c c' t' ∧ t' ≤ 400 * n + 21 * k + 310 ∧
      RecAt M ds gid ν S T y (XX + 2) (c'.nreg 8510) c'.nmem ∧ c'.nreg 8510 ≤ 7 * n + 3 ∧
      LrIn M gid ν S T ds c' x P Hs ρ st g d m k R n Sb A Y LFb CCb W ∧
      (∀ a, (a < A + n ∨ (A + 2 * n ≤ a ∧ a < A + 4 * n + k + 2) ∨ (Y ≤ a ∧ a < Y + 3 * n) ∨
        (Y + 8 * n ≤ a ∧ a < XX + 2) ∨ XX + 7 * n + 6 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 3013 ∨ (8000 ≤ x ∧ x ≠ 8510)) → c'.nreg x = c.nreg x) ∧
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
  have wC := h.wC
  have hk := h.hk
  have arr := h.arr
  have hP := h.hP
  simp only at hP
  set B : Finset D := pdarts M (core M ds.Q P) x2 with hB
  set Hs' : List (Finset V) := childHoles x2 ρ.mverts with hHs'
  set Bc : Finset D := pdarts M (core M ds.Q X) Hs' with hBc
  have hgP : ∀ i < n, g i ∈ P := fun i hi => hP ▸ arr.g_mem i hi
  have hPr : ∀ d ∈ P, M.rev d ∈ P := fun d hd => by
    rw [← hP] at hd ⊢
    obtain ⟨i, hi, rfl⟩ := arr.g_surj d hd
    rw [← (arr.rp i hi).2]; exact arr.g_mem _ (arr.rp i hi).1
  have hBP : B ⊆ P := (pdarts_subset _ _).trans (fun d hd => (mem_core.1 hd).1)
  have hBr : ∀ d ∈ B, M.rev d ∈ B := stable_pdarts (fun d hd => by
    rw [mem_core] at hd ⊢
    exact ⟨hPr _ hd.1, by rw [CombMap.tail_rev]; exact hd.2.2,
      by rw [CombMap.head_rev]; exact hd.2.1⟩) x2
  have hBcsub : Bc ⊆ B \ ρ.darts.toFinset := childBc_sub ρ hXP
  have hBcX : Bc ⊆ X := fun d hd => (mem_core.1 (mem_pdarts.1 hd).1).1
  -- stage 1: the flags, stage B, the core flags of the child
  obtain ⟨c₁, t₁, mem₁, e₁, ht₁, hR1, s21, s33, s34, f1, M1, MM1, KC, HC, s40, CIX, s41, IX2,
    BCm, lo1, mid1, hi1, rg1, rr1, rm1, o1⟩ := lrOneA_exec (I := I) c hc h.regs h.r21 h.r00 r08
      h.r84 h.r16 (fun i hi => (arr.rp i hi).1)
      (fun i hi => by rw [arr.hp i hi, ← hk]; exact hlab_le _ _) oR (by omega)
      (by omega) (by omega) h.wA (by omega) wL wC h.hW
  -- the meaning of the children's data
  have hA1 : RArr M gid ν S T (x1, x2, x3) m n R g mem₁ :=
    arr.congr fun a a1 a2 => M1 a (by clear * - a2 hA oR; omega)
  obtain ⟨VHC, VKC, VCF⟩ := smSem_vals (x := (x1, x2, x3)) (L := X) (C := ρ.mverts) (A := A)
    hA1 h.pw h.hSC h.hTC h.hSA
    (fun i hi => by rw [f1 i hi]; exact hLF i hi)
    (fun i hi => by rw [M1 _ (by clear * - hi; omega)]; exact h.cv i hi)
    (fun j hj => by rw [M1 _ (by clear * - hj; omega)]; exact h.hm j hj)
  simp only at VHC VKC VCF
  rw [hk] at VHC VCF
  have LPv : ∀ i < n, mem₁ (A + n + i) = bf (g i ∈ X) := fun i hi => by rw [f1 i hi]; exact hLF i hi
  have BCv : ∀ i < n, c₁.nmem (Y + 3 * n + i) = bf (g i ∈ Bc) := fun i hi => by
    rw [BCm i hi, VCF i hi, h.cc i hi, bf_mul_bf]
    exact bf_congr (mem_childBc_iff hXP).symm
  -- stage 2: the child's rotation over the parent record
  have q1 : ∀ x, (x < 3013 ∨ 8000 ≤ x) → c₁.nreg x = c.nreg x := rg1
  have Y1 : ∀ a, Y ≤ a → a < Y + 3 * n → c₁.nmem a = c.nmem a := fun a a1 a2 =>
    hi1 a (by clear * - a1 hY; omega) (by clear * - a2; omega)
  obtain ⟨c₂, t₂, e₂, ht₂, CN, M2, rg2, rr2, rm2, o2⟩ := lrCr_exec (I := I) M (ret st B) P
    ρ.darts Bc c₁ e₁.wb_right hR1.r04 ((q1 _ (by decide)).trans h.r06) (by omega) (by omega)
    (fun i hi j hj e => arr.g_inj hi hj e) hgP (fun d hd => arr.g_surj d (hP ▸ hd))
    (stable_ret_sup hBP) hPr (hpath_rev_mem ρ) (hBcsub.trans (sdiff_subset_sdiff hBP le_rfl))
    (fun i hi => by
      have hcc : c.nmem (CCb + i) = bf (g i ∈ B) := h.cc i hi
      rw [Y1 _ le_self_add (by clear * - hi; omega), h.sg i hi, hcc]
      by_cases hgB : g i ∈ B
      · have hs := h.sp i hi hgB
        simp only [bf, hgB, ↓reduceIte, one_ne_zero]
        exact ⟨hs.1, by rw [hs.2, ret_stable_apply h.stab hgB]⟩
      · simp only [bf, hgB, ↓reduceIte]
        exact ⟨hi, by rw [ret_apply_of_not_mem hgB]⟩)
    (fun i hi => by
      rw [Y1 _ (by clear * - hi; omega) (by clear * - hi; omega), h.rv i hi]
      exact arr.rp i hi)
    (fun i hi => by
      rw [Y1 _ (by clear * - hi; omega) (by clear * - hi; omega), h.pf i hi]; rfl)
    (fun i hi => by rw [BCv i hi]; rfl)
  have q2 : ∀ x, (x < 6200 ∨ 6250 < x) → c₂.nreg x = c₁.nreg x := rg2
  have N21 : ∀ a, a < Y + 4 * n → c₂.nmem a = c₁.nmem a := fun a ha => M2 a (by omega)
  have hR2 : SmRegs c₂ d m k R n Sb A := hR1.congr fun x hx =>
    q2 x (by clear * - hx; unfold smReg at hx; omega)
  -- stage 3: the record
  set F : ℕ → ℕ := fun j => bf (g j ∈ X) with hF
  set FY : ℕ → ℕ := fun j => bf (g j ∈ pdarts M X Hs') with hFY
  have cA : ∀ i ≤ n, cnt (fun j => mem₁ (A + n + j)) i = cnt F i := fun i hi =>
    cnt_congr fun j hj => LPv j (by omega)
  have cY : ∀ i ≤ n, cnt (fun j => smCF mem₁ A R n k j) i = cnt FY i := fun i hi =>
    cnt_congr fun j hj => VCF j (by omega)
  have A21 : ∀ a, a < A + 4 * n + k + 2 → c₂.nmem a = mem₁ a := fun a ha => by
    rw [N21 a (by clear * - ha hY; omega), MM1 a ha]
  have CI2 : ∀ i < n, g i ∈ X →
      c₂.nmem (A + 11 * n + 4 * k + 2 + i) = cnt F i ∧
      c₂.nmem (A + 12 * n + 4 * k + 2 + cnt F i) = i := fun i hi hX => by
    have hf : 0 < mem₁ (A + n + i) := by rw [LPv i hi]; exact (bf_pos).2 hX
    obtain ⟨a1, a2⟩ := CIX i hi hf
    rw [cA i hi.le] at a1 a2
    have := cnt_le F i
    rw [N21 _ (by clear * - hi hY; omega), N21 _ (by clear * - hi this hY; omega)]
    exact ⟨a1, a2⟩
  have IX22 : ∀ i < n, g i ∈ pdarts M X Hs' →
      c₂.nmem (A + 15 * n + 4 * k + 2 + cnt FY i) = i := fun i hi hY' => by
    have hf : 0 < smCF mem₁ A R n k i := by rw [VCF i hi]; exact (bf_pos).2 hY'
    have a2 := IX2 i hi hf
    rw [cY i hi.le] at a2
    have := cnt_le FY i
    rw [N21 _ (by clear * - hi this hY; omega)]
    exact a2
  have rpA : ∀ i < n, c₂.nmem (R + 3 + n + i) < n ∧ g (c₂.nmem (R + 3 + n + i)) = M.rev (g i) :=
    fun i hi => by rw [A21 _ (by clear * - hi hA oR; omega)]; exact hA1.rp i hi
  have r40 : c₂.nreg 5540 = cnt F n := by rw [q2 _ (by decide), s40, cA n le_rfl]
  have r41 : c₂.nreg 5541 = cnt FY n := by rw [q2 _ (by decide), s41, cY n le_rfl]
  have hFn : cnt F n ≤ n := cnt_le F n
  have hFYn : cnt FY n ≤ n := cnt_le FY n
  obtain ⟨c₃, t₃, e₃, ht₃, hR3, u21, u10, w0, w1, w2, GP, RP, HP, KP, VP, SP, FXo, lo3, hi3, rg3,
    rr3, rm3, o3⟩ := lrOneB_exec (I := I) c₂ e₂.wb_right hR2
      ((q2 _ (by decide)).trans s21) ((q2 _ (by decide)).trans s33)
      ((q2 _ (by decide)).trans s34) r40 r41
      ((q2 _ (by decide)).trans ((q1 _ (by decide)).trans r05))
      ((q2 _ (by decide)).trans ((q1 _ (by decide)).trans r09))
      ((q2 _ (by decide)).trans ((q1 _ (by decide)).trans h.r16))
      ((q2 _ (by decide)).trans ((q1 _ (by decide)).trans h.r17))
      (fun i hi hf => by
        have hX : g i ∈ X := by
          rw [A21 _ (by clear * - hi; omega), LPv i hi] at hf; exact (bf_pos).1 hf
        have ec : cnt (fun j => c₂.nmem (A + n + j)) i = cnt F i := cnt_congr fun j hj => by
          rw [A21 _ (by clear * - hj hi; omega), LPv j (by omega)]
        rw [ec]; exact CI2 i hi hX)
      (cnt_congr fun j hj => by rw [A21 _ (by clear * - hj; omega), LPv j hj]).symm
      hFYn
      (fun j hj => by
        obtain ⟨i, hi, hfi, rfl⟩ := cnt_surj FY n j hj
        rw [IX22 i hi ((bf_pos).1 hfi)]; exact hi)
      (fun i hi => (rpA i hi).1)
      (fun i hi hf => by
        rw [N21 _ (by clear * - hi; omega), BCv i hi] at hf
        rw [A21 _ (by clear * - hi; omega), LPv i hi]
        exact (bf_pos).2 (hBcX ((bf_pos).1 hf)))
      (fun i hi hf => by
        rw [N21 _ (by clear * - hi; omega), BCv i hi] at hf
        exact (CN i hi ((bf_pos).1 hf)).1)
      oR (by omega) oX1 (by omega) h.hW
  -- the meaning of the record
  have hst : ∀ i < n, g i ∈ Bc → c₂.nmem (Y + 6 * n + i) < n ∧
      g (c₂.nmem (Y + 6 * n + i)) = childRot M st B ρ.darts Bc (g i) := fun i hi hb' => by
    obtain ⟨a1, a2⟩ := CN i hi hb'
    rw [childRot_ret h.stab hBP hBr hBcsub] at a2
    exact ⟨a1, a2⟩
  have hIXl : ∀ j < cnt F n, c₂.nmem (A + 12 * n + 4 * k + 2 + j) < n := fun j hj => by
    obtain ⟨i, hi, hfi, rfl⟩ := cnt_surj F n j hj
    rw [(CI2 i hi ((bf_pos).1 hfi)).2]; exact hi
  have hrec := lrRec_sem (ds := ds) (y := y) (P := P) (X := X) (g := g) (n := n)
    (st' := childRot M st B ρ.darts Bc) (bb := 1 - hb)
    (CI := fun i => c₂.nmem (A + 11 * n + 4 * k + 2 + i))
    (IX := fun j => c₂.nmem (A + 12 * n + 4 * k + 2 + j))
    (IX2 := fun j => c₂.nmem (A + 15 * n + 4 * k + 2 + j))
    (RPf := fun i => c₂.nmem (R + 3 + n + i)) (CN := fun i => c₂.nmem (Y + 6 * n + i))
    (mem := c₃.nmem) (Rp := XX + 2)
    (fun i hi j hj e => arr.g_inj hi hj e) (fun d hd => arr.g_surj d (hP ▸ hd)) arr.g_mono hXP hXr
    hyX (by
      have e := hph
      rw [show pdarts M (core M ds.Q X) y.2.1 = Bc by rw [hyH]] at e
      exact e) (by omega)
    (fun d hd => by rw [hyH] at hd; unfold childRot; exact hBcX (ret_mem hd))
    (fun i hi hX => CI2 i hi hX) (fun i hi hY' => by rw [hyH] at hY' ⊢; exact IX22 i hi hY')
    rpA (fun i hi hb' => by rw [hyH] at hb'; exact hst i hi hb')
    w0 w1 w2
    (fun j hj => by
      have e1 := hIXl j hj
      rw [GP j hj, A21 (R + 3 + c₂.nmem (A + 12 * n + 4 * k + 2 + j))
        (by clear * - e1 hA oR; omega)]
      exact hA1.gp _ e1)
    (fun i hi hX => by
      have hf : 0 < c₂.nmem (A + n + i) := by
        rw [A21 _ (by clear * - hi; omega), LPv i hi]; exact (bf_pos).2 hX
      exact RP i hi hf)
    (fun j hj => by
      have h1 := hIXl j hj
      rw [HP j hj, N21 (A + 4 * n + k + 2 + 4 * n + c₂.nmem (A + 12 * n + 4 * k + 2 + j))
        (by clear * - h1 hY; omega), HC _ h1, VHC _ h1, hyH])
    (fun j hj => by
      have h1 := hIXl j hj
      rw [KP j hj, N21 (A + 4 * n + k + 2 + 3 * n + c₂.nmem (A + 12 * n + 4 * k + 2 + j))
        (by clear * - h1 hY; omega), KC _ h1, VKC _ h1, hyH])
    (fun j hj => by
      have h1 := hIXl j hj
      rw [VP j hj, A21 (R + 3 + 4 * n + c₂.nmem (A + 12 * n + 4 * k + 2 + j))
        (by clear * - h1 hA oR; omega)]
      exact hA1.vp _ h1)
    (fun i hi hb' => by
      rw [hyH] at hb'
      have hf : 0 < c₂.nmem (Y + 3 * n + i) := by
        rw [N21 _ (by clear * - hi; omega), BCv i hi]; exact (bf_pos).2 hb'
      exact SP i hi hf)
    (fun j hj => by
      rw [hyH] at hj
      exact FXo j hj)
  rw [hyH] at hrec
  have hz : c₃.nreg 8510 = 6 * cnt F n + cnt FY n + 3 := u10
  have ht : t₁ + (t₂ + t₃) ≤ 400 * n + 21 * k + 310 := by clear * - ht₁ ht₂ ht₃; omega
  have q3 : ∀ x, (x < 3013 ∨ (8000 ≤ x ∧ x ≠ 8510)) → c₃.nreg x = c₂.nreg x := rg3
  have Q : ∀ x, 8000 ≤ x → x ≠ 8510 → c₃.nreg x = c.nreg x := fun x h1 h2 => by
    rw [q3 x (Or.inr ⟨h1, h2⟩), q2 x (by omega), q1 x (by omega)]
  have MM : ∀ a, (a < A + n ∨ (A + 2 * n ≤ a ∧ a < A + 4 * n + k + 2) ∨
      (Y ≤ a ∧ a < Y + 3 * n) ∨ (Y + 8 * n ≤ a ∧ a < XX + 2) ∨ XX + 7 * n + 6 ≤ a) →
      c₃.nmem a = c.nmem a := fun a ha => by
    rcases ha with ha | ha | ha | ha | ha
    · rw [lo3 a (by clear * - ha oX1 hY; omega), N21 a (by clear * - ha hY; omega), lo1 a ha]
    · rw [lo3 a (by clear * - ha oX1 hY; omega), N21 a (by clear * - ha hY; omega),
        mid1 a ha.1 ha.2]
    · rw [lo3 a (by clear * - ha oX1; omega), N21 a (by clear * - ha; omega),
        Y1 a ha.1 ha.2]
    · rw [lo3 a ha.2, M2 a (by clear * - ha; omega),
        hi1 a (by clear * - ha hY; omega) (by clear * - ha; omega)]
    · rw [hi3 a ha, M2 a (by clear * - ha oX1; omega),
        hi1 a (by clear * - ha oX1 hY; omega) (by clear * - ha oX1; omega)]
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), ht, by rw [hz]; exact hrec, by rw [hz]; omega,
    h.congr hR3 u21 (fun x hx => Q x (by omega) (by omega)) (fun a ha => MM a (by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (by clear * - ha hA; omega)
      · exact Or.inr (Or.inl ⟨by clear * - ha; omega, by clear * - ha; omega⟩)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by clear * - ha oX2; omega)))))),
    MM, fun x hx => ?_, by rw [rr3, rr2, rr1], by rw [rm3, rm2, rm1], by rw [o3, o2, o1]⟩
  rcases hx with hx | hx
  · rw [q3 x (Or.inl hx), q2 x (by omega), q1 x (Or.inl hx)]
  · exact Q x hx.1 hx.2

end Exec

end MfDrv

end BKMNW

end PlanarFlow
