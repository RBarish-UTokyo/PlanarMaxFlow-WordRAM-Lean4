module

public import PlanarFlow.BKMNW.NrPchD

/-!
# `pchP`, phase E: Kahn's order and the visits

* `nr_rcnt_eq_card`, `kahn_all`, **`kahn_len`** (the length of Kahn's queue is the number of
  vertex labels `rcnt VL m`, computed in phase C);
* **`pchE = pG15 ; kahnP ; pG16a ; pG16b ; pushP`**, **`pchE_exec`**: Kahn's queue `Q` of the
  (acyclic) flow `g` of the flow array (`KSt`), then the visits of `pushP` along it: the flow array
  becomes `Z + nrGt Mp ed m β Fr g Q t`; within `186 m + 100` steps; memory changed only in `FL`,
  `DV` (`[A + 4m, A + 5m)`) and the scratch `[A + 19m, A + 27m + 1)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab MfDrv NegSSSP

lemma nr_rcnt_eq_card (X : ℕ → ℕ) : ∀ n, (∀ j < n, X j ≤ j) →
    rcnt X n = ((range n).filter fun j => X j = j).card
  | 0, _ => by simp [rcnt]
  | n + 1, h => by
    rw [rcnt_succ, nr_rcnt_eq_card X n fun j hj => h j (by omega), range_add_one, filter_insert]
    have hn := h n (by omega)
    by_cases e : X n = n
    · rw [iteT e, card_insert_of_notMem (by simp)]; omega
    · rw [iteF e]; omega

section Kahn

variable {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
  [Fintype F'] [DecidableEq F']

/-- **Kahn's queue holds every vertex label** (acyclic flow). -/
lemma kahn_all {Mp : CombMap D' V' F'} {m : ℕ} {ed : ℕ → D'} {rv vl : ℕ → ℕ}
    (hI : IxMap Mp m ed rv vl) {g₁ : D' → ℤ} (hac : ∀ v, ¬ Relation.TransGen (Pos Mp g₁) v v)
    {ps : ℕ → ℕ} (hps : ∀ j < m, ps j ≠ 0 ↔ 0 < g₁ (ed j)) {Q IND : ℕ → ℕ} {t : ℕ}
    (hk : KSt m vl vl (fun j => vl (rv j)) ps Q IND t t) : ∀ w, KRep m vl w → w ∈ kQ Q t := by
  have hvt : ∀ j < m, Mp.tail (ed (vl j)) = Mp.tail (ed j) := fun j hj =>
    (hI.vl_iff _ (hI.vlt j hj).1 j hj).2 (hI.vlt j hj).2.1
  have hvh : ∀ j < m, Mp.tail (ed (vl (rv j))) = Mp.head (ed j) := fun j hj => by
    rw [hvt _ (hI.rv j hj).1, (hI.rv j hj).2]; rfl
  exact kst_final hk (fun w => rk Mp g₁ (Mp.tail (ed w)))
    (fun j hj hp => by
      show rk Mp g₁ (Mp.tail (ed (vl j))) < rk Mp g₁ (Mp.tail (ed (vl (rv j))))
      rw [hvt j hj, hvh j hj]
      exact rk_lt hac ((hps j hj).1 hp))
    (fun j hj => ⟨(hI.vlt j hj).1, (hI.vlt j hj).2.1⟩)

/-- **The length of Kahn's queue is the number of vertex labels.** -/
lemma kahn_len {Mp : CombMap D' V' F'} {m : ℕ} {ed : ℕ → D'} {rv vl : ℕ → ℕ}
    (hI : IxMap Mp m ed rv vl) {g₁ : D' → ℤ} (hac : ∀ v, ¬ Relation.TransGen (Pos Mp g₁) v v)
    {ps : ℕ → ℕ} (hps : ∀ j < m, ps j ≠ 0 ↔ 0 < g₁ (ed j)) {Q IND : ℕ → ℕ} {t : ℕ}
    (hk : KSt m vl vl (fun j => vl (rv j)) ps Q IND t t) : t = rcnt vl m := by
  classical
  have hall := kahn_all hI hac hps hk
  rw [nr_rcnt_eq_card vl m fun j hj => (hI.vlt j hj).2.2]
  have e : (kQ Q t).toFinset = (range m).filter fun j => vl j = j := by
    ext w
    simp only [List.mem_toFinset, mem_filter, mem_range]
    constructor
    · intro hw
      simp only [kQ, List.mem_map, List.mem_range] at hw
      obtain ⟨k, hk', rfl⟩ := hw
      exact hk.rep k hk'
    · intro hw; exact hall w hw
  rw [← e, List.toFinset_card_of_nodup hk.nd]
  simp [kQ]

end Kahn

/-- **Phase E of `pchP`**: Kahn's order and the visits. -/
def pchE : Stmt := .seq pG15 (.seq kahnP (.seq pG16a (.seq pG16b pushP)))

section Exec

variable {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
  [Fintype F'] [DecidableEq F']

variable {P : Input} {W : ℕ}

/-- **Phase E of `pchP`** (see the module docstring). -/
theorem pchE_exec {Mp : CombMap D' V' F'} {m : ℕ} {ed : ℕ → D'} (c : Config)
    (hc : WordsBounded W c) {d A BT FR Kd Z : ℕ} (R : PchR c d A BT FR Kd m Z) (hm : 0 < m)
    (hI : IxMap Mp m ed (fun i => c.nmem (d + 4 + m + i)) (fun i => c.nmem (A + 3 * m + i)))
    (r27 : c.nreg 9227 = rcnt (fun j => c.nmem (A + 3 * m + j)) m)
    {g : D' → ℤ} (hg : Mp.IsAntisymm g) (hac : ∀ v, ¬ Relation.TransGen (Pos Mp g) v v)
    (hZ : ZBnd Z g) (hG : GRep c.nmem (d + 4 + 6 * m) Z m ed g)
    {β : V' → ℤ} {Fr : Finset V'}
    (hD : DRep Mp c.nmem (A + 4 * m) Kd m ed (fun i => c.nmem (A + 3 * m + i)) g)
    (hBT : ∀ v < m, c.nmem (A + 3 * m + v) = v → (c.nmem (BT + v) : ℤ) = Kd + β (Mp.tail (ed v)))
    (hFR : ∀ v < m, c.nmem (A + 3 * m + v) = v → (c.nmem (FR + v) = 0 ↔ Mp.tail (ed v) ∉ Fr))
    (hO : ∀ y < m, c.nmem (A + 13 * m + y) = c.nmem (A + 12 * m + y) +
          (nrF (fun i => c.nmem (A + 3 * m + i)) (fun _ => 1) m y).length ∧
        c.nmem (A + 13 * m + y) ≤ m ∧
        ∀ t (ht : t < (nrF (fun i => c.nmem (A + 3 * m + i)) (fun _ => 1) m y).length),
          c.nmem (A + 14 * m + (c.nmem (A + 12 * m + y) + t)) =
            (nrF (fun i => c.nmem (A + 3 * m + i)) (fun _ => 1) m y)[t])
    (hKd : (m + 1) * (Z : ℤ) ≤ Kd) (wKd : Kd + (m + 1) * (Z : ℤ) ≤ W) (wZ : 2 * Z ≤ W)
    (sBT : BT + m ≤ d + 4 + 6 * m ∨ d + 4 + 7 * m ≤ BT) (tBT : BT + m ≤ A ∨ A + 30 * m + 1 ≤ BT)
    (sFR : FR + m ≤ d + 4 + 6 * m ∨ d + 4 + 7 * m ≤ FR) (tFR : FR + m ≤ A ∨ A + 30 * m + 1 ≤ FR)
    (wBT : BT + m ≤ W) (wFR : FR + m ≤ W)
    (hA : d + 4 + 7 * m ≤ A) (w : A + 30 * m + 10 ≤ W) :
    ∃ c' t, Exec P W pchE c c' t ∧ t ≤ 186 * m + 100 ∧
      (∃ (Q IND ps : ℕ → ℕ) (t' : ℕ),
        KSt m (fun i => c.nmem (A + 3 * m + i)) (fun i => c.nmem (A + 3 * m + i))
          (fun j => c.nmem (A + 3 * m + c.nmem (d + 4 + m + j))) ps Q IND t' t' ∧
        (∀ j < m, ps j ≠ 0 ↔ 0 < g (ed j)) ∧
        GRep c'.nmem (d + 4 + 6 * m) Z m ed (nrGt Mp ed m β Fr g Q t')) ∧
      (∀ a, (a < d + 4 + 6 * m ∨ d + 4 + 7 * m ≤ a) → (a < A + 4 * m ∨ A + 5 * m ≤ a) →
        (a < A + 19 * m ∨ A + 27 * m + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set VL : ℕ → ℕ := fun i => c.nmem (A + 3 * m + i) with hVL
  set RV : ℕ → ℕ := fun i => c.nmem (d + 4 + m + i) with hRV
  -- `pG15 ; kahnP`
  obtain ⟨c₁, t₁, e₁, ht₁, a00, a01, a02, a03, a04, a05, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    pG15_exec (P := P) c hc
  have R₁ := R.congr (fun x h1 h2 => f₁ x (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)
    (by clear * - h1 h2; omega) (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)
    (by clear * - h1 h2; omega))
    (f₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  rw [R.r04] at a00; rw [R.r10] at a01; rw [R.r06] at a02; rw [R.r08] at a03; rw [R.r05] at a04
  rw [R.r25] at a05
  obtain ⟨c₂, t₂, e₂, ht₂, pos₂, t', hk, k₂, f₂, rr₂, rm₂, o₂⟩ := kahnP_exec (P := P) c₁
    e₁.wb_right a00 a01 a02 a03 a04 a05 hm
    (fun j hj => by rw [m₁]; exact (hI.rv j hj).1)
    (fun j hj => by rw [m₁]; exact (hI.vlt j hj))
    (Or.inl (by clear * - hA; omega)) (Or.inl (by clear * - hA; omega))
    (Or.inl (by clear * - hA; omega)) (by clear * - w hA; omega) (by clear * - w hA; omega)
    (by clear * - w hA hA; omega) (by clear * - w hA hA; omega)
  rw [m₁] at hk pos₂
  have R₂ := R₁.congr (fun x h1 h2 => f₂ x (by clear * - h1 h2; omega)) (f₂ _ (by decide))
  have hps : ∀ j < m, c₂.nmem (A + 19 * m + j) ≠ 0 ↔ 0 < g (ed j) := fun j hj => by
    rw [pos₂ j hj]; unfold kps
    have := hG j hj
    split_ifs with h <;> simp <;> omega
  have hlen : t' = rcnt VL m := kahn_len hI hac hps hk
  have mem₂ : ∀ a, (a < A + 19 * m ∨ A + 27 * m + 1 ≤ a) → c₂.nmem a = c.nmem a := fun a ha => by
    rw [k₂ a (by clear * - ha; omega), m₁]
  -- `pG16a ; pG16b ; pushP`
  obtain ⟨c₃, t₃, e₃, ht₃, b51, b52, b53, b54, b55, b56, b57, b58, f₃, m₃, rr₃, rm₃, o₃⟩ :=
    pG16a_exec (P := P) c₂ e₂.wb_right (by rw [R₂.r25, R₂.r04]; clear * - w hA; omega)
      (by rw [R₂.r25, R₂.r04]; clear * - w hA; omega)
  have R₃ := R₂.congr (fun x h1 h2 => f₃ x (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)
    (by clear * - h1 h2; omega) (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)
    (by clear * - h1 h2; omega) (by clear * - h1 h2; omega) (by clear * - h1 h2; omega))
    (f₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide))
  rw [R₂.r08] at b51; rw [R₂.r06] at b52; rw [R₂.r10] at b53; rw [R₂.r05] at b54
  rw [R₂.r11] at b55; rw [R₂.r01] at b56; rw [R₂.r02] at b57; rw [R₂.r25, R₂.r04] at b58
  obtain ⟨c₄, t₄, e₄, ht₄, g59, g60, g61, g62, f₄, m₄, rr₄, rm₄, o₄⟩ :=
    pG16b_exec (P := P) c₃ e₃.wb_right
  have R₄ := R₃.congr (fun x h1 h2 => f₄ x (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)
    (by clear * - h1 h2; omega) (by clear * - h1 h2; omega))
    (f₄ _ (by decide) (by decide) (by decide) (by decide))
  have r27' : c₃.nreg 9227 = rcnt VL m := by
    rw [f₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), f₂ _ (by decide), f₁ _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), r27]
  rw [r27', ← hlen] at g59; rw [R₃.r19] at g60; rw [R₃.r20] at g61; rw [R₃.r21] at g62
  have q4 : ∀ x, 9151 ≤ x → x ≤ 9158 → c₄.nreg x = c₃.nreg x := fun x h1 h2 =>
    f₄ x (by clear * - h2; omega) (by clear * - h2; omega) (by clear * - h2; omega)
      (by clear * - h2; omega)
  have mem₄ : c₄.nmem = c₂.nmem := by rw [m₄, m₃]
  have hQ : ∀ k < t', c₄.nmem (A + 19 * m + 2 * m + k) < m ∧
      c₄.nmem (A + 3 * m + c₄.nmem (A + 19 * m + 2 * m + k)) =
        c₄.nmem (A + 19 * m + 2 * m + k) := fun k hk' => by
    obtain ⟨h1, h2⟩ := hk.rep k hk'
    rw [mem₄]
    refine ⟨h1, ?_⟩
    rw [mem₂ (A + 3 * m + c₂.nmem (A + 19 * m + 2 * m + k)) (by clear * - h1; omega)]
    exact h2
  have nv_le : t' ≤ m := by
    rw [hlen]; exact rcnt_le _ _
  have vlm : ∀ i < m, c₄.nmem (A + 3 * m + i) = VL i := fun i hi => by
    rw [mem₄, mem₂ _ (by clear * - hi; omega)]
  have rvm : ∀ i < m, c₄.nmem (d + 4 + m + i) = RV i := fun i hi => by
    rw [mem₄, mem₂ _ (by clear * - hi hA; omega)]
  obtain ⟨c₅, t₅, e₅, ht₅, G₅, -, -, -, k₅, f₅, rr₅, rm₅, o₅⟩ := pushP_exec (P := P) c₄
    e₄.wb_right (M := Mp) (m := m) (ed := ed) (Kd := Kd) (g := g) (β := β) (Fr := Fr)
    (G := d + 4 + 6 * m) (RV := d + 4 + m) (VL := A + 3 * m) (Zn := Z) (DV := A + 4 * m)
    (BT := BT) (FR := FR) (Q := A + 19 * m + 2 * m) (nv := t') (OB := A + 12 * m)
    (OE := A + 13 * m) (OL := A + 14 * m)
    (IxMap.congr hI (fun i hi => rvm i hi) (fun i hi => vlm i hi))
    (by rw [q4 _ (by decide) (by decide)]; exact b51)
    (by rw [q4 _ (by decide) (by decide)]; exact b52)
    (by rw [q4 _ (by decide) (by decide)]; exact b53)
    (by rw [q4 _ (by decide) (by decide)]; exact b54)
    (by rw [q4 _ (by decide) (by decide)]; exact b55)
    (by rw [q4 _ (by decide) (by decide)]; exact b56)
    (by rw [q4 _ (by decide) (by decide)]; exact b57)
    (by rw [q4 _ (by decide) (by decide), b58]; clear * -; omega) g59 g60 g61 g62
    (fun v hv => by
      rw [nrF_congr (T := VL) (K := fun _ => 1) (fun i hi => vlm i hi) (fun _ _ => rfl)]
      obtain ⟨u1, u2, u3⟩ := hO v hv
      refine ⟨(by rw [mem₄, mem₂ _ (by clear * - hv; omega), mem₂ _ (by clear * - hv; omega)];
                  exact u1), (by rw [mem₄, mem₂ _ (by clear * - hv; omega)]; exact u2),
        fun t ht => ?_⟩
      have hle : c.nmem (A + 12 * m + v) + t < m := by
        have := u2; rw [u1] at this; clear * - this ht; omega
      rw [mem₄, mem₂ (A + 12 * m + v) (by clear * - hv; omega),
        mem₂ _ (by clear * - hle; omega)]
      exact u3 t ht)
    (by
      have : kQ (fun k => c₄.nmem (A + 19 * m + 2 * m + k)) t' =
          kQ (fun k => c₂.nmem (A + 19 * m + 2 * m + k)) t' := by rw [mem₄]
      rw [this]; exact hk.nd)
    hQ
    (fun v hv hvv => by
      rw [mem₄, mem₂ _ (by clear * - tFR hv; omega)]
      exact hFR v hv (by have := vlm v hv; rw [hvv] at this; exact this.symm))
    (fun v hv hvv => by
      rw [mem₄, mem₂ _ (by clear * - tBT hv; omega)]
      exact hBT v hv (by have := vlm v hv; rw [hvv] at this; exact this.symm))
    (fun i hi => by rw [mem₄, mem₂ _ (by clear * - hi hA; omega)]; exact hG i hi)
    (fun v hv hvv => by
      rw [mem₄, mem₂ _ (by clear * - hv; omega)]
      exact hD v hv (by
        have := vlm v hv; have h' : c₄.nmem (A + 3 * m + v) = v := hvv
        rw [h'] at this; exact this.symm))
    hg hZ hKd wKd wZ
    (Or.inl (by clear * - hA; omega)) (Or.inr (by clear * -; omega))
    (Or.inl (by clear * - hA; omega)) (Or.inl (by clear * - hA; omega))
    (Or.inr (by clear * - hA; omega)) (Or.inr (by clear * -; omega)) (Or.inl (by clear * -; omega))
    (Or.inl (by clear * - hA; omega)) (Or.inl (by clear * -; omega))
    (Or.inl (by clear * - hA; omega)) (Or.inl (by clear * -; omega))
    (Or.inl (by clear * - hA; omega)) (Or.inl (by clear * - nv_le; omega))
    (by clear * - sFR; unfold NrSep; omega) (by clear * - tFR; unfold NrSep; omega)
    (by clear * - sBT; unfold NrSep; omega) (by clear * - tBT; unfold NrSep; omega)
    (by clear * - w hA hA; omega) (by clear * - w hA; omega) (by clear * - w hA hA; omega)
    (by clear * - w hA; omega) (by clear * - w hA; omega) (by clear * - w hA; omega)
    (by clear * - w hA; omega) (by clear * - w hA nv_le; omega) wFR wBT (by clear * - w hA; omega)
  refine ⟨c₅, t₁ + (t₂ + (t₃ + (t₄ + t₅))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))),
    by clear * - ht₁ ht₂ ht₃ ht₄ ht₅ nv_le; unfold kahnCost at ht₂; omega,
    ⟨fun k => c₂.nmem (A + 19 * m + 2 * m + k), fun w => c₂.nmem (A + 19 * m + m + w),
      fun i => c₂.nmem (A + 19 * m + i), t', hk, hps, ?_⟩, fun a h1 h2 h3 => ?_,
    by rw [rr₅, rr₄, rr₃, rr₂, rr₁], by rw [rm₅, rm₄, rm₃, rm₂, rm₁],
    by rw [o₅, o₄, o₃, o₂, o₁]⟩
  · have : (fun k => c₄.nmem (A + 19 * m + 2 * m + k)) =
        fun k => c₂.nmem (A + 19 * m + 2 * m + k) := by rw [mem₄]
    rw [this] at G₅; exact G₅
  · rw [k₅ a (by clear * - h1; omega) (by clear * - h2; omega), mem₄, mem₂ a h3]

end Exec

end BKMNW

end PlanarFlow
