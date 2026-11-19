module

public import PlanarFlow.Monge.PrepScan

/-!
# Building the tables: the data of a level

For the level `sz` and a target `t` (its half block `hbT b sz t = (r0, nr, c1, nc)`, the pattern
`F = Fb X r0 c1` of the half block, the row `ρ = t - r0`):

* `Lv b X sz t = lcol nc F ρ`: the first column of the row with an arc (pass 1 of `prepO`);
  `Gv b X sz t`: whether the row has an arc (`1`) or not (`0`);
* `Rv b X sz t = r0 + repR nr nc F ρ`: the target standing for `t` (pass 2).

`hbT_eq`: the targets of a half block share it; `lcol_of_scan`, `repR_of_scan_found`,
`repR_of_scan_none`: the results of the scans are `lcol` and `repR`; `tVal_hbT`, `tMul_hbT`: the
table entries of a pair of the half block in terms of these data.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

attribute [local instance] Classical.propDecidable

/-- The first column with an arc of the row of `t` in its half block at the level `sz`. -/
noncomputable def Lv (b : ℕ) (X : ℕ → ℕ → Prop) (sz t : ℕ) : ℕ :=
  lcol (hbT b sz t).2.2.2 (Fb X (hbT b sz t).1 (hbT b sz t).2.2.1) (t - (hbT b sz t).1)

/-- Whether the row of `t` has an arc in its half block at the level `sz`. -/
noncomputable def Gv (b : ℕ) (X : ℕ → ℕ → Prop) (sz t : ℕ) : ℕ :=
  if Lv b X sz t < (hbT b sz t).2.2.2 then 1 else 0

/-- The target standing for `t` in its half block at the level `sz`. -/
noncomputable def Rv (b : ℕ) (X : ℕ → ℕ → Prop) (sz t : ℕ) : ℕ :=
  (hbT b sz t).1 + repR (hbT b sz t).2.1 (hbT b sz t).2.2.2
    (Fb X (hbT b sz t).1 (hbT b sz t).2.2.1) (t - (hbT b sz t).1)

variable {b : ℕ} {X : ℕ → ℕ → Prop} {sz t : ℕ}

/-- The half block of a target holds it, its sources are separated from its targets. -/
lemma hbT_mem (hsz : 0 < sz) (ht : t < b) (hnc : 0 < (hbT b sz t).2.2.2) :
    (hbT b sz t).1 ≤ t ∧ t < (hbT b sz t).1 + (hbT b sz t).2.1 ∧
      (hbT b sz t).1 + (hbT b sz t).2.1 ≤ b ∧ (hbT b sz t).2.2.2 ≤ (hbT b sz t).2.2.1 ∧
      (hbT b sz t).2.2.1 ≤ b ∧ (hbT b sz t).2.1 ≤ sz ∧ (hbT b sz t).2.2.2 ≤ sz ∧
      ((hbT b sz t).1 + (hbT b sz t).2.1 ≤ (hbT b sz t).2.2.1 - (hbT b sz t).2.2.2 ∨
        (hbT b sz t).2.2.1 ≤ (hbT b sz t).1) := by
  obtain ⟨h1, h2, -⟩ := blk_of (t := t) hsz
  have hm := min_le_left (t / (sz + sz) * (sz + sz) + sz + sz) b
  have hm' := min_le_right (t / (sz + sz) * (sz + sz) + sz + sz) b
  unfold hbT at hnc ⊢
  split_ifs at hnc ⊢ with h
  · simp only at hnc ⊢; omega
  · simp only at hnc ⊢; omega

/-- **The targets of a half block share it.** -/
lemma hbT_eq (hsz : 0 < sz) (_ht : t < b) {t' : ℕ} (h1 : (hbT b sz t).1 ≤ t')
    (h2 : t' < (hbT b sz t).1 + (hbT b sz t).2.1) : hbT b sz t' = hbT b sz t := by
  obtain ⟨a1, a2, -⟩ := blk_of (t := t) hsz
  obtain ⟨b1, b2, b3⟩ := blk_of (t := t') hsz
  have hm := min_le_left (t / (sz + sz) * (sz + sz) + sz + sz) b
  have hq : t' / (sz + sz) = t / (sz + sz) := by
    refine div_of_mem (by omega) ?_ ?_
    · unfold hbT at h1; split_ifs at h1 <;> simp only at h1 <;> rw [Nat.mul_comm] <;> omega
    · unfold hbT at h1 h2; split_ifs at h1 h2 <;> simp only at h1 h2 <;> rw [Nat.mul_comm] <;>
        omega
  have key : (t' < t / (sz + sz) * (sz + sz) + sz) ↔ (t < t / (sz + sz) * (sz + sz) + sz) := by
    unfold hbT at h1 h2; split_ifs at h1 h2 with h <;> simp only at h1 h2 <;> omega
  unfold hbT
  rw [hq]
  by_cases h : t < t / (sz + sz) * (sz + sz) + sz
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true (key.2 h))]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h),
      ite_eq_right_of_eq_false _ _ (eq_false (fun h' => h (key.1 h')))]

/-- **The first column found by a scan is `lcol`.** -/
lemma lcol_of_scan {n : ℕ} {F : ℕ → ℕ → Prop} {ρ L : ℕ}
    (h : (L < n ∧ F ρ L ∧ ∀ j < L, ¬ F ρ j) ∨ (L = n ∧ ∀ j < n, ¬ F ρ j)) : lcol n F ρ = L := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · obtain ⟨l1, l2, l3⟩ := lcol_spec (F := F) ⟨L, h1, h2⟩
    rcases Nat.lt_trichotomy (lcol n F ρ) L with h | h | h
    · exact absurd l2 (h3 _ h)
    · exact h
    · exact absurd h2 (l3 _ h)
  · rw [h1]; exact lcol_none fun ⟨κ, hκ, hF⟩ => h2 κ hκ hF

/-- The standing row when a genuine row lies at or above: the nearest one, found by the downward
scan. -/
lemma repR_of_scan_found {m n : ℕ} {F : ℕ → ℕ → Prop} {ρ j : ℕ} (hj : j ≤ ρ)
    (h1 : GRow m n F (ρ - j)) (h2 : ∀ j' < j, ¬ GRow m n F (ρ - j')) :
    repR m n F ρ = ρ - j := by
  have hex : ∃ u ≤ ρ, GRow m n F u := ⟨ρ - j, by omega, h1⟩
  rw [repR_of_le hex, Nat.findGreatest_eq_iff]
  refine ⟨by omega, fun _ => h1, fun k hk hk' hg => h2 (ρ - k) (by omega) ?_⟩
  rw [show ρ - (ρ - k) = k by omega]; exact hg

/-- The standing row when no genuine row lies at or above: the first genuine row (found by the
upward scan), or the row itself. -/
lemma repR_of_scan_none {m n : ℕ} {F : ℕ → ℕ → Prop} {ρ u : ℕ}
    (hno : ∀ j < ρ + 1, ¬ GRow m n F (ρ - j))
    (hu : (u < m ∧ GRow m n F u ∧ ∀ u' < u, ¬ GRow m n F u') ∨
      (u = m ∧ ∀ u' < m, ¬ GRow m n F u')) :
    repR m n F ρ = if u < m then u else ρ := by
  classical
  have hle : ¬ ∃ u ≤ ρ, GRow m n F u := fun ⟨u', hu', hg⟩ =>
    hno (ρ - u') (by omega) (by rw [show ρ - (ρ - u') = u' by omega]; exact hg)
  rcases hu with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · have hex : ∃ u, GRow m n F u := ⟨u, h2⟩
    rw [repR_of_not_le hle hex, ite_eq_left_of_eq_true _ _ (eq_true h1), Nat.find_eq_iff]
    exact ⟨h2, fun u' hu' => h3 u' hu'⟩
  · have hex : ¬ ∃ u, GRow m n F u := fun ⟨u', hg⟩ => h2 u' hg.1 hg
    rw [repR_none hex, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-- The flag of a target of the half block of `t`: whether its row is genuine. -/
lemma Gv_eq (hsz : 0 < sz) (ht : t < b) {u : ℕ} (hu : u < (hbT b sz t).2.1) :
    Gv b X sz ((hbT b sz t).1 + u) = if GRow (hbT b sz t).2.1 (hbT b sz t).2.2.2
      (Fb X (hbT b sz t).1 (hbT b sz t).2.2.1) u then 1 else 0 := by
  have he := hbT_eq hsz ht (t' := (hbT b sz t).1 + u) (by omega) (by omega)
  unfold Gv Lv
  rw [he, show (hbT b sz t).1 + u - (hbT b sz t).1 = u by omega]
  by_cases hg : GRow (hbT b sz t).2.1 (hbT b sz t).2.2.2 (Fb X (hbT b sz t).1 (hbT b sz t).2.2.1) u
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hg),
      ite_eq_left_of_eq_true _ _ (eq_true (lcol_spec hg.2).1)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hg), ite_eq_right_of_eq_false _ _ (eq_false ?_)]
    intro hl
    exact hg ⟨hu, _, hl, (lcol_spec (by
      by_contra hc; rw [lcol_none hc] at hl; omega)).2.1⟩

/-- The standing target lies in the half block. -/
lemma Rv_mem (hsz : 0 < sz) (ht : t < b) (hnc : 0 < (hbT b sz t).2.2.2) :
    (hbT b sz t).1 ≤ Rv b X sz t ∧ Rv b X sz t < (hbT b sz t).1 + (hbT b sz t).2.1 := by
  have hm := hbT_mem (b := b) hsz ht hnc
  unfold Rv
  by_cases hex : ∃ u, GRow (hbT b sz t).2.1 (hbT b sz t).2.2.2
      (Fb X (hbT b sz t).1 (hbT b sz t).2.2.1) u
  · have := ((repR_spec hex (t - (hbT b sz t).1)).1).1
    omega
  · rw [repR_none hex]; omega

/-- **The constant entry of a pair of the half block of `t`**, from the level data. -/
lemma tVal_hbT {D : ℕ → ℕ → ℤ} {H : ℝ} {T κ : ℕ} (hT : sz = 2 ^ T) (ht : t < b)
    (hκ : κ < (hbT b sz t).2.2.2) :
    tVal b X D H ((hbT b sz t).2.2.1 - 1 - κ) t =
      if X ((hbT b sz t).2.2.1 - 1 - κ) (Rv b X sz t) then
        (D ((hbT b sz t).2.2.1 - 1 - κ) (Rv b X sz t) : ℝ)
      else H + (if κ < Lv b X sz (Rv b X sz t) then -(κ : ℝ) else κ) := by
  have hsz : 0 < sz := by rw [hT]; exact Nat.two_pow_pos T
  have hm := hbT_mem (b := b) hsz ht (by omega)
  obtain ⟨he, -, -, -⟩ := hbOf_eq_hbT (b := b) hT ht hκ
  obtain ⟨r1, r2⟩ := Rv_mem (X := X) hsz ht (by omega)
  have hR := hbT_eq hsz ht r1 r2
  unfold tVal subVal
  rw [he]
  have e1 : (hbT b sz t).2.2.1 - 1 - ((hbT b sz t).2.2.1 - 1 - κ) = κ := by omega
  rw [e1]
  have hL : lcol (hbT b sz t).2.2.2 (Fb X (hbT b sz t).1 (hbT b sz t).2.2.1)
      (repR (hbT b sz t).2.1 (hbT b sz t).2.2.2 (Fb X (hbT b sz t).1 (hbT b sz t).2.2.1)
        (t - (hbT b sz t).1)) = Lv b X sz (Rv b X sz t) := by
    unfold Lv
    rw [hR, show Rv b X sz t - (hbT b sz t).1 = repR (hbT b sz t).2.1 (hbT b sz t).2.2.2
      (Fb X (hbT b sz t).1 (hbT b sz t).2.2.1) (t - (hbT b sz t).1) by unfold Rv; omega]
  unfold wt
  rw [hL]
  rfl

/-- **The multiplier entry of a pair of the half block of `t`**, from the level data. -/
lemma tMul_hbT {T κ : ℕ} (hT : sz = 2 ^ T) (ht : t < b) (hκ : κ < (hbT b sz t).2.2.2) :
    tMul b X ((hbT b sz t).2.2.1 - 1 - κ) t =
      if X ((hbT b sz t).2.2.1 - 1 - κ) (Rv b X sz t) then 1 else 0 := by
  have hsz : 0 < sz := by rw [hT]; exact Nat.two_pow_pos T
  have hm := hbT_mem (b := b) hsz ht (by omega)
  obtain ⟨he, -, -, -⟩ := hbOf_eq_hbT (b := b) hT ht hκ
  unfold tMul subMul
  rw [he]
  have e1 : (hbT b sz t).2.2.1 - 1 - ((hbT b sz t).2.2.1 - 1 - κ) = κ := by omega
  rw [e1]
  rfl

end Monge

end PlanarFlow
