module

public import PlanarFlow.Monge.Basic
public import Mathlib.Tactic.Ring

/-!
# Row minima of Monge matrices with missing entries

A matrix with entries in `ℝ ∪ {+∞}` is *Monge in the extended sense* when
`A ρ κ + A ρ' κ' ≤ A ρ κ' + A ρ' κ` holds in `ℝ ∪ {+∞}` for `ρ < ρ'`, `κ < κ'`: whenever the
anti-diagonal `A ρ κ'`, `A ρ' κ` is finite, so is the diagonal, and the inequality holds
(`ExtClosed`, for the finite pattern `F` and the finite values `a`). This is the form the block
matrices of a dense distance graph with missing arcs take (`PlanarFlow.Monge.CrossingO`).

Such a matrix is in general **not** totally monotone once `+∞` is replaced by a finite number,
whatever the number, and no single finite completion can be Monge. This file gives a
replacement that is **totally monotone for every value of the columns' shifts** (the values `e`
of the sources), so that the row-minima program `PlanarFlow.Monge.smawk` applies unchanged:

* `lcol n F ρ`: the leftmost finite column of the row `ρ` (`n` if there is none);
  `wt n F ρ κ`: `-κ` left of it, `κ` from it on.
* In a *genuine* row (`GRow`: one with a finite entry), a missing entry `(ρ, κ)` is replaced by
  `Hs + wt n F ρ κ`, `Hs` a bound above every finite entry plus `n`: the missing entries left of
  the first finite one decrease, the others increase (`subA`). On the genuine rows this matrix is
  totally monotone (`subA_totMono`): the extended Monge property excludes every pattern of four
  entries that would contradict it (`lcol_gt_of_up`, `le_lcol_of_down`, `lcol_gt_of_left`).
* A row without a finite entry cannot be completed statically: whether it should prefer a column
  depends on the shifts `e`. It is replaced by a copy of a genuine row (`repR`: the nearest
  genuine row above, the first genuine row if there is none above; the rows are kept when there
  is no genuine row at all). `repR` is nondecreasing (`repR_mono`), so the copied matrix `extA`
  is **totally monotone** (`extA_totMono`). Its entries are `subMul ρ κ · e κ + subVal ρ κ`:
  `subMul ∈ {0, 1}` and `subVal` depend on the pattern and the raw values only, not on `e`.
* `extA_lmin`: in a genuine row the leftmost minimum of `extA` is a finite entry, at most every
  finite entry of the row: the row minimum over the finite entries. A row without a finite entry
  has nothing to relax.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

section Ext

attribute [local instance] Classical.propDecidable

variable {m n : ℕ} {F : ℕ → ℕ → Prop}

/-- **Monge in the extended sense** (missing entries read as `+∞`): an anti-diagonal of finite
entries forces a finite diagonal, and the Monge inequality. -/
def ExtClosed (m n : ℕ) (F : ℕ → ℕ → Prop) (a : ℕ → ℕ → ℝ) : Prop :=
  ∀ ρ ρ' κ κ', ρ < ρ' → ρ' < m → κ < κ' → κ' < n → F ρ κ' → F ρ' κ →
    F ρ κ ∧ F ρ' κ' ∧ a ρ κ + a ρ' κ' ≤ a ρ κ' + a ρ' κ

/-- A genuine row: one with a finite entry. -/
def GRow (m n : ℕ) (F : ℕ → ℕ → Prop) (ρ : ℕ) : Prop := ρ < m ∧ ∃ κ < n, F ρ κ

/-- The leftmost finite column of the row `ρ` (`n` if there is none). -/
noncomputable def lcol (n : ℕ) (F : ℕ → ℕ → Prop) (ρ : ℕ) : ℕ := by
  classical exact if h : ∃ κ, κ < n ∧ F ρ κ then Nat.find h else n

/-- The leftmost finite column is finite, and the first one. -/
lemma lcol_spec {ρ : ℕ} (h : ∃ κ < n, F ρ κ) :
    lcol n F ρ < n ∧ F ρ (lcol n F ρ) ∧ ∀ κ < lcol n F ρ, ¬ F ρ κ := by
  classical
  have h' : ∃ κ, κ < n ∧ F ρ κ := h
  have e : lcol n F ρ = Nat.find h' := by unfold lcol; rw [dite_eq_left_of_eq_true (eq_true h')]
  rw [e]
  exact ⟨(Nat.find_spec h').1, (Nat.find_spec h').2, fun κ hκ hF =>
    Nat.find_min h' hκ ⟨by have := (Nat.find_spec h').1; omega, hF⟩⟩

/-- Without a finite entry, `lcol` is `n`. -/
lemma lcol_none {ρ : ℕ} (h : ¬ ∃ κ < n, F ρ κ) : lcol n F ρ = n := by
  classical
  have h' : ¬ ∃ κ, κ < n ∧ F ρ κ := h
  unfold lcol; rw [dite_eq_right_of_eq_false (eq_false h')]

/-- The order of the missing entries of a row: decreasing left of the first finite entry,
increasing from it on. -/
noncomputable def wt (n : ℕ) (F : ℕ → ℕ → Prop) (ρ κ : ℕ) : ℝ :=
  if κ < lcol n F ρ then -(κ : ℝ) else κ

/-- `wt` decreases left of the first finite entry. -/
lemma wt_left {ρ κ κ' : ℕ} (h : κ < κ') (h' : κ' < lcol n F ρ) : wt n F ρ κ' < wt n F ρ κ := by
  unfold wt
  rw [ite_eq_left_of_eq_true _ _ (eq_true h'), ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
  have : (κ : ℝ) < κ' := by exact_mod_cast h
  linarith

/-- `wt` increases from the first finite entry on. -/
lemma wt_right {ρ κ κ' : ℕ} (h : κ < κ') (h' : lcol n F ρ ≤ κ) : wt n F ρ κ < wt n F ρ κ' := by
  unfold wt
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  exact_mod_cast h

/-- A non-increase of `wt` happens left of the first finite entry only. -/
lemma lt_lcol_of_wt_le {ρ κ κ' : ℕ} (h : κ < κ') (hw : wt n F ρ κ' ≤ wt n F ρ κ) :
    κ' < lcol n F ρ := by
  by_contra hc
  unfold wt at hw
  rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at hw
  have hκ : (κ : ℝ) < κ' := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ κ := Nat.cast_nonneg κ
  split_ifs at hw <;> linarith

/-- `|wt| < n`. -/
lemma wt_bound {ρ κ : ℕ} (h : κ < n) : -(n : ℝ) < wt n F ρ κ ∧ wt n F ρ κ < n := by
  have h1 : (κ : ℝ) < n := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ κ := Nat.cast_nonneg κ
  unfold wt
  split_ifs <;> constructor <;> linarith

/-- The completed matrix of the genuine rows: a missing entry is `Hs + wt`. -/
noncomputable def subA (n : ℕ) (F : ℕ → ℕ → Prop) (a : ℕ → ℕ → ℝ) (Hs : ℝ) (ρ κ : ℕ) : ℝ := by
  classical exact if F ρ κ then a ρ κ else Hs + wt n F ρ κ

/-- A finite entry of `subA`. -/
lemma subA_of {a : ℕ → ℕ → ℝ} {Hs : ℝ} {ρ κ : ℕ} (h : F ρ κ) : subA n F a Hs ρ κ = a ρ κ := by
  classical unfold subA; rw [ite_eq_left_of_eq_true _ _ (eq_true h)]

/-- A replaced entry of `subA`. -/
lemma subA_of_not {a : ℕ → ℕ → ℝ} {Hs : ℝ} {ρ κ : ℕ} (h : ¬ F ρ κ) :
    subA n F a Hs ρ κ = Hs + wt n F ρ κ := by
  classical unfold subA; rw [ite_eq_right_of_eq_false _ _ (eq_false h)]

variable {a : ℕ → ℕ → ℝ} {Hs : ℝ}

/-- A missing entry in the row `ρ'` at `κ'` below a finite entry at `κ'` of an upper row lies
left of the first finite entry of `ρ'`. -/
lemma lcol_gt_of_up (hc : ExtClosed m n F a) {ρ ρ' κ' : ℕ} (h1 : ρ < ρ') (h2 : ρ' < m)
    (hκ' : κ' < n) (hg : ∃ μ < n, F ρ' μ) (hup : F ρ κ') (hno : ¬ F ρ' κ') :
    κ' < lcol n F ρ' := by
  obtain ⟨hl, hF, -⟩ := lcol_spec hg
  by_contra hcon
  have hlt : lcol n F ρ' < κ' := by
    rcases Nat.lt_or_ge (lcol n F ρ') κ' with h | h
    · exact h
    · exact absurd (show lcol n F ρ' = κ' by omega ▸ hF) hno
  exact hno (hc ρ ρ' _ κ' h1 h2 hlt hκ' hup hF).2.1

/-- A missing entry in the row `ρ` at `κ` above a finite entry at `κ` of a lower row lies at or
right of the first finite entry of `ρ`. -/
lemma le_lcol_of_down (hc : ExtClosed m n F a) {ρ ρ' κ : ℕ} (h1 : ρ < ρ') (h2 : ρ' < m)
    (hg : ∃ μ < n, F ρ μ) (hdown : F ρ' κ) (hno : ¬ F ρ κ) : lcol n F ρ ≤ κ := by
  obtain ⟨hl, hF, -⟩ := lcol_spec hg
  by_contra hcon
  exact hno (hc ρ ρ' κ _ h1 h2 (by omega) hl hF hdown).1

/-- The first finite entry of a lower row is at or right of that of an upper row. -/
lemma lcol_le_of_lower (hc : ExtClosed m n F a) {ρ ρ' : ℕ} (h1 : ρ < ρ') (h2 : ρ' < m)
    (hg : ∃ μ < n, F ρ μ) (hg' : ∃ μ < n, F ρ' μ) : lcol n F ρ ≤ lcol n F ρ' := by
  obtain ⟨hl, hF, hmin⟩ := lcol_spec hg
  obtain ⟨hl', hF', -⟩ := lcol_spec hg'
  by_contra hcon
  exact hmin _ (by omega) (hc ρ ρ' _ _ h1 h2 (by omega) hl hF hF').1

/-- **The completed matrix is totally monotone on the genuine rows.** -/
theorem subA_totMono (hc : ExtClosed m n F a) (hB : ∀ ρ < m, ∀ κ < n, F ρ κ → a ρ κ + n < Hs)
    {ρ ρ' κ κ' : ℕ} (h1 : ρ < ρ') (h2 : ρ' < m) (h3 : κ < κ') (h4 : κ' < n)
    (hg : ∃ μ < n, F ρ μ) (hg' : ∃ μ < n, F ρ' μ) :
    (subA n F a Hs ρ κ' < subA n F a Hs ρ κ → subA n F a Hs ρ' κ' < subA n F a Hs ρ' κ) ∧
      (subA n F a Hs ρ κ' ≤ subA n F a Hs ρ κ → subA n F a Hs ρ' κ' ≤ subA n F a Hs ρ' κ) := by
  have hρ : ρ < m := by omega
  have hκ : κ < n := by omega
  -- a finite entry is below every completed one
  have below : ∀ r < m, ∀ x < n, ∀ y < n, F r x → ¬ F r y →
      subA n F a Hs r x < subA n F a Hs r y := fun r hr x hx y hy hFx hFy => by
    rw [subA_of hFx, subA_of_not hFy]
    have := hB r hr x hx hFx
    have := (wt_bound (F := F) (ρ := r) hy).1
    linarith
  by_cases hb : F ρ κ'
  · by_cases hcF : F ρ' κ
    · obtain ⟨ha, hd, hm⟩ := hc ρ ρ' κ κ' h1 h2 h3 h4 hb hcF
      rw [subA_of ha, subA_of hb, subA_of hcF, subA_of hd]
      constructor <;> intro <;> linarith
    · by_cases hd : F ρ' κ'
      · have := below ρ' h2 κ' h4 κ hκ hd hcF
        exact ⟨fun _ => this, fun _ => this.le⟩
      · have hl := lcol_gt_of_up hc h1 h2 h4 hg' hb hd
        have hw := wt_left (F := F) h3 hl
        rw [subA_of_not hd, subA_of_not hcF]
        exact ⟨fun _ => by linarith, fun _ => by linarith⟩
  · by_cases hcF : F ρ' κ
    · -- the premise fails
      have hpre : subA n F a Hs ρ κ < subA n F a Hs ρ κ' := by
        by_cases ha : F ρ κ
        · exact below ρ hρ κ hκ κ' h4 ha hb
        · have hl := le_lcol_of_down hc h1 h2 hg hcF ha
          rw [subA_of_not ha, subA_of_not hb]
          have := wt_right (F := F) h3 hl
          linarith
      exact ⟨fun h => absurd h (not_lt.2 hpre.le), fun h => absurd h (not_le.2 hpre)⟩
    · by_cases hd : F ρ' κ'
      · have := below ρ' h2 κ' h4 κ hκ hd hcF
        exact ⟨fun _ => this, fun _ => this.le⟩
      · -- both rows miss both entries in the lower row; the premise forces both left
        have key : subA n F a Hs ρ κ' ≤ subA n F a Hs ρ κ →
            subA n F a Hs ρ' κ' < subA n F a Hs ρ' κ := by
          intro hpre
          have ha : ¬ F ρ κ := fun ha => absurd hpre (not_le.2 (below ρ hρ κ hκ κ' h4 ha hb))
          rw [subA_of_not ha, subA_of_not hb] at hpre
          have hl := lt_lcol_of_wt_le (F := F) h3 (by linarith)
          have hll := lcol_le_of_lower hc h1 h2 hg hg'
          have hw := wt_left (F := F) (ρ := ρ') h3 (lt_of_lt_of_le hl hll)
          rw [subA_of_not hd, subA_of_not hcF]
          linarith
        exact ⟨fun h => key h.le, fun h => (key h).le⟩

/-! ### Rows without a finite entry -/

/-- The row standing for `ρ`: `ρ` if it is genuine, the nearest genuine row above, the first
genuine row if there is none above, `ρ` if there is no genuine row. -/
noncomputable def repR (m n : ℕ) (F : ℕ → ℕ → Prop) (ρ : ℕ) : ℕ := by
  classical exact
    if ∃ u ≤ ρ, GRow m n F u then Nat.findGreatest (GRow m n F) ρ
    else if h : ∃ u, GRow m n F u then Nat.find h else ρ

/-- `repR` when a genuine row lies at or above. -/
lemma repR_of_le {ρ : ℕ} (h : ∃ u ≤ ρ, GRow m n F u) :
    repR m n F ρ = Nat.findGreatest (GRow m n F) ρ := by
  classical unfold repR; rw [ite_eq_left_of_eq_true _ _ (eq_true h)]

/-- `repR` when no genuine row lies at or above. -/
lemma repR_of_not_le {ρ : ℕ} (h : ¬ ∃ u ≤ ρ, GRow m n F u) (hex : ∃ u, GRow m n F u) :
    repR m n F ρ = Nat.find hex := by
  classical
  unfold repR
  rw [ite_eq_right_of_eq_false _ _ (eq_false h), dite_eq_left_of_eq_true (eq_true hex)]

/-- `repR` without genuine rows. -/
lemma repR_none {ρ : ℕ} (hex : ¬ ∃ u, GRow m n F u) : repR m n F ρ = ρ := by
  classical
  unfold repR
  rw [ite_eq_right_of_eq_false _ _ (eq_false (fun ⟨u, _, hu⟩ => hex ⟨u, hu⟩)),
    dite_eq_right_of_eq_false (eq_false hex)]

/-- The greatest genuine row at or above. -/
lemma findGreatest_spec' {ρ : ℕ} (h : ∃ u ≤ ρ, GRow m n F u) :
    GRow m n F (Nat.findGreatest (GRow m n F) ρ) ∧ Nat.findGreatest (GRow m n F) ρ ≤ ρ := by
  classical
  obtain ⟨u, hu, hg⟩ := h
  exact ⟨Nat.findGreatest_spec hu hg, Nat.findGreatest_le ρ⟩

/-- The standing row is genuine (when some row is), and a genuine row stands for itself. -/
lemma repR_spec (hex : ∃ u, GRow m n F u) (ρ : ℕ) :
    GRow m n F (repR m n F ρ) ∧ (GRow m n F ρ → repR m n F ρ = ρ) := by
  classical
  by_cases h : ∃ u ≤ ρ, GRow m n F u
  · rw [repR_of_le h]
    refine ⟨(findGreatest_spec' h).1, fun hρ => ?_⟩
    exact le_antisymm (Nat.findGreatest_le ρ) (Nat.le_findGreatest le_rfl hρ)
  · rw [repR_of_not_le h hex]
    exact ⟨Nat.find_spec hex, fun hρ => absurd ⟨ρ, le_rfl, hρ⟩ h⟩

/-- **The standing row is nondecreasing.** -/
lemma repR_mono (hex : ∃ u, GRow m n F u) {ρ ρ' : ℕ} (hle : ρ ≤ ρ') :
    repR m n F ρ ≤ repR m n F ρ' := by
  classical
  by_cases h : ∃ u ≤ ρ, GRow m n F u
  · have h' : ∃ u ≤ ρ', GRow m n F u := let ⟨u, hu, hg⟩ := h; ⟨u, by omega, hg⟩
    rw [repR_of_le h, repR_of_le h']
    exact Nat.findGreatest_mono_right _ hle
  · rw [repR_of_not_le h hex]
    by_cases h' : ∃ u ≤ ρ', GRow m n F u
    · rw [repR_of_le h']
      obtain ⟨u, hu, hg⟩ := h'
      exact (Nat.find_min' hex hg).trans (Nat.le_findGreatest hu hg)
    · rw [repR_of_not_le h' hex]

/-- The multiplier of the shift in the copied matrix (`1` at a finite entry, `0` otherwise). -/
noncomputable def subMul (m n : ℕ) (F : ℕ → ℕ → Prop) (ρ κ : ℕ) : ℝ := by
  classical exact if (F (repR m n F ρ) κ) then 1 else 0

/-- The constant part of the copied matrix. -/
noncomputable def subVal (m n : ℕ) (F : ℕ → ℕ → Prop) (Dr : ℕ → ℕ → ℝ) (Hs : ℝ) (ρ κ : ℕ) :
    ℝ := by
  classical exact
    if (F (repR m n F ρ) κ) then Dr (repR m n F ρ) κ else Hs + wt n F (repR m n F ρ) κ

/-- **The copied matrix**: `subMul ρ κ · e κ + subVal ρ κ`. -/
noncomputable def extA (m n : ℕ) (F : ℕ → ℕ → Prop) (Dr : ℕ → ℕ → ℝ) (Hs : ℝ) (e : ℕ → ℝ)
    (ρ κ : ℕ) : ℝ := subMul m n F ρ κ * e κ + subVal m n F Dr Hs ρ κ

/-- The copied matrix is `subA` at the standing row. -/
lemma extA_eq (Dr : ℕ → ℕ → ℝ) (e : ℕ → ℝ) (ρ κ : ℕ) :
    extA m n F Dr Hs e ρ κ = subA n F (fun r k => e k + Dr r k) Hs (repR m n F ρ) κ := by
  classical
  unfold extA subMul subVal
  by_cases h : F (repR m n F ρ) κ
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h),
      subA_of h]; ring
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h),
      subA_of_not h]; ring

/-- **The copied matrix is totally monotone**, for every shift `e` of the columns. -/
theorem extA_totMono {Dr : ℕ → ℕ → ℝ} {e : ℕ → ℝ}
    (hc : ExtClosed m n F (fun r k => e k + Dr r k))
    (hB : ∀ ρ < m, ∀ κ < n, F ρ κ → e κ + Dr ρ κ + n < Hs) :
    IsTotMono m n (extA m n F Dr Hs e) := by
  intro ρ ρ' κ κ' h1 h2 h3 h4
  rw [extA_eq, extA_eq, extA_eq, extA_eq]
  by_cases hex : ∃ u, GRow m n F u
  · have hmono := repR_mono hex h1.le
    obtain ⟨⟨hm', hg'⟩, -⟩ := repR_spec hex ρ'
    obtain ⟨⟨hm, hg⟩, -⟩ := repR_spec hex ρ
    rcases Nat.lt_or_ge (repR m n F ρ) (repR m n F ρ') with hlt | hge
    · exact subA_totMono hc hB hlt hm' h3 h4 hg hg'
    · rw [show repR m n F ρ' = repR m n F ρ by omega]
      exact ⟨id, id⟩
  · rw [repR_none hex, repR_none hex]
    have hall : ∀ r < m, ∀ x < n, subA n F (fun r k => e k + Dr r k) Hs r x = Hs - x :=
      fun r hr x hx => by
        have hno : ¬ ∃ κ < n, F r κ := fun hf => hex ⟨r, hr, hf⟩
        have hF : ¬ F r x := fun hF => hno ⟨x, hx, hF⟩
        rw [subA_of_not hF]
        unfold wt
        rw [lcol_none hno, ite_eq_left_of_eq_true _ _ (eq_true hx)]; ring
    rw [hall ρ (by omega) κ (by omega), hall ρ (by omega) κ' h4, hall ρ' h2 κ (by omega),
      hall ρ' h2 κ' h4]
    exact ⟨id, id⟩

/-- **In a genuine row the leftmost minimum of the copied matrix is the minimum over the finite
entries.** -/
theorem extA_lmin {Dr : ℕ → ℕ → ℝ} {e : ℕ → ℝ}
    (hB : ∀ ρ < m, ∀ κ < n, F ρ κ → e κ + Dr ρ κ + n < Hs) {ρ : ℕ} (hg : GRow m n F ρ) :
    F ρ (lmin n (extA m n F Dr Hs e) ρ) ∧
      extA m n F Dr Hs e ρ (lmin n (extA m n F Dr Hs e) ρ) =
        e (lmin n (extA m n F Dr Hs e) ρ) + Dr ρ (lmin n (extA m n F Dr Hs e) ρ) ∧
      ∀ κ < n, F ρ κ → extA m n F Dr Hs e ρ (lmin n (extA m n F Dr Hs e) ρ) ≤ e κ + Dr ρ κ := by
  have hrep : repR m n F ρ = ρ := (repR_spec ⟨ρ, hg⟩ ρ).2 hg
  obtain ⟨hρ, μ, hμ, hFμ⟩ := hg
  have hn : 0 < n := by omega
  set κs := lmin n (extA m n F Dr Hs e) ρ
  have hκs : κs < n := lmin_lt _ ρ hn
  have hval : ∀ κ, extA m n F Dr Hs e ρ κ = subA n F (fun r k => e k + Dr r k) Hs ρ κ :=
    fun κ => by rw [extA_eq, hrep]
  have hle : ∀ κ < n, F ρ κ → extA m n F Dr Hs e ρ κs ≤ e κ + Dr ρ κ := fun κ hκ hF => by
    have := lmin_le (extA m n F Dr Hs e) ρ hκ
    rw [hval κ, subA_of hF] at this
    exact this
  have hF : F ρ κs := by
    by_contra hno
    have h1 := hle μ hμ hFμ
    rw [hval κs, subA_of_not hno] at h1
    have := hB ρ hρ μ hμ hFμ
    have := (wt_bound (F := F) (ρ := ρ) hκs).1
    linarith
  exact ⟨hF, by rw [hval κs, subA_of hF], hle⟩

end Ext

end Monge

end PlanarFlow
