module

public import PlanarFlow.BKMNW.PfMk

/-!
# The path's flags on the record, the pure part

The path `ρ` given (as in `PathPD`) by record indices `I j` (`j ≤ ρ.k`, `g (I j) = ρ.d j`), with
the record's reverses `rp` and vertex keys `vk` (equal keys iff equal tails):

* `PfIn`; **`pf_darts`** (`g i ∈ ρ.darts ↔ ∃ j < ρ.k, I j = i ∨ rp (I j) = i`), **`pf_mverts`**
  (`tail (g i) ∈ ρ.mverts ↔` its key is that of a tail `I j`, `j ≤ ρ.k`, or of a head
  `rp (I j)`, `j < ρ.k`), **`pf_mverts_tail`** (every vertex of the path is the tail of a dart of
  the record);
* the keys of the marks as the machine computes them (`pfKA` … `pfKD` with `pdSel`), and their
  values under `PathPD`: **`pfKA_eq`** … **`pfKD_eq`** (`I j` resp. `n` past the path).
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

open Finset

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- **The path on the record**: injective `g` on `[0, n)`, reverses `rp`, vertex keys `vk`, and
the path `ρ` by the record indices `I j` (`j ≤ ρ.k < n`). -/
structure PfIn (g : ℕ → D) (n : ℕ) (rp vk I : ℕ → ℕ) (ρ : HPath M) : Prop where
  inj : ∀ i < n, ∀ i' < n, g i = g i' → i = i'
  rp : ∀ i < n, rp i < n ∧ g (rp i) = M.rev (g i)
  vk : ∀ i < n, ∀ i' < n, (vk i = vk i' ↔ M.tail (g i) = M.tail (g i'))
  kn : ρ.k < n
  I : ∀ j ≤ ρ.k, I j < n ∧ g (I j) = ρ.d j ∧ M.tail (ρ.d j) = ρ.p j

variable {g : ℕ → D} {n : ℕ} {rp vk I pd ix : ℕ → ℕ} {ρ : HPath M}

/-- **The darts of the path on the record.** -/
theorem pf_darts (h : PfIn M g n rp vk I ρ) {i : ℕ} (hi : i < n) :
    g i ∈ ρ.darts ↔ ∃ j < ρ.k, I j = i ∨ rp (I j) = i := by
  rw [HPath.mem_darts]
  constructor
  · rintro ⟨j, hj, e | e⟩
    · obtain ⟨h1, h2, -⟩ := h.I j hj.le
      exact ⟨j, hj, Or.inl (h.inj _ h1 _ hi (by rw [h2, e]))⟩
    · obtain ⟨h1, h2, -⟩ := h.I j hj.le
      obtain ⟨h3, h4⟩ := h.rp _ h1
      exact ⟨j, hj, Or.inr (h.inj _ h3 _ hi (by rw [h4, h2, e]))⟩
  · rintro ⟨j, hj, e | e⟩
    · obtain ⟨-, h2, -⟩ := h.I j hj.le
      exact ⟨j, hj, Or.inl (by rw [← e, h2])⟩
    · obtain ⟨h1, h2, -⟩ := h.I j hj.le
      obtain ⟨-, h4⟩ := h.rp _ h1
      exact ⟨j, hj, Or.inr (by rw [← e, h4, h2])⟩

/-- **The vertices of the path on the record.** -/
theorem pf_mverts (h : PfIn M g n rp vk I ρ) {i : ℕ} (hi : i < n) :
    M.tail (g i) ∈ ρ.mverts ↔
      (∃ j ≤ ρ.k, vk (I j) = vk i) ∨ (∃ j < ρ.k, vk (rp (I j)) = vk i) := by
  rw [HPath.mem_mverts]
  constructor
  · rintro (⟨j, hj, e⟩ | ⟨j, hj, e⟩)
    · obtain ⟨h1, h2, h3⟩ := h.I j hj
      exact Or.inl ⟨j, hj, (h.vk _ h1 _ hi).2 (by rw [h2, h3, e])⟩
    · obtain ⟨h1, h2, -⟩ := h.I j hj.le
      obtain ⟨h3, h4⟩ := h.rp _ h1
      exact Or.inr ⟨j, hj, (h.vk _ h3 _ hi).2 (by rw [h4, h2, CombMap.tail_rev, e])⟩
  · rintro (⟨j, hj, e⟩ | ⟨j, hj, e⟩)
    · obtain ⟨h1, h2, h3⟩ := h.I j hj
      have := (h.vk _ h1 _ hi).1 e
      exact Or.inl ⟨j, hj, by rw [← h3, ← h2, this]⟩
    · obtain ⟨h1, h2, -⟩ := h.I j hj.le
      obtain ⟨h3, h4⟩ := h.rp _ h1
      have := (h.vk _ h3 _ hi).1 e
      exact Or.inr ⟨j, hj, by rw [← this, h4, h2, CombMap.tail_rev]⟩

/-- **Every vertex of the path is the tail of a dart of the record.** -/
theorem pf_mverts_tail (h : PfIn M g n rp vk I ρ) {v : V} (hv : v ∈ ρ.mverts) :
    ∃ i < n, M.tail (g i) = v := by
  rw [HPath.mem_mverts] at hv
  rcases hv with ⟨j, hj, e⟩ | ⟨j, hj, e⟩
  · obtain ⟨h1, h2, h3⟩ := h.I j hj
    exact ⟨I j, h1, by rw [h2, h3, e]⟩
  · obtain ⟨h1, h2, -⟩ := h.I j hj.le
    obtain ⟨h3, h4⟩ := h.rp _ h1
    exact ⟨rp (I j), h3, by rw [h4, h2, CombMap.tail_rev, e]⟩

/-! ### The keys of the marks -/

/-- The record index of the `j`-th dart: `IX[PD[j] - 1]`. -/
def pfI (pd ix : ℕ → ℕ) (j : ℕ) : ℕ := ix (pd j - 1)

/-- The key of the tails (`n` past the path). -/
def pfKA (pd ix vk : ℕ → ℕ) (n j : ℕ) : ℕ := pdSel (pd j / pd j) (vk (pfI pd ix j)) n

/-- The key of the first darts (`n` past the path's darts). -/
def pfKB (pd ix : ℕ → ℕ) (n j : ℕ) : ℕ := pdSel (pd (j + 1) / pd (j + 1)) (pfI pd ix j) n

/-- The key of the reverses. -/
def pfKC (pd ix rp : ℕ → ℕ) (n j : ℕ) : ℕ := pdSel (pd (j + 1) / pd (j + 1)) (rp (pfI pd ix j)) n

/-- The key of the heads. -/
def pfKD (pd ix rp vk : ℕ → ℕ) (n j : ℕ) : ℕ :=
  pdSel (pd (j + 1) / pd (j + 1)) (vk (rp (pfI pd ix j))) n

lemma dself_eq (x : ℕ) : x / x = if x = 0 then 0 else 1 := by
  split_ifs with h
  · subst h; simp
  · exact Nat.div_self (Nat.pos_of_ne_zero h)

/-- The `PathPD` shape of `PD`: nonzero up to `kk`, zero after. -/
def PdShape (pd : ℕ → ℕ) (n kk : ℕ) : Prop := (∀ j ≤ kk, pd j ≠ 0) ∧ (∀ j < n, kk < j → pd j = 0)

lemma pfKA_eq {pd ix vk : ℕ → ℕ} {n np kk : ℕ} (h : PdShape pd np kk) {j : ℕ} (hj : j < np) :
    pfKA pd ix vk n j = if j ≤ kk then vk (pfI pd ix j) else n := by
  unfold pfKA
  split_ifs with h1
  · rw [dself_eq, iteF (h.1 j h1), pdSel_one]
  · rw [dself_eq, iteT (h.2 j hj (by omega)), pdSel_zero]

lemma pf_sel_succ {pd : ℕ → ℕ} {np kk : ℕ} (h : PdShape pd np kk) {j : ℕ} (hj : j + 1 < np) :
    pd (j + 1) / pd (j + 1) = if j < kk then 1 else 0 := by
  rw [dself_eq]
  split_ifs with h1 h2 h2
  · exact absurd h1 (h.1 _ (by omega))
  · rfl
  · rfl
  · exact absurd (h.2 _ hj (by omega)) h1

lemma pfKB_eq {pd ix : ℕ → ℕ} {n np kk : ℕ} (h : PdShape pd np kk) {j : ℕ} (hj : j + 1 < np) :
    pfKB pd ix n j = if j < kk then pfI pd ix j else n := by
  unfold pfKB; rw [pf_sel_succ h hj]; split_ifs <;> simp [pdSel_one, pdSel_zero]

lemma pfKC_eq {pd ix rp : ℕ → ℕ} {n np kk : ℕ} (h : PdShape pd np kk) {j : ℕ} (hj : j + 1 < np) :
    pfKC pd ix rp n j = if j < kk then rp (pfI pd ix j) else n := by
  unfold pfKC; rw [pf_sel_succ h hj]; split_ifs <;> simp [pdSel_one, pdSel_zero]

lemma pfKD_eq {pd ix rp vk : ℕ → ℕ} {n np kk : ℕ} (h : PdShape pd np kk) {j : ℕ} (hj : j + 1 < np) :
    pfKD pd ix rp vk n j = if j < kk then vk (rp (pfI pd ix j)) else n := by
  unfold pfKD; rw [pf_sel_succ h hj]; split_ifs <;> simp [pdSel_one, pdSel_zero]

/-- **The dart flags from the marks**: `i` is a key `pfKB` or `pfKC` (`j < n - 1`) iff
`g i ∈ ρ.darts`. -/
theorem pf_darts_keys {np : ℕ} (h : PfIn M g n rp vk (pfI pd ix) ρ) (hs : PdShape pd np ρ.k)
    (hk' : ρ.k < np) {i : ℕ} (hi : i < n) :
    (∃ j < np - 1, pfKB pd ix n j = i ∨ pfKC pd ix rp n j = i) ↔ g i ∈ ρ.darts := by
  rw [pf_darts h hi]
  have hk := h.kn
  constructor
  · rintro ⟨j, hj, e | e⟩
    · rw [pfKB_eq hs (by omega)] at e
      split_ifs at e with h1
      · exact ⟨j, h1, Or.inl e⟩
      · omega
    · rw [pfKC_eq hs (by omega)] at e
      split_ifs at e with h1
      · exact ⟨j, h1, Or.inr e⟩
      · omega
  · rintro ⟨j, hj, e | e⟩
    · exact ⟨j, by omega, Or.inl (by rw [pfKB_eq hs (by omega), iteT hj, e])⟩
    · exact ⟨j, by omega, Or.inr (by rw [pfKC_eq hs (by omega), iteT hj, e])⟩

/-- **The vertex flags from the marks**: the key `vk i` is a key `pfKA` (`j < n`) or `pfKD`
(`j < n - 1`) iff `tail (g i) ∈ ρ.mverts` (keys `< n`). -/
theorem pf_mverts_keys {np : ℕ} (h : PfIn M g n rp vk (pfI pd ix) ρ)
    (hs : PdShape pd np ρ.k) (hk' : ρ.k < np) {i : ℕ} (hi : i < n) (hvk : vk i < n) :
    ((∃ j < np, pfKA pd ix vk n j = vk i) ∨ (∃ j < np - 1, pfKD pd ix rp vk n j = vk i)) ↔
      M.tail (g i) ∈ ρ.mverts := by
  rw [pf_mverts h hi]
  have hk := h.kn
  constructor
  · rintro (⟨j, hj, e⟩ | ⟨j, hj, e⟩)
    · rw [pfKA_eq hs hj] at e
      split_ifs at e with h1
      · exact Or.inl ⟨j, h1, e⟩
      · omega
    · rw [pfKD_eq hs (by omega)] at e
      split_ifs at e with h1
      · exact Or.inr ⟨j, h1, e⟩
      · omega
  · rintro (⟨j, hj, e⟩ | ⟨j, hj, e⟩)
    · exact Or.inl ⟨j, by omega, by rw [pfKA_eq hs (by omega), iteT hj, e]⟩
    · exact Or.inr ⟨j, by omega, by rw [pfKD_eq hs (by omega), iteT hj, e]⟩

end MfDrv

end BKMNW

end PlanarFlow
