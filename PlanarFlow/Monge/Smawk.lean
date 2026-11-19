module

public import PlanarFlow.Monge.Basic
public import Mathlib.Tactic.Ring

/-!
# The algorithm SMAWK: the mathematics

The row minima of a totally monotone `m × n` matrix can be found with `O(m + n)` entry
evaluations (Aggarwal, Klawe, Moran, Shor, Wilber). The rows are numbered `1, …, m` (row `r` is
the row `r - 1` of `A`); at the *level* `s = 2 ^ ℓ` the rows are the multiples of `s`, the
`k`-th one (`k < p = ⌊m / s⌋`) being the row `ρ s k = (k + 1) s - 1` of `A`.

* **Reduce** (`RedInv`). Going down the levels, a list of columns containing the leftmost
  minima of all the rows of the level is reduced to at most `p` columns which still contain
  them, by one pass with a stack: the column `j` on top of the stack, at position `t - 1`, is
  compared with the next column `j'` in the row `ρ s (t - 1)`; if `j'` is strictly better, `j`
  is popped (`RedInv.pop`); otherwise `j'` is pushed (`RedInv.push`), or discarded when the stack
  is full (`RedInv.discard`). The invariant: the stack is increasing, its column at position `u`
  is not the leftmost minimum of any of the rows `ρ s k` with `k < u` (`dead`), and every leftmost
  minimum seen so far is on the stack (`keep`). The columns of the stack at one level contain
  the leftmost minima of the next level, whose rows are the rows `ρ s (2k + 1)`.
* **Interpolate** (`interp_eq`). Going up the levels, the leftmost minimum of an odd multiple
  `r` of `s` lies, in the reduced list of the level, between those of `r - s` and `r + s`
  (`IsTotMono.lmin_mono`), and a scan of this window finds it.

Lists of columns are functions `L : ℕ → ℕ`, increasing up to a sentinel `L len = n`
(`IsCols`).

## References

* A. Aggarwal, M. M. Klawe, S. Moran, P. Shor, R. Wilber, *Geometric applications of a
  matrix-searching algorithm*, Algorithmica 2 (1987), 195–208.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

/-- An increasing list of columns `L 0 < L 1 < ⋯ < L len = n`, ended by the sentinel `n`. -/
def IsCols (n : ℕ) (L : ℕ → ℕ) (len : ℕ) : Prop :=
  (∀ i j, i < j → j ≤ len → L i < L j) ∧ L len = n

lemma IsCols.lt {n : ℕ} {L : ℕ → ℕ} {len : ℕ} (h : IsCols n L len) {i : ℕ} (hi : i < len) :
    L i < n := h.2 ▸ h.1 i len hi le_rfl

lemma IsCols.le_iff {n : ℕ} {L : ℕ → ℕ} {len : ℕ} (h : IsCols n L len) {i j : ℕ} (hj : j ≤ len)
    (hi : i ≤ len) : L i ≤ L j ↔ i ≤ j := by
  constructor
  · intro hle
    by_contra hlt
    exact absurd hle (not_le.2 (h.1 j i (by omega) hi))
  · intro hle
    rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · exact le_rfl
    · exact (h.1 i j hlt hj).le

/-- The identity list `0, 1, …, n`. -/
lemma isCols_id (n : ℕ) : IsCols n (fun j => j) n := ⟨fun _ _ h _ => h, rfl⟩

/-- The `k`-th row of the level `s` (a row of `A`). -/
def rowL (s k : ℕ) : ℕ := (k + 1) * s - 1

lemma rowL_lt {m s p k : ℕ} (hs : 0 < s) (hps : p * s ≤ m) (hk : k < p) : rowL s k < m := by
  unfold rowL
  have : (k + 1) * s ≤ p * s := Nat.mul_le_mul_right _ hk
  have : 1 ≤ (k + 1) * s := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  omega

lemma rowL_mono {s k k' : ℕ} (h : k ≤ k') : rowL s k ≤ rowL s k' := by
  unfold rowL
  have := Nat.mul_le_mul_right s (show k + 1 ≤ k' + 1 by omega)
  omega

lemma rowL_strict {s k k' : ℕ} (hs : 0 < s) (h : k < k') : rowL s k < rowL s k' := by
  unfold rowL
  have := Nat.mul_le_mul_right s (show k + 2 ≤ k' + 1 by omega)
  have : 1 ≤ (k + 1) * s := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  rw [show (k + 2) * s = (k + 1) * s + s by ring] at *
  omega

/-- The rows of the level `2s` are rows of the level `s`. -/
lemma rowL_double (s k : ℕ) : rowL (2 * s) k = rowL s (2 * k + 1) := by
  unfold rowL; congr 1; ring

/-- A column beaten strictly by another is not the leftmost minimum. -/
lemma ne_lmin_of_lt {n : ℕ} {A : ℕ → ℕ → α} {r c c' : ℕ} (hc' : c' < n) (h : A r c' < A r c) :
    c ≠ lmin n A r := by
  rintro rfl
  exact absurd (lmin_le A r hc') (not_le.2 h)

/-- A column beaten weakly by a column on its left is not the leftmost minimum. -/
lemma ne_lmin_of_le_left {n : ℕ} {A : ℕ → ℕ → α} {r c c' : ℕ} (hc : c < n) (hcc : c' < c)
    (h : A r c' ≤ A r c) : c ≠ lmin n A r := by
  rintro rfl
  exact absurd h (not_le.2 ((isLMin_lmin A r (by omega)).2.2.2 c' (Nat.zero_le _) hcc))

/-! ### Reduce -/

/-- The state of the reduction at the level `s` (`p` rows) after the input columns
`In 0, …, In (i - 1)` have been processed, with the stack `St 0, …, St (t - 1)`. -/
structure RedInv (n : ℕ) (A : ℕ → ℕ → α) (s p : ℕ) (In St : ℕ → ℕ) (i t : ℕ) : Prop where
  tle : t ≤ p
  sub : ∀ u < t, ∃ i' < i, St u = In i'
  inc : ∀ u v, u < v → v < t → St u < St v
  dead : ∀ u < t, ∀ k < u, St u ≠ lmin n A (rowL s k)
  keep : ∀ k < p, ∀ i' < i, In i' = lmin n A (rowL s k) → ∃ u < t, St u = lmin n A (rowL s k)

variable {m n : ℕ} {A : ℕ → ℕ → α} {s p : ℕ} {In St : ℕ → ℕ} {N i t : ℕ}

theorem RedInv.init (St : ℕ → ℕ) : RedInv n A s p In St 0 0 :=
  ⟨Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩

/-- In the row `ρ s k` with `k ≥ t - 1`, the new column beats the top of the stack. -/
lemma RedInv.top_lt (h : RedInv n A s p In St i t) (hA : IsTotMono m n A) (hs : 0 < s)
    (hps : p * s ≤ m) (hIn : IsCols n In N) (hi : i < N) (ht : 0 < t)
    (hlt : A (rowL s (t - 1)) (In i) < A (rowL s (t - 1)) (St (t - 1))) {k : ℕ} (hk : k < p)
    (hkt : t - 1 ≤ k) : A (rowL s k) (In i) < A (rowL s k) (St (t - 1)) := by
  obtain ⟨i', hi', he⟩ := h.sub (t - 1) (by omega)
  have hlt' : St (t - 1) < In i := he ▸ hIn.1 i' i hi' hi.le
  rcases Nat.eq_or_lt_of_le hkt with e | hlt2
  · rw [← e]; exact hlt
  · exact (hA _ _ _ _ (rowL_strict hs hlt2) (rowL_lt hs hps hk) hlt' (hIn.lt hi)).1 hlt

/-- **Pop**: the top of the stack is beaten by the new column in its row. -/
theorem RedInv.pop (h : RedInv n A s p In St i t) (hA : IsTotMono m n A) (hs : 0 < s)
    (hps : p * s ≤ m) (hIn : IsCols n In N) (hi : i < N) (ht : 0 < t)
    (hlt : A (rowL s (t - 1)) (In i) < A (rowL s (t - 1)) (St (t - 1))) :
    RedInv n A s p In St i (t - 1) := by
  refine ⟨by have := h.tle; omega, fun u hu => h.sub u (by omega),
    fun u v huv hv => h.inc u v huv (by omega), fun u hu => h.dead u (by omega),
    fun k hk i' hi' he => ?_⟩
  obtain ⟨u, hu, hSt⟩ := h.keep k hk i' hi' he
  rcases Nat.lt_or_ge u (t - 1) with hlt' | hge
  · exact ⟨u, hlt', hSt⟩
  · exfalso
    rw [show u = t - 1 by omega] at hSt
    rcases Nat.lt_or_ge k (t - 1) with hk' | hk'
    · exact h.dead (t - 1) (by omega) k hk' hSt
    · exact ne_lmin_of_lt (hIn.lt hi) (h.top_lt hA hs hps hIn hi ht hlt hk hk') hSt

/-- In the rows `ρ s k` with `k < t`, the new column is not the leftmost minimum when it does not
beat the top of the stack. -/
lemma RedInv.new_dead (h : RedInv n A s p In St i t) (hA : IsTotMono m n A) (hs : 0 < s)
    (hps : p * s ≤ m) (hIn : IsCols n In N) (hi : i < N) (ht : 0 < t)
    (hle : A (rowL s (t - 1)) (St (t - 1)) ≤ A (rowL s (t - 1)) (In i)) {k : ℕ} (hk : k < t) :
    In i ≠ lmin n A (rowL s k) := by
  obtain ⟨i', hi', he⟩ := h.sub (t - 1) (by omega)
  have hlt' : St (t - 1) < In i := he ▸ hIn.1 i' i hi' hi.le
  have htp := h.tle
  refine ne_lmin_of_le_left (hIn.lt hi) hlt' ?_
  rcases Nat.eq_or_lt_of_le (show k ≤ t - 1 by omega) with e | hlt2
  · rw [e]; exact hle
  · by_contra hcon
    rw [not_le] at hcon
    have := (hA _ _ _ _ (rowL_strict hs hlt2) (rowL_lt hs hps (by omega)) hlt' (hIn.lt hi)).1 hcon
    exact absurd hle (not_le.2 this)

/-- **Push**: the new column is pushed on a stack which is not full. -/
theorem RedInv.push (h : RedInv n A s p In St i t) (hA : IsTotMono m n A) (hs : 0 < s)
    (hps : p * s ≤ m) (hIn : IsCols n In N) (hi : i < N) (htp : t < p)
    (hle : t = 0 ∨ A (rowL s (t - 1)) (St (t - 1)) ≤ A (rowL s (t - 1)) (In i)) {St' : ℕ → ℕ}
    (h1 : ∀ u < t, St' u = St u) (h2 : St' t = In i) :
    RedInv n A s p In St' (i + 1) (t + 1) := by
  refine ⟨by omega, fun u hu => ?_, fun u v huv hv => ?_, fun u hu k hk => ?_,
    fun k hk i' hi' he => ?_⟩
  · rcases Nat.lt_or_ge u t with hlt | hge
    · obtain ⟨i', hi', e⟩ := h.sub u hlt
      exact ⟨i', by omega, (h1 u hlt).trans e⟩
    · exact ⟨i, by omega, by rw [show u = t by omega, h2]⟩
  · rcases Nat.lt_or_ge v t with hlt | hge
    · rw [h1 u (by omega), h1 v hlt]; exact h.inc u v huv hlt
    · rw [h1 u (by omega), show v = t by omega, h2]
      obtain ⟨i', hi', e⟩ := h.sub u (by omega)
      exact e ▸ hIn.1 i' i hi' hi.le
  · rcases Nat.lt_or_ge u t with hlt | hge
    · rw [h1 u hlt]; exact h.dead u hlt k hk
    · rw [show u = t by omega, h2]
      rcases hle with h0 | hle
      · omega
      · exact h.new_dead hA hs hps hIn hi (by omega) hle (by omega)
  · rcases Nat.lt_or_ge i' i with hlt | hge
    · obtain ⟨u, hu, e⟩ := h.keep k hk i' hlt he
      exact ⟨u, by omega, (h1 u hu).trans e⟩
    · exact ⟨t, by omega, by rw [h2, ← he, show i' = i by omega]⟩

/-- **Discard**: the new column does not beat the top of a full stack. -/
theorem RedInv.discard (h : RedInv n A s p In St i t) (hA : IsTotMono m n A) (hs : 0 < s)
    (hps : p * s ≤ m) (hIn : IsCols n In N) (hi : i < N) (htp : t = p) (hp : 0 < p)
    (hle : A (rowL s (t - 1)) (St (t - 1)) ≤ A (rowL s (t - 1)) (In i)) :
    RedInv n A s p In St (i + 1) t := by
  refine ⟨h.tle, fun u hu => ?_, h.inc, h.dead, fun k hk i' hi' he => ?_⟩
  · obtain ⟨i', hi', e⟩ := h.sub u hu
    exact ⟨i', by omega, e⟩
  · rcases Nat.lt_or_ge i' i with hlt | hge
    · exact h.keep k hk i' hlt he
    · rw [show i' = i by omega] at he
      exact absurd he (h.new_dead hA hs hps hIn hi (by omega) hle (by omega))

/-- **The end of the reduction**: the stack contains the leftmost minima of all the rows of the
level, and with the sentinel it is a list of columns. -/
theorem RedInv.final (h : RedInv n A s p In St N t) (hIn : IsCols n In N)
    (hall : ∀ k < p, ∃ i' < N, In i' = lmin n A (rowL s k)) {St' : ℕ → ℕ}
    (h1 : ∀ u < t, St' u = St u) (h2 : St' t = n) :
    IsCols n St' t ∧ ∀ k < p, ∃ u < t, St' u = lmin n A (rowL s k) := by
  refine ⟨⟨fun u v huv hv => ?_, h2⟩, fun k hk => ?_⟩
  · rw [h1 u (by omega)]
    rcases Nat.lt_or_ge v t with hlt | hge
    · rw [h1 v hlt]; exact h.inc u v huv hlt
    · rw [show v = t by omega, h2]
      obtain ⟨i', hi', e⟩ := h.sub u (by omega)
      exact e ▸ hIn.lt hi'
  · obtain ⟨i', hi', e⟩ := hall k hk
    obtain ⟨u, hu, e'⟩ := h.keep k hk i' hi' e
    exact ⟨u, hu, (h1 u hu).trans e'⟩

/-! ### Interpolate -/

/-- **The scan of a window of a reduced list.** Let `L` be a list of columns containing the
leftmost minimum `L i⋆` of the row `R`, with `L lo ≤ L i⋆` and `L i⋆ < h`. If the positions
`lo, …, cur - 1` all have columns `< h` and `L cur ≥ h`, then the leftmost minimum of
`i ↦ A R (L i)` on the window `[lo, cur - 1]` is at `i⋆`. -/
theorem interp_eq {L : ℕ → ℕ} {len R lo cur h istar best : ℕ} (hL : IsCols n L len)
    (hstar : istar < len) (hlolen : lo ≤ len) (he : L istar = lmin n A R) (hlo : L lo ≤ L istar) (hh : L istar < h)
    (hhn : h ≤ n) (hcur : ∀ i, lo ≤ i → i < cur → L i < h) (hend : h ≤ L cur)
    (hbest : IsLMin (fun i => A R (L i)) lo (cur - 1) best) :
    best = istar ∧ cur - 1 < len := by
  have hlo' : lo ≤ istar := (hL.le_iff hstar.le hlolen).1 hlo
  have hcur' : istar < cur := by
    by_contra hc
    rw [not_lt] at hc
    rcases Nat.eq_or_lt_of_le hc with e | hlt
    · rw [e] at hend; omega
    · have := hL.1 cur istar hlt hstar.le; omega
  have hlen : cur - 1 < len := by
    by_contra hc
    rw [not_lt] at hc
    have := hcur len (by omega) (by omega)
    rw [hL.2] at this; omega
  refine ⟨hbest.unique ⟨hlo', by omega, fun j h1 h2 => ?_, fun j h1 h2 => ?_⟩, hlen⟩
  · show A R (L istar) ≤ A R (L j)
    rw [he]; exact lmin_le A R (hL.lt (by omega))
  · show A R (L istar) < A R (L j)
    have : L j < L istar := hL.1 j istar h2 hstar.le
    rw [he] at this ⊢
    exact (isLMin_lmin A R (by omega)).2.2.2 _ (Nat.zero_le _) this

/-- After the scan, the last position of the window is the position of `h - 1` if `h - 1` is in
the list: it is the left end of the window of the next row. -/
theorem interp_next {L : ℕ → ℕ} {len lo cur h q : ℕ} (hL : IsCols n L len) (hq : q < len)
    (hlolen : lo ≤ len)
    (hLq : L q + 1 = h) (hlo : L lo ≤ L q) (hcur : ∀ i, lo ≤ i → i < cur → L i < h)
    (hend : h ≤ L cur) (hlocur : lo < cur) : cur - 1 = q := by
  have hlq : lo ≤ q := (hL.le_iff hq.le hlolen).1 hlo
  have h1 : q < cur := by
    by_contra hc
    rw [not_lt] at hc
    rcases Nat.eq_or_lt_of_le hc with e | hlt
    · rw [e] at hend; omega
    · have := hL.1 cur q hlt hq.le; omega
  have hlen : cur - 1 ≤ len := by
    by_contra hc
    have := hcur len hlolen (by omega)
    have := hL.lt hq
    rw [hL.2] at *
    omega
  have h2 : cur - 1 ≤ q := by
    by_contra hc
    rw [not_le] at hc
    have := hcur (cur - 1) (by omega) (by omega)
    have := hL.1 q (cur - 1) hc hlen
    omega
  omega

end Monge

end PlanarFlow
