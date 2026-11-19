module

public import PlanarFlow.NegSSSP.KEncNatB

/-!
# Bellman–Ford for the leaves: the semantics (negative lengths, a virtual source)

The leaf of the recursion needs a feasible potential of its piece, or the certificate that none
exists. On `m` arcs `a < m` from `T a` to `H a` (nodes `< w`) with lengths `lam a`
(`|lam a| ≤ L`, stored in the offset form `LL a = lam a + L`), Bellman–Ford from a **virtual
source with zero-length arcs** to every node: the values `D v` (natural words, `D v − K` the
value) start at `K` (value `0`); a relaxation of the arc `j` sets
`D (H j) := D (T j) + LL j − L` when `D (T j) + LL j < D (H j) + L`.

* `lbG`: the digraph of the arcs; `LBInv` (every value is the length of a walk of at most `s`
  arcs, and at most the length of every walk of at most `r` arcs), `LBArc` (the arcs of the
  current round already relaxed), `lbRelax`.
* `lb_step`, `lbInv_succ`: one relaxation, the end of a round.
* **`lb_feas`**: if no arc can be relaxed, `v ↦ D v − K` is feasible.
* **`lb_noPot`**: after `R ≥ w` rounds, if some arc can still be relaxed, **no feasible
  potential exists** (a feasible potential makes the cycles nonnegative: a walk shortened to
  distinct tails, `MSSP.exists_nodup_walk`, at most `w` arcs, is not longer, by the telescoping of
  the reduced lengths).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset MSSP WordRAM WordRAM.Machine

/-- **The digraph of the arcs of a leaf**: `a < m` from `T a` to `H a`, length `lam a`. -/
def lbG (m : ℕ) (T H : ℕ → ℕ) (lam : ℕ → ℤ) : Digraph ℕ (Fin m) where
  src a := T a
  dst a := H a
  len a := lam a

variable {m : ℕ} {T H : ℕ → ℕ} {lam : ℕ → ℤ}

/-- **The invariant of the leaf's Bellman–Ford**: every value is the length of a walk of at most
`s` arcs, and at most the length of every walk of at most `r` arcs. -/
def LBInv (m : ℕ) (T H : ℕ → ℕ) (lam : ℕ → ℤ) (w Db K r s : ℕ) (mem : ℕ → ℕ) : Prop :=
  (∀ v < w, ∃ x l, LWalk (lbG m T H lam) x v l ∧ l.length ≤ s ∧
      wlen (lbG m T H lam) l = (mem (Db + v) : ℤ) - K) ∧
  (∀ v < w, ∀ x l, LWalk (lbG m T H lam) x v l → l.length ≤ r →
      (mem (Db + v) : ℤ) - K ≤ wlen (lbG m T H lam) l)

/-- The arcs `< i` relaxed in the current round. -/
def LBArc (m : ℕ) (T H : ℕ → ℕ) (lam : ℕ → ℤ) (Db K r i : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ a : Fin m, (a : ℕ) < i → ∀ x l, LWalk (lbG m T H lam) x (T a) l → l.length ≤ r →
    (mem (Db + H a) : ℤ) - K ≤ wlen (lbG m T H lam) l + lam a

/-- **The relaxation of the arc `j`.** -/
def lbRelax (T H LL : ℕ → ℕ) (Db L j : ℕ) (mem : ℕ → ℕ) : ℕ → ℕ :=
  if mem (Db + T j) + LL j < mem (Db + H j) + L then
    upd mem (Db + H j) (mem (Db + T j) + LL j - L) else mem

lemma lb_wlen_ge {L : ℕ} (hlam : ∀ a < m, -(L : ℤ) ≤ lam a) :
    ∀ l : List (Fin m), -((l.length * L : ℕ) : ℤ) ≤ wlen (lbG m T H lam) l
  | [] => by simp
  | a :: l => by
    have := lb_wlen_ge hlam l
    have h1 := hlam a a.2
    rw [wlen_cons, List.length_cons, add_mul, one_mul]
    have e : (lbG m T H lam).len a = lam a := rfl
    rw [e]; push_cast at *; omega

lemma lbRelax_other {LL : ℕ → ℕ} {Db L j : ℕ} {mem : ℕ → ℕ} {a : ℕ}
    (ha : a ≠ Db + H j) : lbRelax T H LL Db L j mem a = mem a := by
  unfold lbRelax; split_ifs
  · rw [upd_other _ _ _ ha]
  · rfl

/-- **One relaxation keeps the invariant.** -/
theorem lb_step {w Db K L r s j : ℕ} {LL : ℕ → ℕ} (hj : j < m)
    (hT : ∀ a < m, T a < w) (hH : ∀ a < m, H a < w)
    (hLL : ∀ a < m, (LL a : ℤ) = lam a + L) (hlam : ∀ a < m, -(L : ℤ) ≤ lam a)
    (hK : (s + 1) * L ≤ K) {mem : ℕ → ℕ} (hI : LBInv m T H lam w Db K r s mem)
    (hA : LBArc m T H lam Db K r j mem) :
    LBInv m T H lam w Db K r (s + 1) (lbRelax T H LL Db L j mem) ∧
      LBArc m T H lam Db K r (j + 1) (lbRelax T H LL Db L j mem) := by
  obtain ⟨W1, W2⟩ := hI
  have tj := hT j hj
  have hj' := hH j hj
  have eLL := hLL j hj
  -- the value of the tail is not too small
  obtain ⟨x₀, l₀, hl₀, hlen₀, hw₀⟩ := W1 _ tj
  have hge := lb_wlen_ge (T := T) (H := H) (L := L) hlam l₀
  have h3 : l₀.length * L ≤ s * L := Nat.mul_le_mul_right _ hlen₀
  have hlo : (K : ℤ) ≤ mem (Db + T j) + s * L := by
    have : ((l₀.length * L : ℕ) : ℤ) ≤ ((s * L : ℕ) : ℤ) := by exact_mod_cast h3
    push_cast at this; omega
  have hK' : ((s + 1) * L : ℕ) ≤ (K : ℤ) := by exact_mod_cast hK
  push_cast at hK'
  have hlam' := hlam j hj
  by_cases hc : mem (Db + T j) + LL j < mem (Db + H j) + L
  · have e : lbRelax T H LL Db L j mem =
        upd mem (Db + H j) (mem (Db + T j) + LL j - L) := by
      unfold lbRelax; rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    have hsub : ((mem (Db + T j) + LL j - L : ℕ) : ℤ) = mem (Db + T j) + lam j := by
      have : L ≤ mem (Db + T j) + LL j := by
        have : (L : ℤ) ≤ mem (Db + T j) + LL j := by nlinarith
        exact_mod_cast this
      push_cast [this]; omega
    have hv : ∀ v, lbRelax T H LL Db L j mem (Db + v) =
        if v = H j then mem (Db + T j) + LL j - L else mem (Db + v) := by
      intro v
      rw [e, upd_apply]
      by_cases hx : v = H j
      · subst hx; simp
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
          ite_eq_right_of_eq_false _ _ (eq_false hx)]
    have hdec : ∀ v, (lbRelax T H LL Db L j mem (Db + v) : ℤ) ≤ mem (Db + v) := fun v => by
      rw [hv]; split_ifs with hx
      · subst hx; rw [hsub]; push_cast at hc eLL ⊢; omega
      · exact le_rfl
    refine ⟨⟨fun v hv' => ?_, fun v hv' x l hl hlen => ?_⟩, fun a ha x l hl hlen => ?_⟩
    · by_cases hx : v = H j
      · subst hx
        refine ⟨x₀, l₀ ++ [(⟨j, hj⟩ : Fin m)], hl₀.concat (G := lbG m T H lam) (a := (⟨j, hj⟩ : Fin m)) rfl, ?_, ?_⟩
        · simp only [List.length_append, List.length_singleton]; omega
        · rw [wlen_append, hw₀, hv, ite_eq_left_of_eq_true _ _ (eq_true rfl), hsub]
          simp only [wlen_cons, wlen_nil, add_zero]
          change _ + lam j = _
          ring
      · obtain ⟨x, l, hl, hlen, hw⟩ := W1 v hv'
        refine ⟨x, l, hl, by omega, ?_⟩
        rw [hv, ite_eq_right_of_eq_false _ _ (eq_false hx)]; exact hw
    · have := W2 v hv' x l hl hlen
      have := hdec v
      omega
    · by_cases hai : (a : ℕ) = j
      · have ha' : a = ⟨j, hj⟩ := Fin.ext hai
        subst ha'
        have hw := W2 _ tj x l hl hlen
        rw [hv, ite_eq_left_of_eq_true _ _ (eq_true rfl), hsub]
        simp only at hl ⊢
        omega
      · have := hA a (by omega) x l hl hlen
        have := hdec (H a)
        omega
  · have e : lbRelax T H LL Db L j mem = mem := by
      unfold lbRelax; rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    rw [e]
    refine ⟨⟨fun v hv' => ?_, W2⟩, fun a ha x l hl hlen => ?_⟩
    · obtain ⟨x, l, hl, hlen, hw⟩ := W1 v hv'
      exact ⟨x, l, hl, by omega, hw⟩
    · by_cases hai : (a : ℕ) = j
      · have ha' : a = ⟨j, hj⟩ := Fin.ext hai
        subst ha'
        have hw := W2 _ tj x l hl hlen
        simp only at hl ⊢
        push_cast at hc eLL
        omega
      · exact hA a (by omega) x l hl hlen

/-- **The end of a round**: all the arcs relaxed, the invariant for one more arc. -/
theorem lbInv_succ {w Db K r s : ℕ} {mem : ℕ → ℕ} (hH : ∀ a < m, H a < w)
    (hI : LBInv m T H lam w Db K r s mem) (hA : LBArc m T H lam Db K r m mem) :
    LBInv m T H lam w Db K (r + 1) s mem := by
  obtain ⟨W1, W2⟩ := hI
  refine ⟨W1, fun v hv x l hl hlen => ?_⟩
  by_cases hle : l.length ≤ r
  · exact W2 v hv x l hl hle
  · rcases List.eq_nil_or_concat l with rfl | ⟨l', a, rfl⟩
    · simp at hle
    · rw [List.concat_eq_append] at hl hle hlen ⊢
      obtain ⟨hl', hx⟩ := LWalk.concat_iff.1 hl
      simp only [List.length_append, List.length_singleton] at hle hlen
      have := hA a a.2 x l' hl' (by omega)
      have hx' : H a = v := hx
      rw [hx'] at this
      rw [wlen_append]
      simp only [wlen_cons, wlen_nil, add_zero]
      exact this

/-- **No arc relaxable: the values are a feasible potential.** -/
theorem lb_feas {LL : ℕ → ℕ} {Db K L : ℕ} {mem : ℕ → ℕ}
    (hLL : ∀ a < m, (LL a : ℤ) = lam a + L)
    (h : ∀ j < m, ¬ mem (Db + T j) + LL j < mem (Db + H j) + L) :
    ∀ j < m, (mem (Db + H j) : ℤ) - K ≤ (mem (Db + T j) : ℤ) - K + lam j := by
  intro j hj
  have := h j hj
  have := hLL j hj
  push_cast at *; omega

/-- Telescoping of the reduced lengths along a walk. -/
lemma lb_tele (p : ℕ → ℤ) {x y : ℕ} {l : List (Fin m)} (h : LWalk (lbG m T H lam) x y l) :
    wlen (lbG m T H lam) l =
      (l.map fun a : Fin m => lam a + p (T a) - p (H a)).sum - p x + p y := by
  induction h with
  | nil x => simp
  | @cons a y l _ ih =>
    rw [wlen_cons, ih, List.map_cons, List.sum_cons]
    have e1 : (lbG m T H lam).len a = lam a := rfl
    have e2 : (lbG m T H lam).src a = T a := rfl
    have e3 : (lbG m T H lam).dst a = H a := rfl
    rw [e1, e2, e3]
    ring

/-- A walk with distinct tails below `w` has at most `w` arcs. -/
lemma lb_len_le {w : ℕ} (hT : ∀ a < m, T a < w) {l : List (Fin m)}
    (hnd : (l.map (lbG m T H lam).src).Nodup) : l.length ≤ w := by
  have hs : (l.map (lbG m T H lam).src).toFinset ⊆ range w := by
    intro x hx
    simp only [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨a, -, rfl⟩ := hx
    exact mem_range.2 (hT a a.2)
  have := card_le_card hs
  rwa [List.toFinset_card_of_nodup hnd, List.length_map, card_range] at this

/-- **After `R ≥ w` rounds, an arc still relaxable certifies that no feasible potential
exists.** -/
theorem lb_noPot {w Db K L R s : ℕ} {LL : ℕ → ℕ} {mem : ℕ → ℕ}
    (hT : ∀ a < m, T a < w) (hH : ∀ a < m, H a < w) (hLL : ∀ a < m, (LL a : ℤ) = lam a + L) (hR : w ≤ R)
    (hI : LBInv m T H lam w Db K R s mem) {j : ℕ} (hj : j < m)
    (hv : mem (Db + T j) + LL j < mem (Db + H j) + L) :
    ¬ ∃ p : ℕ → ℤ, ∀ a < m, p (H a) ≤ p (T a) + lam a := by
  classical
  rintro ⟨p, hp⟩
  obtain ⟨W1, W2⟩ := hI
  obtain ⟨x, l, hl, -, hw⟩ := W1 _ (hT j hj)
  have hl' : LWalk (lbG m T H lam) x (H j) (l ++ [⟨j, hj⟩]) := hl.concat (G := lbG m T H lam) (a := (⟨j, hj⟩ : Fin m)) rfl
  obtain ⟨l', hw', hsub, hnd⟩ := exists_nodup_walk hl'
  have hlen := lb_len_le (H := H) (lam := lam) hT hnd
  have h1 := W2 _ (hH j hj) x l' hw' (by omega)
  have t1 := lb_tele (lam := lam) p hw'
  have t2 := lb_tele (lam := lam) p hl'
  have hle : (l'.map fun a : Fin m => lam a + p (T a) - p (H a)).sum ≤
      ((l ++ [(⟨j, hj⟩ : Fin m)]).map fun a : Fin m => lam a + p (T a) - p (H a)).sum :=
    List.Sublist.sum_le_sum (hsub.map _) (fun b hb => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hb
      have := hp a a.2; linarith)
  rw [wlen_append, hw] at t2
  simp only [wlen_cons, wlen_nil, add_zero] at t2
  have e : (lbG m T H lam).len ⟨j, hj⟩ = lam j := rfl
  rw [e] at t2
  have := hLL j hj
  push_cast at hv
  linarith

end NegSSSP

end PlanarFlow
