module

public import PlanarFlow.Monge.Crossing

/-!
# Bellman–Ford rounds over the blocks of a dense distance graph

A round of Bellman–Ford over `ddg b D` processes the arcs block by block: for a block with the
sources `S` and a target `t`, the value of `t` is lowered to `V = min_{i ∈ S} (E i + D i t)`
(a row minimum of the block's Monge matrix), if that is smaller. `RoundOK b D k C E₀ E flag` is
the state of round `k` after the arcs `C` have been processed, from the values `E₀` at the start
of the round to the current values `E`, with `flag` recording whether some value has decreased:

* `RoundOK.start`: the start of a round;
* `RoundOK.update`: lowering one target to the minimum over a set of sources adds those arcs;
* `RoundOK.mono`: a smaller set of processed arcs;
* `RoundOK.finish`: when every arc has been processed, the values are below `bf (k + 1)` (and
  above `bf b` if a feasible potential exists); if no value has changed they form a feasible
  potential; if one has changed, `bf b < bf k` somewhere (impossible for `k = b`).

This is the in-place (Gauss–Seidel) variant of `PlanarFlow.Digraph.bf`, as in
`PlanarFlow.Digraph.le_bf_succ_of_round`.

## References

* P. N. Klein, S. Mozes, O. Weimann, *Shortest paths in directed planar graphs with negative
  lengths: a linear-space `O(n log² n)`-time algorithm*, ACM Trans. Algorithms 6 (2010), 30.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

/-- The state of round `k` of Bellman–Ford over `ddg b D` after the arcs `C` have been
processed: the values `E` are below the values `E₀` of the start of the round, `flag` records
whether one of them is strictly below, unchanged values satisfy the processed arc inequalities,
and (if a feasible potential exists) the values lie between `bf b` and `bf k` and satisfy the
processed arc inequalities against `bf k`. -/
structure RoundOK (b : ℕ) (D : ℕ → ℕ → ℤ) (k : ℕ) (C : ℕ → ℕ → Prop) (E₀ E : ℕ → ℤ) (flag : ℕ) :
    Prop where
  le : ∀ v < b, E v ≤ E₀ v
  chg : (flag = 0 ∧ ∀ v < b, E v = E₀ v) ∨ (flag = 1 ∧ ∃ v < b, E v < E₀ v)
  feas : flag = 0 → ∀ i j, i < b → j < b → i ≠ j → C i j → E j ≤ E i + D i j
  bf : HasPot b D → (∀ v < b, bfv b D b v ≤ E v ∧ E₀ v ≤ bfv b D k v) ∧
    ∀ i j, i < b → j < b → i ≠ j → C i j → E j ≤ bfv b D k i + D i j

variable {b : ℕ} {D : ℕ → ℕ → ℤ} {k : ℕ}

/-- The start of a round. -/
theorem RoundOK.start {E : ℕ → ℤ} (h : HasPot b D → ∀ v < b, bfv b D b v ≤ E v ∧ E v ≤ bfv b D k v) :
    RoundOK b D k (fun _ _ => False) E E 0 :=
  ⟨fun _ _ => le_rfl, Or.inl ⟨rfl, fun _ _ => rfl⟩, fun _ _ _ _ _ _ h => h.elim,
    fun hP => ⟨h hP, fun _ _ _ _ _ h => h.elim⟩⟩

/-- Fewer processed arcs. -/
theorem RoundOK.mono {C C' : ℕ → ℕ → Prop} {E₀ E : ℕ → ℤ} {flag : ℕ} (h : RoundOK b D k C E₀ E flag)
    (hC : ∀ i j, i < b → j < b → i ≠ j → C' i j → C i j) : RoundOK b D k C' E₀ E flag :=
  ⟨h.le, h.chg, fun hf i j hi hj hij hc => h.feas hf i j hi hj hij (hC i j hi hj hij hc),
    fun hP => ⟨(h.bf hP).1, fun i j hi hj hij hc => (h.bf hP).2 i j hi hj hij (hC i j hi hj hij hc)⟩⟩

/-- **One target lowered to the minimum over a set of sources.** -/
theorem RoundOK.update {C : ℕ → ℕ → Prop} {E₀ E : ℕ → ℤ} {flag : ℕ} (h : RoundOK b D k C E₀ E flag)
    {S : ℕ → Prop} {t : ℕ} (ht : t < b) (hS : ∀ i, S i → i < b ∧ i ≠ t) {V : ℤ}
    (hV1 : ∀ i, S i → V ≤ E i + D i t) (hV2 : ∃ i, S i ∧ V = E i + D i t) :
    RoundOK b D k (fun i j => C i j ∨ (S i ∧ j = t)) E₀
      (fun v => if v = t ∧ V < E t then V else E v) (if V < E t then 1 else flag) := by
  obtain ⟨hle, hfl, hfe, hbf⟩ := h
  by_cases hV : V < E t
  · simp only [hV, and_true, ite_true]
    refine ⟨fun v hv => ?_, Or.inr ⟨rfl, t, ht, ?_⟩, fun h => absurd h one_ne_zero, fun hP => ?_⟩
    · split_ifs with e
      · subst e; exact hV.le.trans (hle v hv)
      · exact hle v hv
    · simp only [ite_true]; exact lt_of_lt_of_le hV (hle t ht)
    · obtain ⟨h1, h2⟩ := hbf hP
      obtain ⟨i₀, hi₀, hVi₀⟩ := hV2
      refine ⟨fun v hv => ⟨?_, (h1 v hv).2⟩, fun i j hi hj hij hc => ?_⟩
      · split_ifs with e
        · subst e
          have := bfv_isPot hP (hS i₀ hi₀).1 hv (hS i₀ hi₀).2
          have := (h1 i₀ (hS i₀ hi₀).1).1
          omega
        · exact (h1 v hv).1
      · split_ifs with e
        · subst e
          rcases hc with hc | ⟨hc, -⟩
          · have := h2 i j hi hj hij hc; omega
          · have := hV1 i hc
            have := hle i hi
            have := (h1 i hi).2
            omega
        · rcases hc with hc | ⟨-, hc⟩
          · exact h2 i j hi hj hij hc
          · exact absurd hc e
  · simp only [hV, and_false, ite_false]
    refine ⟨hle, hfl, fun hf i j hi hj hij hc => ?_, fun hP => ⟨(hbf hP).1, fun i j hi hj hij hc => ?_⟩⟩
    · rcases hc with hc | ⟨hc, rfl⟩
      · exact hfe hf i j hi hj hij hc
      · have := hV1 i hc; omega
    · rcases hc with hc | ⟨hc, rfl⟩
      · exact (hbf hP).2 i j hi hj hij hc
      · have := hV1 i hc
        have := hle i hi
        have := ((hbf hP).1 i hi).2
        omega

/-- **The end of a round.** -/
theorem RoundOK.finish {E₀ E : ℕ → ℤ} {flag : ℕ}
    (h : RoundOK b D k (fun _ _ => True) E₀ E flag) :
    flag ≤ 1 ∧ (HasPot b D → ∀ v < b, bfv b D b v ≤ E v ∧ E v ≤ bfv b D (k + 1) v) ∧
      (flag = 0 → ∀ i j, i < b → j < b → i ≠ j → E j ≤ E i + D i j) ∧
      (flag = 1 → HasPot b D → ∃ v < b, bfv b D b v < bfv b D k v) := by
  obtain ⟨hle, hfl, hfe, hbf⟩ := h
  refine ⟨by rcases hfl with ⟨h, -⟩ | ⟨h, -⟩ <;> omega, fun hP => fun v hv => ⟨((hbf hP).1 v hv).1, ?_⟩,
    fun hf i j hi hj hij => hfe hf i j hi hj hij trivial, fun hf hP => ?_⟩
  · exact bfv_le_succ (fun w hw => (hle w hw).trans ((hbf hP).1 w hw).2)
      (fun i j hi hj hij => (hbf hP).2 i j hi hj hij trivial) hv
  · rcases hfl with ⟨h0, -⟩ | ⟨-, v, hv, hlt⟩
    · omega
    · exact ⟨v, hv, by have := (hbf hP).1 v hv; omega⟩

end Monge

end PlanarFlow
