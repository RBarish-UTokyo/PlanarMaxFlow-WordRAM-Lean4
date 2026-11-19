module

public import PlanarFlow.BKMNW.NrDkM

/-!
# The counting sort `osProg` as stable out-lists

`NegSSSP.osProg_exec` describes its output through the lists `pre`/`blk` of `csList`. Here, for
the kept indices `F y = [i < M | K i ≠ 0 ∧ T i = y]` (in increasing order):

* **`nrOs_exec`**: `OE[y] = OB[y] + |F y|`, `OL[OB[y] + t] = (F y)[t]`, `OE[y] ≤ M`, and
  `Σ_{y < N} (OE[y] - OB[y]) ≤ M`;
* `nr_ord_arc`, `nr_ord_all`: every listed index has key `y`, every kept index is listed under
  its key.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP Monge.FR

/-- The kept indices of key `y`, in increasing order. -/
def nrF (T K : ℕ → ℕ) (M y : ℕ) : List ℕ :=
  (List.range M).filter fun i => decide (K i ≠ 0 ∧ T i = y)

lemma nr_pre_len_sum (L : List (ℕ × ℕ × ℤ)) : ∀ N,
    ∑ y ∈ range N, (blk L y).length = (pre L N).length
  | 0 => by simp [pre]
  | N + 1 => by rw [sum_range_succ, nr_pre_len_sum L N, pre_succ, List.length_append]

variable {P : Input} {W : ℕ} {M N Tb Kb Ob Cb OBb OEb Db : ℕ} {T K : ℕ → ℕ}

/-- **The counting sort as stable out-lists** (see the module docstring). -/
theorem nrOs_exec (hL : OsLay M N Tb Kb Ob Cb OBb OEb Db W T K) (c : Config)
    (hc : WordsBounded W c) (hI : OsIn M N Tb Kb Ob Cb OBb OEb Db T K c) :
    ∃ c' k, Exec P W osProg c c' k ∧ k ≤ osCost M N ∧
      (∀ y < N, c'.nmem (OEb + y) = c'.nmem (OBb + y) + (nrF T K M y).length ∧
        c'.nmem (OEb + y) ≤ M ∧
        ∀ t (ht : t < (nrF T K M y).length),
          c'.nmem (Db + (c'.nmem (OBb + y) + t)) = (nrF T K M y)[t]) ∧
      ∑ y ∈ range N, (c'.nmem (OEb + y) - c'.nmem (OBb + y)) ≤ M ∧
      (∀ a, (a < Ob ∨ Ob + 2 * N + 1 ≤ a) → (a < OBb ∨ Db + M ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1510 ∨ 1520 < r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', k, ex, hk, hOB, hOL, hm, hn, hr, hrm, ho⟩ := osProg_exec (P := P) hL c hc hI
  set L := csList T id K (fun _ => 0) M with hLd
  have hbl : ∀ y, (blk L y).map (fun a => a.2.1) = nrF T K M y := fun y => blk_map_csList T K _ y M
  have hlen : ∀ y, (blk L y).length = (nrF T K M y).length := fun y => by
    rw [← hbl y, List.length_map]
  have hpreN : (pre L N).length ≤ M := (length_pre_le _ _).trans (length_csList_le M)
  refine ⟨c', k, ex, hk, fun y hy => ?_, ?_, hm, hn, hr, hrm, ho⟩
  · obtain ⟨b1, b2⟩ := hOB y hy
    have e1 : (pre L (y + 1)).length = (pre L y).length + (nrF T K M y).length := by
      rw [pre_succ, List.length_append, hlen]
    obtain ⟨rest, hrest⟩ := pre_add L (y + 1) (N - (y + 1))
    rw [show y + 1 + (N - (y + 1)) = N by omega] at hrest
    have hle : (pre L (y + 1)).length ≤ (pre L N).length := by rw [hrest]; simp
    refine ⟨by rw [b2, b1, e1], by rw [b2]; omega, fun t ht => ?_⟩
    rw [b1]
    have hlt : (pre L y).length + t < (pre L N).length := by omega
    rw [hOL _ hlt, hrest, pre_succ, List.append_assoc, List.getD_eq_getElem _ _ (by
        simp only [List.length_append]; rw [hlen]; omega),
      List.getElem_append_right (by omega), List.getElem_append_left (by rw [hlen]; omega)]
    have := congrArg (fun l => l[t]?) (hbl y)
    simp only [List.getElem?_map] at this
    rw [List.getElem?_eq_getElem (by rw [hlen]; omega),
      List.getElem?_eq_getElem ht] at this
    simp only [Option.map_some, Option.some.injEq] at this
    simpa using this
  · rw [← show ∑ y ∈ range N, (blk L y).length = (pre L N).length from nr_pre_len_sum L N]
      at hpreN
    refine le_trans (le_of_eq (sum_congr rfl fun y hy => ?_)) hpreN
    obtain ⟨b1, b2⟩ := hOB y (mem_range.1 hy)
    rw [b1, b2, pre_succ, List.length_append]; omega

/-- Every listed index has its key. -/
lemma nr_ord_arc {OB OE OL : ℕ → ℕ} {y : ℕ}
    (hy : OE y = OB y + (nrF T K M y).length ∧
      ∀ t (ht : t < (nrF T K M y).length), OL (OB y + t) = (nrF T K M y)[t])
    {i : ℕ} (h1 : OB y ≤ i) (h2 : i < OE y) : OL i < M ∧ K (OL i) ≠ 0 ∧ T (OL i) = y := by
  have ht : i - OB y < (nrF T K M y).length := by omega
  have e := hy.2 _ ht
  rw [show OB y + (i - OB y) = i by omega] at e
  have hm := List.getElem_mem ht
  rw [← e] at hm
  simp only [nrF, List.mem_filter, List.mem_range, decide_eq_true_eq] at hm
  exact ⟨hm.1, hm.2⟩

/-- Every kept index is listed under its key. -/
lemma nr_ord_all {OB OE OL : ℕ → ℕ} {j : ℕ} (hj : j < M) (hK : K j ≠ 0)
    (hy : OE (T j) = OB (T j) + (nrF T K M (T j)).length ∧
      ∀ t (ht : t < (nrF T K M (T j)).length), OL (OB (T j) + t) = (nrF T K M (T j))[t]) :
    ∃ i, OB (T j) ≤ i ∧ i < OE (T j) ∧ OL i = j := by
  have hm : j ∈ nrF T K M (T j) := by
    simp only [nrF, List.mem_filter, List.mem_range, decide_eq_true_eq, and_true]; exact ⟨hj, hK⟩
  obtain ⟨t, ht, e⟩ := List.getElem_of_mem hm
  exact ⟨OB (T j) + t, by omega, by omega, by rw [hy.2 t ht, e]⟩

end BKMNW

end PlanarFlow
