module

public import PlanarFlow.Klein.ProgExists
public import PlanarFlow.Klein.Sources

/-!
# Klein's program on the map with the sources copied

`PlanarFlow/Klein/Sources.lean` copies the vertices `t i = tail (g i)` of a face cycle of a plane
map `M` into roots `r i` inside the face (`srcMap hf`), on which the hypotheses of Klein's
algorithm hold, and reads the distances in a piece of `M` from the vertices `t i` off the answers
of the trip (`srcAns`, `srcAns_eq`). This file runs the verified machine program on that map.

* `srcOut W m o`: an answer of the program (`kOut`, on the perturbed lengths) read back: its
  integer part divided by `2^m` (`outNN`), cut off at `W`.
* `src_exec`: **the program `kleinProg` runs on the map with the sources copied** (with the
  perturbed lengths, from an input and a starting configuration as in `klein_exec_exists`) with
  the copies of `t` requested vertices `X i` of `M` as targets, **within
  `2372500000 (N lg N + k t lg N)` steps**, `N = #V + #F + #D` the size of `M` (the map with the
  sources copied has `N + 12 k ≤ 13 N` vertices, faces and darts), and **ends with the answers in
  its output**: for every root `j` and target `i`, the answer `kOut j i` read back (`srcOut`) is
  the distance in the piece of `M` from `t j` to `X i`, none when it is not reached (`odist`).
  For the boundary vertices themselves, `X i = t i` and `t = k`: `k²` path-sum queries,
  `O(k² log N)` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP WordRAM WordRAM.Machine

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {k : ℕ} {g : ℕ → D}
  (hf : FaceCycle M k g) {S : Finset D} {ℓ : D → ℤ}

/-- **An answer of the program on the map with the sources copied, read back**: its integer
part divided by `2^m` (the perturbation, `outNN`), cut off at `W` (`cutW`). -/
noncomputable def srcOut (W : ℤ) (m : ℕ) (o : Option ℝ) : Option ℤ := (outNN m o).bind (cutW W)

/-- `lg (16 n) = lg n + 4` for `n ≥ 1`. -/
lemma lg_sixteen_mul {n : ℕ} (hn : 1 ≤ n) : BKMNW.lg (16 * n) = BKMNW.lg n + 4 := by
  unfold BKMNW.lg
  have e : 16 * n = n * 2 * 2 * 2 * 2 := by ring
  rw [e, Nat.log_mul_base (by norm_num) (by omega), Nat.log_mul_base (by norm_num) (by omega),
    Nat.log_mul_base (by norm_num) (by omega), Nat.log_mul_base (by norm_num) (by omega)]

include hf in
/-- **Klein's program on the map with the sources copied**: for `t` requested vertices `X i` of
`M`, there are an input and a starting configuration (as in `klein_exec_exists`, the targets
the copies of the `X i`) from which `kleinProg` runs within `2372500000 (N lg N + k t lg N)` steps,
`N = #V + #F + #D` the size of `M`, prints nothing, and ends with the answers in its output: for
every `j < k` and `i < t`, the answer `kOut j i` (the real word `OUT[j t + i]` where the natural
word `RB[j t + i]` is `1`), its integer part divided by `2^|D'|` and cut off at `W` (`srcOut`), is
the distance in the piece of `M` from `tail (g j)` to `X i`, none when it is not reached. -/
theorem src_exec (hM : M.IsPlane) (hrot : M.RotTrans) (hnn : ∀ d ∈ S, 0 ≤ ℓ d) (t : ℕ)
    (X : ℕ → V) :
    ∃ (n B : ℕ) (P : Input) (c₀ c' : Config) (steps : ℕ),
      n = 2 * (Fintype.card (SrcV V k) + Fintype.card (SrcF F k) + Fintype.card (SrcD D k)) ∧
      Exec P (B + 16 * (n + 1)) (kleinProg B (Fintype.card (SrcD D k)) n k t) c₀ c' steps ∧
      steps ≤ 2372500000 * ((Fintype.card V + Fintype.card F + Fintype.card D) *
          BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D) +
        k * t * BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D)) ∧
      (∀ j < k, ∀ i < t, srcOut (srcW S ℓ) (Fintype.card (SrcD D k))
        (kOut (Fintype.card (SrcD D k)) n t c' j i) =
          odist (pieceGraph M S ℓ) (M.tail (g j)) (X i)) ∧
      c'.output = c₀.output := by
  have H := (srcMap_hypNN hf hM hrot hnn (srcW_pos hnn).le).hyp
  have hR := srcMap_sameReach hf (S := S) (pert (srcLen ℓ (srcW S ℓ)))
  have hX : ∀ i < t, ¬ IsRoot (srcMap hf) k (srcG hf) (.inl (X i)) := by
    rintro i - ⟨j, hj, hji⟩
    rw [srcTail_srcG hf hj] at hji
    cases hji
  obtain ⟨n, B, P, c₀, c', steps, hn, hE, hs, -, hd, hout⟩ :=
    klein_exec_exists H hR t (fun i => .inl (X i)) hX
  refine ⟨n, B, P, c₀, c', steps, hn, hE, hs.trans ?_, fun j hj i hi => ?_, hout⟩
  · set N := Fintype.card V + Fintype.card F + Fintype.card D with hN
    have hk : k ≤ Fintype.card V := by
      have hinj : Function.Injective fun i : Fin k => M.tail (g i) := fun i j h =>
        Fin.ext (hf.inj _ i.2 _ j.2 h)
      simpa using Fintype.card_le_of_injective _ hinj
    have hN1 : 1 ≤ N := by have := hf.two_le; omega
    have e : Fintype.card (SrcV V k) + Fintype.card (SrcF F k) + Fintype.card (SrcD D k) =
        N + 12 * k := by
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
        card_srcKind, hN]
      ring
    rw [e]
    have h13 : N + 12 * k ≤ 13 * N := by omega
    have hl : BKMNW.lg (N + 12 * k) ≤ 5 * BKMNW.lg N := by
      have h1 := BKMNW.lg_mono (show N + 12 * k ≤ 16 * N by omega)
      have h2 := lg_sixteen_mul hN1
      have h3 := BKMNW.one_le_lg N
      omega
    have h4 : (N + 12 * k) * BKMNW.lg (N + 12 * k) ≤ 13 * N * (5 * BKMNW.lg N) :=
      Nat.mul_le_mul h13 hl
    have h5 : k * t * BKMNW.lg (N + 12 * k) ≤ k * t * (5 * BKMNW.lg N) :=
      Nat.mul_le_mul_left _ hl
    have e4 : 13 * N * (5 * BKMNW.lg N) = 65 * (N * BKMNW.lg N) := by ring
    have e5 : k * t * (5 * BKMNW.lg N) = 5 * (k * t * BKMNW.lg N) := by ring
    omega
  · rw [hd j hj i hi, ← srcAns_eq hf hM hrot hnn hj]
    unfold srcOut srcAns kleinNN
    rw [outNN_map, ← kleinAns_eq H hR]

end Klein

end PlanarFlow
