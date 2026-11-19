module

public import PlanarFlow.NegSSSP.SepGlue
public import PlanarSeparator.Machine.SepProg10

/-!
# The split of a large connected piece entirely on the machine

`PlanarFlow.NegSSSP.sep_run_split` realizes the large-component split of the recursion for
negative lengths (`exists_cycle_cut`) by `sepRun prog` for any program `prog` of steps 1–10
meeting `PlanarSeparator.MillerProg.Spec10`. Miller's whole program meets it
(`PlanarSeparator.MillerProg.prog10_spec10`, `prog10 = setup10 ; millerFull ; marks01`), so:

* **`sep_run_split_full`**: `sepRun prog10`, from the plain encoding of the piece map `kmap N K`
  of a connected piece `K` with the flags of `K`, ends within
  `(1746 |K| + 156) (log₂ |K| + 3) + 16772 |K| + 1849` steps (and within the bound in `m`,
  `nV`, `nF` of `sep_run_split` with `T = T10 m (nV + nF + m)`) with a mark per dart of the
  piece, and the two parts meet the conclusion of `exists_cycle_cut`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv Orbit CombMap Relation PlanarSeparator PlanarSeparator.Map
  PlanarSeparator.StDart PlanarSeparator.MillerProg BKMNW WordRAM WordRAM.Machine

section Full

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]

variable {N : CombMap D V F}

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The split of a large connected piece entirely on the machine.** From the plain encoding
(`Enc`) of the piece map `kmap N K` of a connected piece `K` (`m ≥ 1` darts, `nV` vertices,
`nF` faces) at `B₀ ≥ aEnd10 (3 m) (nV + nF + m)`, with the flags of the darts of `K` at
`B₀ + 5 m`, `sepRun prog10` (input, Miller's whole program, output) ends within
`(1746 |K| + 156) (log₂ |K| + 3) + 16772 |K| + 1849` steps with a mark per dart of the piece map
at `B₀ + 22 m` (a dart of `K` is in the first part iff its mark is `1`), and the two parts meet
the conclusion of `exists_cycle_cut`. -/
theorem sep_run_split_full (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {K : Finset D} (hKr : K ⊆ reps N) (hK0 : K.Nonempty) (hK : DConn N K)
    {m nV nF : ℕ} (c : SDart (rcl N K) ≃ Fin m) (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV)
    (fn : (kmap N K).Face ≃ Fin nF) (hm1 : 1 ≤ m)
    {W : ℕ} {P : Input} {B₀ : ℕ} {c₀ : Config}
    (hE : Enc (kmap N K) c vn fn c₀.nmem B₀ (B₀ + m) (B₀ + 2 * m) (B₀ + 3 * m) (B₀ + 4 * m))
    (hfl : ∀ d, c₀.nmem (B₀ + 5 * m + c d) = flK N K d)
    (hB : aEnd10 (3 * m) (nV + nF + m) ≤ B₀) (hW : B₀ + 23 * m + nV + nF + 2 ≤ W)
    (hc : WordsBounded W c₀) (h390 : c₀.nreg 390 = m) (h391 : c₀.nreg 391 = nV)
    (h392 : c₀.nreg 392 = nF) (h393 : c₀.nreg 393 = B₀) :
    ∃ c' t, Exec P W (sepRun prog10) c₀ c' t ∧
      t ≤ 221 * m + 5 * (nV + nF) + 4 * Nat.log 2 (nV + nF + m) + 110 +
        T10 m (nV + nF + m) + 9 + (105 * m + 30) ∧
      t ≤ (1746 * K.card + 156) * (Nat.log 2 K.card + 3) + 16772 * K.card + 1849 ∧
      ∃ Z : Finset (kst N K).Face,
        (∀ d (h : d ∈ rcl N K), d ∈ K →
          (d ∈ side N K Z ↔ c'.nmem (B₀ + 22 * m + c ⟨d, h⟩) = 1)) ∧
        side N K Z ∪ side N K Zᶜ = K ∧ Disjoint (side N K Z) (side N K Zᶜ) ∧
        ∃ ℓ, ℓ ≤ 6 * Nat.sqrt (12 * K.card) + 4 ∧
          3 * (side N K Z).card ≤ 2 * K.card + 12 * ℓ ∧
          3 * (side N K Zᶜ).card ≤ 2 * K.card + 12 * ℓ ∧
          (bdry N (side N K Z) (side N K Zᶜ)).card ≤ ℓ ∧
          ∀ R : Finset D, Disjoint (verts N R) (verts N K) →
            OneFace N (side N K Z ∪ R) (bdry N (side N K Z) (side N K Zᶜ)) (18 * K.card) ℓ ∧
            OneFace N (side N K Zᶜ ∪ R) (bdry N (side N K Z) (side N K Zᶜ)) (18 * K.card) ℓ := by
  obtain ⟨d₀, hd₀⟩ := hK0
  have hd₀' : d₀ ∈ rcl N K := subset_rcl K hd₀
  have hfl0 : 0 < flK N K ⟨d₀, hd₀'⟩ := by simp [flK, hd₀]
  have hX := prog10_spec10 (P := P) (W := W) (kmap N K) c vn fn (flK N K) hm1
    (kmap_isPlane hM hrot hface ⟨d₀, hd₀⟩ hK) (kmap_loopless hrot hKr) (flK_le K) hfl0 hB
    (by omega)
  have hB' : aEnd (3 * m) (nV + nF + m) ≤ B₀ := by unfold aEnd10 at hB; omega
  obtain ⟨c', t, e, ht, Z, h1, h2, h3, ℓ, h4⟩ :=
    sep_run_split hM hrot hface hKr ⟨d₀, hd₀⟩ hK c vn fn hm1 hE hfl hB' hW hc h390 h391 h392
      h393 hX
  refine ⟨c', t, e, ht, ?_, Z, h1, h2, h3, ℓ, h4⟩
  -- the sizes in terms of `|K|`
  set κ := K.card with hκ
  have hκ1 : 1 ≤ κ := card_pos.2 ⟨d₀, hd₀⟩
  have hc1 : Fintype.card (SVert (kσ N K) (rcl N K)) + Fintype.card (kmap N K).Face ≤
      2 * (rcl N K).card := card_pieceSep_le _ _
  have hc2 := card_rcl_le (N := N) K
  have hcm : m = (rcl N K).card := by
    rw [← Fintype.card_fin m, ← Fintype.card_congr c]; exact Fintype.card_coe _
  have hcV : nV = Fintype.card (SVert (kσ N K) (rcl N K)) := by
    rw [← Fintype.card_fin nV, ← Fintype.card_congr vn]
  have hcF : nF = Fintype.card (kmap N K).Face := by
    rw [← Fintype.card_fin nF, ← Fintype.card_congr fn]
  have hm2 : m ≤ 2 * κ := by omega
  have hn6 : nV + nF + m ≤ 6 * κ := by omega
  have hlog : Nat.log 2 (nV + nF + m) ≤ Nat.log 2 κ + 3 := by
    have h8 : Nat.log 2 (κ * 2 * 2 * 2) = Nat.log 2 κ + 3 := by
      rw [Nat.log_mul_base (by norm_num) (by omega), Nat.log_mul_base (by norm_num) (by omega),
        Nat.log_mul_base (by norm_num) (by omega)]
    rw [← h8]; exact Nat.log_mono_right (by omega)
  have hmul : (693 * m + 60 * (nV + nF + m) + 156) * Nat.log 2 (nV + nF + m) ≤
      (1746 * κ + 156) * (Nat.log 2 κ + 3) := Nat.mul_le_mul (by omega) hlog
  unfold T10 at ht
  have hexp : (693 * m + 60 * (nV + nF + m) + 156) * Nat.log 2 (nV + nF + m) =
      (693 * m + 60 * (nV + nF + m) + 152) * Nat.log 2 (nV + nF + m) +
        4 * Nat.log 2 (nV + nF + m) := by ring
  clear * - ht hmul hexp hm2 hn6
  generalize (693 * m + 60 * (nV + nF + m) + 152) * Nat.log 2 (nV + nF + m) = P₁ at ht hexp
  generalize (693 * m + 60 * (nV + nF + m) + 156) * Nat.log 2 (nV + nF + m) = P₂ at hmul hexp
  generalize Nat.log 2 (nV + nF + m) = A at ht hexp
  generalize (1746 * κ + 156) * (Nat.log 2 κ + 3) = Q at hmul ⊢
  omega

end Full

end NegSSSP

end PlanarFlow
