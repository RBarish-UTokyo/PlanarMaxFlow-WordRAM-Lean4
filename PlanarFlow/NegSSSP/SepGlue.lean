module

public import PlanarFlow.NegSSSP.FaceSplitOf
public import PlanarSeparator.Machine.SepOut

/-!
# The split of a connected piece from the output of Miller's program

The separator field `NegCosts.sep` of the recursion for negative lengths charges the split of a
piece (`PlanarFlow.NegSSSP.SplitF`), whose large-component case is
`PlanarFlow.NegSSSP.exists_cycle_cut`: Miller's theorem on the stellar subdivision `kst N K` of
the piece map `kmap N K`, weighing the darts of `K`.

* `sep_split`: the program `PlanarSeparator.MillerProg.sepOut` turns a separator of the twice
  subdivided piece map (the output of steps 9–10) into a mark per dart of the piece map, and the
  two parts `side N K Z`, `side N K Zᶜ` meet the conclusion of `exists_cycle_cut`
  (`exists_cycle_cut_of`).
* `sep_run_split`: the whole program `sepRun prog` from the plain encoding of `kmap N K` with
  the flags of `K` (`flK`), for any program of steps 1–10 meeting
  `PlanarSeparator.MillerProg.Spec10`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv Orbit CombMap Relation PlanarSeparator PlanarSeparator.Map
  PlanarSeparator.StDart PlanarSeparator.MillerProg BKMNW WordRAM WordRAM.Machine

section Glue

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]

variable {N : CombMap D V F}

variable (N) in
/-- The flags of the darts of the piece map of `K`: `1` on the darts of `K`. -/
def flK (K : Finset D) : SDart (rcl N K) → ℕ := fun x => if x.1 ∈ K then 1 else 0

lemma flK_le (K : Finset D) (x : SDart (rcl N K)) : flK N K x ≤ 1 := by
  unfold flK; split_ifs <;> omega

lemma flagS_flK (K : Finset D) : flagS (flK N K) = (K.subtype (· ∈ rcl N K)).image old := by
  unfold flagS flK
  congr 1
  ext x
  simp

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The split of a connected piece on the machine, from the separator of steps 9–10.** Let
`K` be a connected piece of kept darts (as in `exists_cycle_cut`), its piece map `kmap N K`
numbered by `c` (darts), `vn` (vertices) and `fn` (faces), and `C'`, `Z'` a simple cycle
separator of the twice subdivided piece map for the weights `wSt c (flK N K)` of Miller's
program (the output of steps 9–10, at most `6 ⌊√n⌋ + 4` darts), its triangles marked at `bZ`,
and the reversals of `kst N K` at `bA`. Then `sepOut` ends within `105 m + 30` steps with a mark
per dart of the piece map at `bZf` — the dart `d` of `K` is in the first part iff its mark is
`1` — and the parts `side N K Z`, `side N K Zᶜ` meet the conclusion of `exists_cycle_cut`
(`exists_cycle_cut_of`): they split `K`, with at most `(2 #K + 12 ℓ) / 3` darts each and at
most `ℓ ≤ 6 √(12 #K) + 4` shared vertices, lying on one face of a plane map of at most `18 #K`
vertices, faces and darts for each part with any rest sharing no vertex with `K`. -/
theorem sep_split (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {K : Finset D} (hKr : K ⊆ reps N) (hK0 : K.Nonempty) (hK : DConn N K)
    {m nV nF : ℕ} (c : SDart (rcl N K) ≃ Fin m) (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV)
    (fn : (kmap N K).Face ≃ Fin nF) (hm1 : 1 ≤ m)
    {C' : (kst N K).stellar.SCycle} {Z' : Finset (kst N K).stellar.Face}
    (hk' : C'.k ≤ 6 * Nat.sqrt (nV + nF + m) + 4)
    (hsep' : IsCycleSep C' Z' (sideIn C' Z') (sideOut C' Z'))
    (hin' : ∑ x ∈ sideIn C' Z', wR (wSt (kmap N K) c (flK N K)) x ≤ 2 / 3)
    (hout' : ∑ x ∈ sideOut C' Z', wR (wSt (kmap N K) c (flK N K)) x ≤ 2 / 3)
    {W : ℕ} {P : Input} {bZ bMj bA bZf : ℕ}
    (hd : (bMj + m ≤ bZ ∨ bZ + 3 * m ≤ bMj) ∧ (bMj + m ≤ bA ∨ bA + 3 * m ≤ bMj) ∧
      (bMj + m ≤ bZf ∨ bZf + m ≤ bMj) ∧ (bZf + m ≤ bZ ∨ bZ + 3 * m ≤ bZf) ∧
      (bZf + m ≤ bA ∨ bA + 3 * m ≤ bZf))
    (hW : bZ + 3 * m ≤ W ∧ bMj + m ≤ W ∧ bA + 3 * m ≤ W ∧ bZf + m ≤ W)
    (c₀ : Config) (hc : WordsBounded W c₀)
    (h370 : c₀.nreg 370 = m) (h371 : c₀.nreg 371 = bZ) (h372 : c₀.nreg 372 = bMj)
    (h373 : c₀.nreg 373 = bA) (h374 : c₀.nreg 374 = bZf)
    (hzm : ∀ G, c₀.nmem (bZ + (kst N K).stFn ((kmap N K).stCode c) G) =
      if G ∈ Z' then 1 else 0)
    (hA₁ : ∀ x, c₀.nmem (bA + (kmap N K).stCode c x) =
      (kmap N K).stCode c ((kst N K).α x)) :
    ∃ c' t, Exec P W sepOut c₀ c' t ∧ t ≤ 105 * m + 30 ∧
      ∃ Z : Finset (kst N K).Face,
        (∀ d (h : d ∈ rcl N K), d ∈ K → (d ∈ side N K Z ↔ c'.nmem (bZf + c ⟨d, h⟩) = 1)) ∧
        side N K Z ∪ side N K Zᶜ = K ∧ Disjoint (side N K Z) (side N K Zᶜ) ∧
        ∃ ℓ, ℓ ≤ 6 * Nat.sqrt (12 * K.card) + 4 ∧
          3 * (side N K Z).card ≤ 2 * K.card + 12 * ℓ ∧
          3 * (side N K Zᶜ).card ≤ 2 * K.card + 12 * ℓ ∧
          (bdry N (side N K Z) (side N K Zᶜ)).card ≤ ℓ ∧
          ∀ R : Finset D, Disjoint (verts N R) (verts N K) →
            OneFace N (side N K Z ∪ R) (bdry N (side N K Z) (side N K Zᶜ)) (18 * K.card) ℓ ∧
            OneFace N (side N K Zᶜ ∪ R) (bdry N (side N K Z) (side N K Zᶜ)) (18 * K.card) ℓ := by
  have hS := kmap_isPlane hM hrot hface hK0 hK
  have hl := kmap_loopless hrot hKr
  obtain ⟨c', t, e, ht, C, Z, hmk, hk, hsep, hin, hout, -, -⟩ :=
    sepOut_sep (P := P) (W := W) (kmap N K) c vn fn hm1 hS hl (flK_le K) hk' hsep' hin' hout'
      hd hW c₀ hc h370 h371 h372 h373 h374 hzm hA₁
  rw [flagS_flK] at hin hout
  have hcardP : Fintype.card (SVert (kσ N K) (rcl N K) ⊕ (kmap N K).Face) = nV + nF := by
    rw [Fintype.card_sum, Fintype.card_congr vn, Fintype.card_congr fn, Fintype.card_fin,
      Fintype.card_fin]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := exists_cycle_cut_of hM hrot hface hKr hK0 hK
    (C := C) (Z := Z) (by rw [hcardP]; exact hk) hsep hin hout
  refine ⟨c', t, e, ht, Z, fun d h hdK => ?_, h1, h2, C.k, h3, h4, h5, h6, h7⟩
  rw [mem_side]
  have := hmk ((kmap N K).stTri ⟨d, h⟩)
  rw [stFn_stTri] at this
  rw [this]
  constructor
  · rintro ⟨-, h', hZ⟩
    exact ite_eq_left hZ
  · intro h'
    refine ⟨hdK, h, ?_⟩
    by_contra hZ
    rw [ite_eq_right (show (kmap N K).stTri ⟨d, h⟩ ∉ Z from hZ)] at h'
    exact absurd h' (by omega)

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The split of a connected piece by the machine, with steps 1–10 as a parameter.** From the
plain encoding (`Enc`) of the piece map `kmap N K` of a connected piece `K` (`m ≥ 1` darts, `nV`
vertices, `nF` faces) at `B₀`, with the flags of the darts of `K` at `B₀ + 5 m`, and any
program `prog` for steps 1–10 meeting `Spec10` within `T` steps, `sepRun prog` ends within
`326 m + 5 (nV + nF) + 4 log₂ n + T + 149` steps with a mark per dart of the piece map at
`B₀ + 22 m` (a dart of `K` is in the first part iff its mark is `1`), and the two parts meet
the conclusion of `exists_cycle_cut`. -/
theorem sep_run_split (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {K : Finset D} (hKr : K ⊆ reps N) (hK0 : K.Nonempty) (hK : DConn N K)
    {m nV nF : ℕ} (c : SDart (rcl N K) ≃ Fin m) (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV)
    (fn : (kmap N K).Face ≃ Fin nF) (hm1 : 1 ≤ m)
    {W : ℕ} {P : Input} {B₀ T : ℕ} {prog : WordRAM.Machine.Stmt} {c₀ : Config}
    (hE : Enc (kmap N K) c vn fn c₀.nmem B₀ (B₀ + m) (B₀ + 2 * m) (B₀ + 3 * m) (B₀ + 4 * m))
    (hfl : ∀ d, c₀.nmem (B₀ + 5 * m + c d) = flK N K d)
    (hB : aEnd (3 * m) (nV + nF + m) ≤ B₀) (hW : B₀ + 23 * m + nV + nF + 2 ≤ W)
    (hc : WordsBounded W c₀) (h390 : c₀.nreg 390 = m) (h391 : c₀.nreg 391 = nV)
    (h392 : c₀.nreg 392 = nF) (h393 : c₀.nreg 393 = B₀)
    (hX : Spec10 (kmap N K) c vn fn (flK N K) B₀ T prog P W) :
    ∃ c' t, Exec P W (sepRun prog) c₀ c' t ∧
      t ≤ 221 * m + 5 * (nV + nF) + 4 * Nat.log 2 (nV + nF + m) + 110 + T + 9 +
        (105 * m + 30) ∧
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
  have hS := kmap_isPlane hM hrot hface hK0 hK
  have hl := kmap_loopless hrot hKr
  obtain ⟨c', t, e, ht, C, Z, hmk, hk, hsep, hin, hout⟩ :=
    sepRun_exec (P := P) (W := W) (kmap N K) c vn fn (flK N K) hm1 hS hl (flK_le K) hE hfl hB
      hW hc h390 h391 h392 h393 hX
  rw [flagS_flK] at hin hout
  have hcardP : Fintype.card (SVert (kσ N K) (rcl N K) ⊕ (kmap N K).Face) = nV + nF := by
    rw [Fintype.card_sum, Fintype.card_congr vn, Fintype.card_congr fn, Fintype.card_fin,
      Fintype.card_fin]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := exists_cycle_cut_of hM hrot hface hKr hK0 hK
    (C := C) (Z := Z) (by rw [hcardP]; exact hk) hsep hin hout
  refine ⟨c', t, e, ht, Z, fun d h hdK => ?_, h1, h2, C.k, h3, h4, h5, h6, h7⟩
  rw [mem_side]
  have := hmk ((kmap N K).stTri ⟨d, h⟩)
  rw [stFn_stTri] at this
  rw [this]
  constructor
  · rintro ⟨-, h', hZ⟩
    exact ite_eq_left hZ
  · intro h'
    refine ⟨hdK, h, ?_⟩
    by_contra hZ
    rw [ite_eq_right (show (kmap N K).stTri ⟨d, h⟩ ∉ Z from hZ)] at h'
    exact absurd h' (by omega)

end Glue

end NegSSSP

end PlanarFlow
