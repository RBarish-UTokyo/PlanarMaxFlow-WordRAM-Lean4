module

public import PlanarFlow.BKMNW.SmXB4

/-!
# The small separator program: the meaning of the children's records

Pure lemmas turning the machine's outputs of stage B into the records `LayR` of the children:

* `cfV_bf` (the flag `cfV`: in `X` and not inside a hole), `cnt_bf_card` (the count of the
  flagged darts of an enumeration is the size of the set);
* **`recL_arr`**: from a compaction `CI`/`IX` of the darts of `X` in an enumeration `g` of `P`
  (increasing in `gid`), a compaction `IX2` of the darts of `Y ⊆ X`, and the arrays written in
  the memory, the record arrays `RArr` of a call with piece `X` and piece map `Y`, enumerated by
  `g ∘ IX`;
* `recR_leaf` (the header of a leaf is its record).
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

open Finset Function Equiv Orbit WordRAM WordRAM.Machine NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable {gid : D → ℕ} {ν : V → ℕ} {S T : Finset V} {ds : DSys M}

lemma cfV_bf (p : Prop) [Decidable p] (a b : ℕ) :
    cfV (bf p) a b = bf (p ∧ ¬ (0 < a ∧ a = b)) := by
  have key : (1 - (1 - a)) + (1 - ((a - b) + (b - a))) - 1 = if 0 < a ∧ a = b then 1 else 0 := by
    split_ifs with h <;> omega
  unfold cfV
  rw [key]
  unfold bf
  by_cases hp : p <;> by_cases h : 0 < a ∧ a = b <;> simp [hp, h] <;> split_ifs <;> omega

/-- **The count of the flagged darts is the size of the set** (`g` injective on `[0, n)`, onto a
superset of `X`). -/
lemma cnt_bf_card {g : ℕ → D} {n : ℕ} (hinj : ∀ i < n, ∀ j < n, g i = g j → i = j) {X : Finset D}
    (hX : ∀ y ∈ X, ∃ i < n, g i = y) : cnt (fun j => bf (g j ∈ X)) n = X.card := by
  unfold cnt
  have e : X = ((range n).filter fun j => 0 < bf (g j ∈ X)).image g := by
    ext y
    simp only [mem_image, mem_filter, mem_range, bf_pos]
    constructor
    · intro hy; obtain ⟨i, hi, rfl⟩ := hX y hy; exact ⟨i, ⟨hi, hy⟩, rfl⟩
    · rintro ⟨i, ⟨-, hi⟩, rfl⟩; exact hi
  have hc := card_image_of_injOn (s := (range n).filter fun j => 0 < bf (g j ∈ X)) (f := g)
    (fun i hi j hj h => by
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hi hj
      exact hinj i hi.1 j hj.1 h)
  rw [← e] at hc
  exact hc.symm

/-- The positions of a compaction are increasing. -/
lemma cnt_ix_mono {F : ℕ → ℕ} {n : ℕ} {IX : ℕ → ℕ}
    (hix : ∀ i < n, 0 < F i → IX (cnt F i) = i) {k k' : ℕ} (hkk : k < k') (hk' : k' < cnt F n) :
    IX k < IX k' ∧ IX k' < n ∧ 0 < F (IX k) ∧ 0 < F (IX k') ∧ cnt F (IX k) = k ∧
      cnt F (IX k') = k' := by
  obtain ⟨i, hi, hfi, rfl⟩ := cnt_surj F n k (by omega)
  obtain ⟨i', hi', hfi', rfl⟩ := cnt_surj F n _ hk'
  rw [hix i hi hfi, hix i' hi' hfi']
  refine ⟨?_, hi', hfi, hfi', rfl, rfl⟩
  by_contra hc
  have := cnt_mono F (show i' ≤ i by omega)
  omega

variable (M) in
/-- **The arrays of the left child's record from the compactions** (see the module docstring). -/
theorem recL_arr {y : MCall M} {P X Y : Finset D} {g : ℕ → D} {n : ℕ}
    (hg_inj : ∀ i < n, ∀ j < n, g i = g j → i = j) (hg_surj : ∀ d ∈ P, ∃ i < n, g i = d)
    (hg_mono : ∀ i j, i < j → j < n → gid (g i) < gid (g j))
    (hXP : X ⊆ P) (hYX : Y ⊆ X) (hXr : ∀ d ∈ X, M.rev d ∈ X)
    (hyX : y.1.piece = X) (hyY : pdarts M y.1.piece y.2.1 = Y)
    {CI IX IX2 RPf : ℕ → ℕ}
    (hci : ∀ i < n, g i ∈ X → CI i = cnt (fun j => bf (g j ∈ X)) i ∧
      IX (cnt (fun j => bf (g j ∈ X)) i) = i)
    (hix2 : ∀ i < n, g i ∈ Y → IX2 (cnt (fun j => bf (g j ∈ Y)) i) = i)
    (hrp : ∀ i < n, RPf i < n ∧ g (RPf i) = M.rev (g i))
    {mem : ℕ → ℕ} {Rp : ℕ}
    (h_gp : ∀ k < cnt (fun j => bf (g j ∈ X)) n, mem (Rp + 3 + k) = gid (g (IX k)))
    (h_rp : ∀ i < n, g i ∈ X →
      mem (Rp + 3 + cnt (fun j => bf (g j ∈ X)) n + CI i) = CI (RPf i))
    (h_hp : ∀ k < cnt (fun j => bf (g j ∈ X)) n,
      mem (Rp + 3 + 2 * cnt (fun j => bf (g j ∈ X)) n + k) = hlab y.2.1 (M.tail (g (IX k))))
    (h_kp : ∀ k < cnt (fun j => bf (g j ∈ X)) n,
      mem (Rp + 3 + 3 * cnt (fun j => bf (g j ∈ X)) n + k) =
        lrk S T (hunion y.2.1) (M.tail (g (IX k))))
    (h_vp : ∀ k < cnt (fun j => bf (g j ∈ X)) n,
      mem (Rp + 3 + 4 * cnt (fun j => bf (g j ∈ X)) n + k) = ν (M.tail (g (IX k))))
    (h_fx : ∀ k < cnt (fun j => bf (g j ∈ Y)) n,
      mem (Rp + 3 + 6 * cnt (fun j => bf (g j ∈ X)) n + k) = CI (IX2 k)) :
    RArr M gid ν S T y (cnt (fun j => bf (g j ∈ Y)) n) (cnt (fun j => bf (g j ∈ X)) n) Rp
      (fun k => g (IX k)) mem := by
  set FX := fun j => bf (g j ∈ X) with hFX
  set FY := fun j => bf (g j ∈ Y) with hFY
  have hix : ∀ i < n, 0 < FX i → IX (cnt FX i) = i := fun i hi hf =>
    (hci i hi ((bf_pos).1 hf)).2
  have hix2' : ∀ i < n, 0 < FY i → IX2 (cnt FY i) = i := fun i hi hf =>
    hix2 i hi ((bf_pos).1 hf)
  -- every position of the compaction is a flagged dart
  have pos : ∀ k < cnt FX n, IX k < n ∧ g (IX k) ∈ X ∧ cnt FX (IX k) = k := fun k hk => by
    obtain ⟨i, hi, hfi, rfl⟩ := cnt_surj FX n k hk
    rw [hix i hi hfi]; exact ⟨hi, (bf_pos).1 hfi, rfl⟩
  have pos2 : ∀ k < cnt FY n, IX2 k < n ∧ g (IX2 k) ∈ Y ∧ cnt FY (IX2 k) = k := fun k hk => by
    obtain ⟨i, hi, hfi, rfl⟩ := cnt_surj FY n k hk
    rw [hix2' i hi hfi]; exact ⟨hi, (bf_pos).1 hfi, rfl⟩
  have cntlt : ∀ i < n, g i ∈ X → cnt FX i < cnt FX n := fun i hi hx =>
    cnt_lt_of FX hi ((bf_pos).2 hx)
  -- the child's index of a flagged dart
  have ciX : ∀ i < n, g i ∈ X → CI i < cnt FX n ∧ g (IX (CI i)) = g i := fun i hi hx => by
    obtain ⟨h1, h2⟩ := hci i hi hx
    rw [h1, h2]; exact ⟨cntlt i hi hx, rfl⟩
  refine ⟨fun k hk => ?_, fun d hd => ?_, fun k k' hkk hk' => ?_, fun k hk => h_gp k hk,
    fun k hk => ?_, fun k hk => h_hp k hk, fun k hk => h_kp k hk, fun k hk => h_vp k hk,
    fun k hk => ?_, fun k hk => ?_, fun d hd => ?_, fun k k' hkk hk' => ?_⟩
  · rw [hyX]; exact (pos k hk).2.1
  · rw [hyX] at hd
    obtain ⟨i, hi, rfl⟩ := hg_surj d (hXP hd)
    exact ⟨cnt FX i, cntlt i hi hd, by rw [hix i hi ((bf_pos).2 hd)]⟩
  · obtain ⟨a1, a2, -⟩ := cnt_ix_mono hix hkk hk'
    exact hg_mono _ _ a1 a2
  · obtain ⟨p1, p2, p3⟩ := pos k hk
    obtain ⟨h1, h2⟩ := hci _ p1 p2
    rw [← p3, ← h1, h_rp _ p1 p2]
    obtain ⟨r1, r2⟩ := hrp _ p1
    have hrx : g (RPf (IX k)) ∈ X := by rw [r2]; exact hXr _ p2
    obtain ⟨c1, c2⟩ := ciX _ r1 hrx
    refine ⟨c1, ?_⟩
    rw [c2, r2, (ciX _ p1 p2).2]
  · obtain ⟨p1, p2, -⟩ := pos2 k hk
    rw [h_fx k hk]; exact (ciX _ p1 (hYX p2)).1
  · obtain ⟨p1, p2, -⟩ := pos2 k hk
    rw [h_fx k hk, (ciX _ p1 (hYX p2)).2, hyY]; exact p2
  · rw [hyY] at hd
    obtain ⟨i, hi, rfl⟩ := hg_surj d (hXP (hYX hd))
    refine ⟨cnt FY i, cnt_lt_of FY hi ((bf_pos).2 hd), ?_⟩
    rw [h_fx _ (cnt_lt_of FY hi ((bf_pos).2 hd)), hix2' i hi ((bf_pos).2 hd),
      (ciX i hi (hYX hd)).2]
  · obtain ⟨a1, a2, f1, f2, -⟩ := cnt_ix_mono hix2' hkk hk'
    have hk : k < cnt FY n := by omega
    rw [h_fx k hk, h_fx k' hk', (ciX _ (by omega) (hYX ((bf_pos).1 f1))).2,
      (ciX _ a2 (hYX ((bf_pos).1 f2))).2]
    exact hg_mono _ _ a1 a2

end MfDrv

end BKMNW

end PlanarFlow
