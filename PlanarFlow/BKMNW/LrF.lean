module

public import PlanarFlow.BKMNW.LrE

/-!
# The children's records of the large split: the meaning of one child's record (pure)

**`lrRec_sem`**: from the compactions of the flags of a child `X ⊆ P` (and of its piece map) over
an enumeration `g` of the parent's piece, the arrays written by `lrOneB` (`GP'`, `RP'`, `HP'`,
`KP'`, `VP'`, `FX'` as for `recL_arr`, and the state array `SP'[CI i] = CI (CN i)` on the darts of
the child's core piece map, where `g (CN i) = st' (g i)`), the header `n_X | 0 | bb`: the record
`RecAt` of the call `y` with `y.1 = ds.dec S T X y.2.1 st' (decide (bb = 1))` — a record of
phase `0` with the state `st'`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit WordRAM WordRAM.Machine NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable {gid : D → ℕ} {ν : V → ℕ} {S T : Finset V} {ds : DSys M}

set_option maxHeartbeats 1000000 in
/-- **The record of one child of the large split** (see the module docstring). -/
theorem lrRec_sem {y : MCall M} {P X : Finset D} {g : ℕ → D} {n : ℕ} {st' : Perm D} {bb : ℕ}
    (hg_inj : ∀ i < n, ∀ j < n, g i = g j → i = j) (hg_surj : ∀ d ∈ P, ∃ i < n, g i = d)
    (hg_mono : ∀ i j, i < j → j < n → gid (g i) < gid (g j))
    (hXP : X ⊆ P) (hXr : ∀ d ∈ X, M.rev d ∈ X) (hyX : y.1.piece = X)
    (hph : y.1 = ds.dec S T X y.2.1 st' (decide (bb = 1))) (hbb : bb ≤ 1)
    (hstX : ∀ d ∈ pdarts M (core M ds.Q X) y.2.1, st' d ∈ X)
    {CI IX IX2 RPf CN : ℕ → ℕ}
    (hci : ∀ i < n, g i ∈ X → CI i = cnt (fun j => bf (g j ∈ X)) i ∧
      IX (cnt (fun j => bf (g j ∈ X)) i) = i)
    (hix2 : ∀ i < n, g i ∈ pdarts M X y.2.1 →
      IX2 (cnt (fun j => bf (g j ∈ pdarts M X y.2.1)) i) = i)
    (hrp : ∀ i < n, RPf i < n ∧ g (RPf i) = M.rev (g i))
    (hcn : ∀ i < n, g i ∈ pdarts M (core M ds.Q X) y.2.1 → CN i < n ∧ g (CN i) = st' (g i))
    {mem : ℕ → ℕ} {Rp : ℕ}
    (h_n : mem Rp = cnt (fun j => bf (g j ∈ X)) n) (h_0 : mem (Rp + 1) = 0)
    (h_b : mem (Rp + 2) = bb)
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
    (h_sp : ∀ i < n, g i ∈ pdarts M (core M ds.Q X) y.2.1 →
      mem (Rp + 3 + 5 * cnt (fun j => bf (g j ∈ X)) n + CI i) = CI (CN i))
    (h_fx : ∀ k < cnt (fun j => bf (g j ∈ pdarts M X y.2.1)) n,
      mem (Rp + 3 + 6 * cnt (fun j => bf (g j ∈ X)) n + k) = CI (IX2 k)) :
    RecAt M ds gid ν S T y Rp
      (6 * cnt (fun j => bf (g j ∈ X)) n + cnt (fun j => bf (g j ∈ pdarts M X y.2.1)) n + 3)
      mem := by
  set FX := fun j => bf (g j ∈ X) with hFX
  set nX := cnt FX n with hnX
  have hYX : pdarts M X y.2.1 ⊆ X := pdarts_subset _ _
  have hyY : pdarts M y.1.piece y.2.1 = pdarts M X y.2.1 := by rw [hyX]
  have hA : RArr M gid ν S T y (cnt (fun j => bf (g j ∈ pdarts M X y.2.1)) n) nX Rp
      (fun k => g (IX k)) mem :=
    recL_arr M hg_inj hg_surj hg_mono hXP hYX hXr hyX hyY hci hix2 hrp h_gp h_rp h_hp h_kp
      h_vp h_fx
  have hcard := hA.card
  have hcardm := hA.card_m
  have hix : ∀ i < n, 0 < FX i → IX (cnt FX i) = i := fun i hi hf => (hci i hi ((bf_pos).1 hf)).2
  refine ⟨?_, nX, fun k => g (IX k), ?_, ⟨h_n, by rw [h_0]; omega, by rw [h_b]; exact hbb, ?_,
    fun _ => hcardm ▸ hA⟩⟩
  · unfold rszC; rw [hcardm, hcard, hyY]; omega
  · rw [h_0]; unfold rszL; rw [hcardm, hyY]; simp only [Nat.ofNat_pos, ↓reduceIte]; omega
  · left
    refine ⟨h_0, st', by rw [hyX, h_b]; exact hph, fun k hk hkB => ?_⟩
    obtain ⟨i, hi, hfi, rfl⟩ := cnt_surj FX n k hk
    dsimp only at hkB ⊢
    rw [hix i hi hfi] at hkB ⊢
    rw [hyX] at hkB
    have hgX : g i ∈ X := (bf_pos).1 hfi
    obtain ⟨c1, c2⟩ := hcn i hi hkB
    have hcX : g (CN i) ∈ X := by rw [c2]; exact hstX _ hkB
    have e1 : CI i = cnt FX i := (hci i hi hgX).1
    have e2 := hci (CN i) c1 hcX
    rw [← e1, h_sp i hi hkB, e2.1, e2.2, c2]
    exact ⟨cnt_lt_of FX c1 ((bf_pos).2 hcX), rfl⟩

end MfDrv

end BKMNW

end PlanarFlow
