module

public import PlanarFlow.BKMNW.SmXD

/-!
# The small separator program and its specification

**`sepSm = smXA ; smXB1 ; smXB2`**, room `smR n m k = 22 m + 24 n + 8 k + 30`.

* `recsOut_sm` (pure): the outputs of stage B are the children's records `RecsOut` at a node of
  `smD` (left child `smD` of its piece with the child's holes, phase `1`; right child a leaf,
  phase `2`);
* **`sepSm_exec`**: at a node call `(.node l r π, Hs, σ)` with `smD pk S T P Hs = .node l r π`
  (`P = l.piece ∪ r.piece`, `PkMin gid pk`, a loopless map, `ν` injective), from the frame and
  the record (`RArr`, `n` darts), within `560 n + 27 m + 50 k + 520` steps: the six outputs of
  `SepPSpec` at `Sb` and the children's records `RecsOut` from `r6501`; memory and reals below
  `Sb`, the registers `3000 … 3012` and the output kept.
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

open Finset Function Equiv Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable {gid : D → ℕ} {ν : V → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {ds : DSys M}

/-- **The small separator program.** -/
def sepSm : Stmt := .seq smXA (.seq smXB1 smXB2)

/-- The room of the small separator program. -/
def smR (n m k : ℕ) : ℕ := 22 * m + 24 * n + 8 * k + 30

set_option maxHeartbeats 2000000 in
/-- **The children's records at a node of `smD`, from the outputs of stage B** (pure). -/
theorem recsOut_sm {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D}
    {g : ℕ → D} {n : ℕ} {mem : ℕ → ℕ} {Xb lo hi : ℕ}
    (hg_inj : ∀ i < n, ∀ j < n, g i = g j → i = j)
    (hg_surj : ∀ d ∈ l.piece ∪ r.piece, ∃ i < n, g i = d)
    (hg_mono : ∀ i j, i < j → j < n → gid (g i) < gid (g j))
    (hlrev : ∀ d ∈ l.piece, M.rev d ∈ l.piece)
    (hlsm : l = smD M ds.pk S T l.piece (childHoles Hs π.path.mverts)) {Q : Finset D}
    (hrl : r = .leaf Q)
    {CI IX IX2 RPf : ℕ → ℕ}
    (hci : ∀ i < n, g i ∈ l.piece → CI i = cnt (fun j => bf (g j ∈ l.piece)) i ∧
      IX (cnt (fun j => bf (g j ∈ l.piece)) i) = i)
    (hix2 : ∀ i < n, g i ∈ pdarts M l.piece (childHoles Hs π.path.mverts) →
      IX2 (cnt (fun j => bf (g j ∈ pdarts M l.piece (childHoles Hs π.path.mverts))) i) = i)
    (hrp : ∀ i < n, RPf i < n ∧ g (RPf i) = M.rev (g i))
    (hlo : lo ≤ Xb)
    (hhi : Xb + 2 + (6 * cnt (fun j => bf (g j ∈ l.piece)) n +
      cnt (fun j => bf (g j ∈ pdarts M l.piece (childHoles Hs π.path.mverts))) n + 3) + 3 ≤ hi)
    (m0 : mem Xb = 6 * cnt (fun j => bf (g j ∈ l.piece)) n +
      cnt (fun j => bf (g j ∈ pdarts M l.piece (childHoles Hs π.path.mverts))) n + 3)
    (m1 : mem (Xb + 1) = 3) (m2 : mem (Xb + 2) = cnt (fun j => bf (g j ∈ l.piece)) n)
    (m3 : mem (Xb + 2 + 1) = 1) (m4 : mem (Xb + 2 + 2) = 0)
    (m5 : mem (Xb + 2 + mem Xb) = 0) (m6 : mem (Xb + 2 + mem Xb + 1) = 2)
    (m7 : mem (Xb + 2 + mem Xb + 2) = 0)
    (h_gp : ∀ k < cnt (fun j => bf (g j ∈ l.piece)) n, mem (Xb + 2 + 3 + k) = gid (g (IX k)))
    (h_rp : ∀ i < n, g i ∈ l.piece →
      mem (Xb + 2 + 3 + cnt (fun j => bf (g j ∈ l.piece)) n + CI i) = CI (RPf i))
    (h_hp : ∀ k < cnt (fun j => bf (g j ∈ l.piece)) n,
      mem (Xb + 2 + 3 + 2 * cnt (fun j => bf (g j ∈ l.piece)) n + k) =
        hlab (childHoles Hs π.path.mverts) (M.tail (g (IX k))))
    (h_kp : ∀ k < cnt (fun j => bf (g j ∈ l.piece)) n,
      mem (Xb + 2 + 3 + 3 * cnt (fun j => bf (g j ∈ l.piece)) n + k) =
        lrk S T (hunion (childHoles Hs π.path.mverts)) (M.tail (g (IX k))))
    (h_vp : ∀ k < cnt (fun j => bf (g j ∈ l.piece)) n,
      mem (Xb + 2 + 3 + 4 * cnt (fun j => bf (g j ∈ l.piece)) n + k) = ν (M.tail (g (IX k))))
    (h_fx : ∀ k < cnt (fun j => bf (g j ∈ pdarts M l.piece (childHoles Hs π.path.mverts))) n,
      mem (Xb + 2 + 3 + 6 * cnt (fun j => bf (g j ∈ l.piece)) n + k) = CI (IX2 k)) :
    RecsOut M ds gid ν S T l r π Hs σ lo hi Xb mem := by
  have hlP : l.piece ⊆ l.piece ∪ r.piece := subset_union_left
  have hYl : pdarts M l.piece (childHoles Hs π.path.mverts) ⊆ l.piece := pdarts_subset _ _
  have cl : cnt (fun j => bf (g j ∈ l.piece)) n = l.piece.card :=
    cnt_bf_card hg_inj fun d hd => hg_surj d (hlP hd)
  have cY : cnt (fun j => bf (g j ∈ pdarts M l.piece (childHoles Hs π.path.mverts))) n =
      (pdarts M l.piece (childHoles Hs π.path.mverts)).card :=
    cnt_bf_card hg_inj fun d hd => hg_surj d (hlP (hYl hd))
  have hArr := recL_arr M (gid := gid) (ν := ν) (S := S) (T := T) (y := chL M l r π Hs σ)
    (P := l.piece ∪ r.piece) hg_inj hg_surj hg_mono hlP hYl hlrev rfl rfl hci hix2 hrp
    (Rp := Xb + 2) h_gp h_rp h_hp h_kp h_vp h_fx
  rw [cY, cl] at hArr
  refine ⟨hlo, by rw [m0, m1]; clear * - hhi; omega, ⟨?_, l.piece.card, fun k => g (IX k), ?_, ?_⟩,
    ⟨?_, 0, g, ?_, ?_⟩⟩
  · rw [m0, cY, cl]; unfold rszC; simp only [chL]; omega
  · rw [m3, m0, cY, cl]; unfold rszL; simp only [chL]; rw [iteT (by omega)]; omega
  · refine ⟨by rw [m2, cl], by rw [m3]; omega, by rw [m4]; omega, ?_, fun _ => ?_⟩
    · rw [m3]; exact Or.inr (Or.inl ⟨rfl, hlsm⟩)
    · rw [← cl] at hArr ⊢; exact hArr.congr fun a _ _ => rfl
  · rw [m1]; unfold rszC; omega
  · rw [m6]; unfold rszL; simpa using m1
  · refine ⟨m5, by rw [m6], by rw [m7]; omega, ?_, fun h => ?_⟩
    · rw [m6, m7]; exact Or.inr (Or.inr ⟨rfl, Q, by rw [hrl]; rfl⟩)
    · rw [m6] at h; omega

end MfDrv

end BKMNW

end PlanarFlow
