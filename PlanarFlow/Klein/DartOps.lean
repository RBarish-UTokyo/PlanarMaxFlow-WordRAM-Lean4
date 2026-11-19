module

public import PlanarFlow.Klein.PivotOps

/-!
# The operations changing the value of one dart, by their nodes

`dart_stored` gives the operations changing the value of a dart of the stored cotree by their
existence (they name the face below the edge in a cotree given by its existence). A program reads
them from the forest: the parent `p` of the node of the edge of the dart.

* `dartOps`: none when the node of the edge is a root (the edge is off the cotree); otherwise the
  additions on the node of the edge and on `p`: on the second values when `p` is the node of the
  face of the dart (the dart is the parent dart), on the first values otherwise (its reverse is).
* `dart_ops_stored`: **these are the operations of `dart_stored`**: valid, printing nothing, the
  value of the dart moved by `δ`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {n : ℕ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ}

/-- **The operations moving the value of the dart `d` by `δ`**, read from the forest `Fo`. -/
def dartOps (Fo : Forest) (n : ℕ) (ιf : F → ℕ) (ιe : D → ℕ) (M : CombMap D V F) (d : D)
    (δ : ℤ) : List EOp :=
  if Fo.par (ιe d) < n then
    if Fo.par (ιe d) = ιf (M.face d) then
      [.add (ιe d) 0, .add (Fo.par (ιe d)) (-0), .add2 (ιe d) δ, .add2 (Fo.par (ιe d)) (-δ)]
    else
      [.add (ιe d) δ, .add (Fo.par (ιe d)) (-δ), .add2 (ιe d) 0, .add2 (Fo.par (ιe d)) (-0)]
  else []

lemma dartOps_length_le (Fo : Forest) (d : D) (δ : ℤ) : (dartOps Fo n ιf ιe M d δ).length ≤ 4 := by
  unfold dartOps; split_ifs <;> simp

/-- **Moving the value of one dart of the stored cotree by `δ`** with the operations `dartOps`
(`dart_stored` with the operations named). -/
theorem dart_ops_stored (hL : Layout M n ιv ιg ιf ιe) {φ : D → ℤ} {fe : F} {Lo : ℝ}
    {Fo : Forest} {T : DTree M.dual} {val : D → ℤ}
    (hS : Stored M n ιv ιg ιf ιe φ fe Lo Fo T val) (d : D) (δ : ℤ) :
    ValidOpsE n Fo (dartOps Fo n ιf ιe M d δ) ∧ (runOpsE n Fo (dartOps Fo n ιf ιe M d δ)).2 = [] ∧
      Stored M n ιv ιg ιf ιe φ fe Lo (runOpsE n Fo (dartOps Fo n ιf ιe M d δ)).1 T
        (Function.update val d (val d + δ)) := by
  classical
  obtain ⟨C, β, β₂, hroot, hoff, hRc, hIc, hLo⟩ := hS.cot
  -- the change by the operations of a point of the cotree
  have hpt : ∀ y, y ≠ C.root → ∀ δ₁ δ₂ : ℤ, (∀ d', (val d' : ℝ) +
      (if d' = C.par y then (δ₂ : ℝ) else 0) + (if d' = M.rev (C.par y) then (δ₁ : ℝ) else 0) =
        ((Function.update val d (val d + δ) d' : ℤ) : ℝ)) →
      ValidOpsE n Fo (pointOps ιf ιe C y δ₁ δ₂) ∧ (runOpsE n Fo (pointOps ιf ιe C y δ₁ δ₂)).2 = [] ∧
        Stored M n ιv ιg ιf ιe φ fe Lo (runOpsE n Fo (pointOps ιf ιe C y δ₁ δ₂)).1 T
          (Function.update val d (val d + δ)) := by
    intro y hy δ₁ δ₂ hκ
    obtain ⟨hv, ho, hR', hpar, hag⟩ := point_trep hRc hL.dual hL.hf hy δ₁ δ₂
    have hint := intF_runOpsE (n := n) (pointOps ιf ιe C y δ₁ δ₂) hS.int
    exact ⟨hv, ho,
      ⟨hS.tree.congr (fun x => hag _ (hL.ve x _)) (fun d' => hag _ (hL.ge d' _)),
        hS.treeIso.congr (fun d' => hag _ (hL.ge d' _)),
        ⟨C, β, β₂, hroot, hoff, hR'.congrκ hκ,
          fun d' hd' => (congrFun hpar _).trans (hIc d' hd'), hLo⟩, hint⟩⟩
  have hfn : ∀ y, ιf y < n := hL.dual.f_lt
  by_cases h1 : ∃ y, y ≠ C.root ∧ C.par y = d
  · obtain ⟨y, hy, rfl⟩ := h1
    have hp := hRc.pe y hy
    have hops : dartOps Fo n ιf ιe M (C.par y) δ = pointOps ιf ιe C y 0 δ := by
      unfold dartOps pointOps
      rw [hp, ite_eq_left (hfn _), ite_eq_left rfl]
    rw [hops]
    refine hpt y hy 0 δ fun d' => ?_
    by_cases hd : d' = C.par y
    · subst hd; simp [Function.update_self]
    · simp [hd]
  by_cases h2 : ∃ y, y ≠ C.root ∧ C.par y = M.rev d
  · obtain ⟨y, hy, hyd⟩ := h2
    have hd : d = M.rev (C.par y) := by rw [hyd, M.rev_rev]
    subst hd
    have hp := hRc.pe y hy
    rw [← hL.dual.e_rev] at hp
    have hne : ιf (M.face (C.par y)) ≠ ιf (M.face (M.rev (C.par y))) := by
      intro h
      have hf := hL.dual.f_inj h
      have hrr := C.head_par y hy
      have hup : C.up y = y := by rw [C.up_of_ne hy, hf, hrr]
      have hdep := C.depth_up hy
      rw [hup] at hdep
      omega
    have hops : dartOps Fo n ιf ιe M (M.rev (C.par y)) δ = pointOps ιf ιe C y δ 0 := by
      unfold dartOps pointOps
      rw [hp, ite_eq_left (hfn _), ite_eq_right hne, hL.dual.e_rev]
    rw [hops]
    refine hpt y hy δ 0 fun d' => ?_
    by_cases hd : d' = M.rev (C.par y)
    · subst hd; simp [Function.update_self, M.rev_ne]
    · simp [hd]
  push Not at h1 h2
  have hiso : Fo.par (ιe d) = n := hIc d fun y hy =>
    ⟨fun h => h1 y hy h.symm, fun h => h2 y hy (by rw [h, M.rev_rev])⟩
  have hops : dartOps Fo n ιf ιe M d δ = [] := by
    unfold dartOps; rw [hiso, ite_eq_right (lt_irrefl n)]
  rw [hops]
  refine ⟨trivial, rfl, hS.tree, hS.treeIso,
    ⟨C, β, β₂, hroot, hoff, ⟨hRc.pf, hRc.pr, hRc.pe, fun y hy => ?_, fun y hy => ?_, hRc.vf,
      hRc.vf2⟩, hIc, hLo⟩, hS.int⟩
  · have hne : M.rev (C.par y) ≠ d := fun h => h2 y hy (by rw [← h, M.rev_rev])
    show Fo.val _ = ((Function.update val d (val d + δ) (M.rev (C.par y)) : ℤ) : ℝ)
    rw [Function.update_of_ne hne]; exact hRc.ve y hy
  · show Fo.val2 _ = ((Function.update val d (val d + δ) (C.par y) : ℤ) : ℝ)
    rw [Function.update_of_ne (h1 y hy)]; exact hRc.ve2 y hy

end Klein

end PlanarFlow
