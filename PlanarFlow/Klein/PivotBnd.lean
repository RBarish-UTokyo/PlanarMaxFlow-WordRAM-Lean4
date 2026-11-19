module

public import PlanarFlow.Klein.PivotOps
public import PlanarFlow.DynTree.VBndOps

/-!
# The values of the forest along a pivot are bounded

The compare-bounded runs of the dynamic trees (`DynTree.ORunC`) need a bound `V` of the values of
the forest (`DynTree.VBnd`) at every operation. Along the sixteen operations `pivotOps` of a
pivot (`pivot_ops_stored`) from a forest with values at most `U`:

* `pivot_allV`: every forest along the operations has values at most
  `U + Σ |z|` (`DynTree.allV_of_vbnd`), at most `5 U + 2 |c| + 4 Tb` when the targets of the four
  additions setting the isolated nodes are at most `Tb`;
* `pivot_vbnd`: **the forest after the pivot has values at most `max (U + |c|) Tb`**: the
  additions `∓c` along the path of the cotree shift values by `|c|`, and the four other additions
  are at roots (by the validity of the links after them) and set the values of the isolated nodes
  of the two new edges: `wt a - φ a - c`, `wt (rev a) + φ a + c` (the node of the edge of the old
  parent dart `a`, whose values `v₁`, `v₂` are kept by the operations before, `Agree`) and
  `φ b`, `φ (rev b)` (the node of the edge of `b` in the spanning tree, read from the stored
  reparented tree).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap STFlow DynTree

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {n : ℕ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ}

/-- The size of the changes of the values by a pivot. -/
lemma zsum_pivotOps (nfa nfra nea neb nz nfe yv nga ngb ntb : ℕ) (c δ₁ δ₂ δ₃ δ₄ : ℤ) :
    zsum (pivotOps nfa nfra nea neb nz nfe yv nga ngb ntb c δ₁ δ₂ δ₃ δ₄) =
      2 * |(c : ℝ)| + |(δ₁ : ℝ)| + |(δ₂ : ℝ)| + |(δ₃ : ℝ)| + |(δ₄ : ℝ)| := by
  simp only [pivotOps, zsum, EOp.zabs, Int.cast_neg, abs_neg]
  ring

/-- **The forests along a pivot are bounded** by `U + Σ |z|`. -/
theorem pivot_allV {U : ℝ} {Fo : Forest} (hU : VBnd U n Fo)
    (nfa nfra nea neb nz nfe yv nga ngb ntb : ℕ) (c δ₁ δ₂ δ₃ δ₄ : ℤ) :
    AllV (U + (2 * |(c : ℝ)| + |(δ₁ : ℝ)| + |(δ₂ : ℝ)| + |(δ₃ : ℝ)| + |(δ₄ : ℝ)|)) n Fo
      (pivotOps nfa nfra nea neb nz nfe yv nga ngb ntb c δ₁ δ₂ δ₃ δ₄) := by
  rw [← zsum_pivotOps]; exact allV_of_vbnd _ hU

/-- **The forest after a pivot is bounded** by `max (U + |c|) Tb`, `Tb` a bound of the new values
of the two edges changing trees. -/
theorem pivot_vbnd (hM : M.IsPlane) (hL : Layout M n ιv ιg ιf ιe) {φ : D → ℤ} {fe : F}
    {Lo : ℝ} {Fo : Forest} {T : DTree M.dual} {val : D → ℤ}
    (hS : Stored M n ιv ιg ιf ιe φ fe Lo Fo T val) {y : V} (hy : y ≠ T.root) {b : D}
    (hby : M.dual.face (M.dual.rev b) = y) (hna : ¬ T.Anc y (M.dual.face b)) (hbT : ¬ T.InT b)
    (wt : D → ℤ) (c : ℤ) {v₁ v₂ w₁ w₂ : ℤ} (hv₁ : Fo.val (ιe (T.par y)) = v₁)
    (hv₂ : Fo.val2 (ιe (T.par y)) = v₂) (hw₁ : Fo.val (ιg b) = w₁)
    (hw₂ : Fo.val2 (ιg b) = w₂) {U Tb : ℝ} (hU : VBnd U n Fo)
    (ht₁ : |((wt (T.par y) - φ (T.par y) - c : ℤ) : ℝ)| ≤ Tb)
    (ht₂ : |((wt (M.rev (T.par y)) + φ (T.par y) + c : ℤ) : ℝ)| ≤ Tb)
    (ht₃ : |(φ b : ℝ)| ≤ Tb) (ht₄ : |(φ (M.rev b) : ℝ)| ≤ Tb) :
    VBnd (max (U + |(c : ℝ)|) Tb) n
      (runOpsE n Fo (pivotOps (ιf (M.face (T.par y))) (ιf (M.face (M.rev (T.par y))))
        (ιe (T.par y)) (ιe b)
        (cutNode (runOpsE n Fo (pivotPre (ιf (M.face (T.par y)))
          (ιf (M.face (M.rev (T.par y)))) c)).1 ιf ιe M b)
        (ιf fe) (ιv y) (ιg (T.par y)) (ιg b) (ιv (M.tail b)) c
        (wt (T.par y) - φ (T.par y) - c - v₁) (wt (M.rev (T.par y)) + φ (T.par y) + c - v₂)
        (φ b - w₁) (φ (M.rev b) - w₂))).1 := by
  classical
  obtain ⟨hval, -, hS'⟩ := pivot_ops_stored hM hL hS hy hby hna hbT wt c hv₁ hv₂ hw₁ hw₂
  obtain ⟨C, β, β₂, -, hoff, hRc, hIc, -⟩ := hS.cot
  set a := T.par y with ha
  set nfa := ιf (M.face a)
  set nfra := ιf (M.face (M.rev a))
  set nea := ιe a
  set neb := ιe b
  set nz := cutNode (runOpsE n Fo (pivotPre nfa nfra c)).1 ιf ιe M b with hnz
  set nfe := ιf fe
  set yv := ιv y
  set nga := ιg a
  set ngb := ιg b
  set ntb := ιv (M.tail b)
  set δ₁ := wt a - φ a - c - v₁
  set δ₂ := wt (M.rev a) + φ a + c - v₂
  set δ₃ := φ b - w₁
  set δ₄ := φ (M.rev b) - w₂
  set F1 := evert Fo n nfa with hF1
  set F2 := addPath F1 n nfra ((-c : ℤ) : ℝ) with hF2
  set F3 := addPath2 F2 n nfra (c : ℝ) with hF3
  set F5 := cut (cut F3 n nz) n neb with hF5
  set F6 := addPath F5 n nea (δ₁ : ℝ) with hF6
  set F7 := addPath2 F6 n nea (δ₂ : ℝ) with hF7
  set F12 := cut (cut (evert (link (link F7 nea nfra) nfa nea) n nfe) n yv) n nga with hF12
  set F13 := addPath F12 n ngb (δ₃ : ℝ) with hF13
  set F14 := addPath2 F13 n ngb (δ₄ : ℝ) with hF14
  have hF : (runOpsE n Fo (pivotOps nfa nfra nea neb nz nfe yv nga ngb ntb c δ₁ δ₂ δ₃ δ₄)).1 =
      link (link F14 ngb ntb) yv ngb := rfl
  rw [hF]
  -- the validity of the links after the additions: `nea`, `ngb` are roots there
  obtain ⟨-, -, -, -, -, -, -, ⟨-, -, h8, -⟩, -, -, -, -, -, -, ⟨-, -, h15, -⟩, -⟩ := hval
  have p7 : F5.par nea = n := h8
  have p14 : F12.par ngb = n := h15
  have hnea : nea < n := hL.dual.e_lt a
  have hngb : ngb < n := hL.prim.e_lt b
  -- `a` is off the cotree
  have hTa : T.InT a := ⟨y, hy, Or.inl rfl⟩
  have hCa : ¬ C.InT a := by
    rintro ⟨x, hx, h | h⟩
    · exact hoff x hx (h ▸ hTa)
    · have hc : C.par x = M.rev a := by rw [h, M.rev_rev]
      obtain ⟨x', hx', h'⟩ := hTa
      refine hoff x hx ⟨x', hx', ?_⟩
      rcases h' with h' | h'
      · right; rw [hc, h']; rfl
      · left
        have h'' : a = M.rev (T.par x') := h'
        rw [hc, h'', M.rev_rev]
  have hd := off_iff_not_inT.2 hCa
  have hd' := off_iff_not_inT.2 (fun h => hCa (reroot_inT (w := M.face a) h))
  -- the values of `nea` are kept until the additions
  have hR1 := evert_trep hRc hL.dual hL.hf (M.face a)
  have n1 : nea ∉ rootPath Fo n nfa := by
    rw [rootPath_rep hRc hL.dual.f_lt hL.dual.e_lt hL.hf]
    exact not_mem_tpath_off hL.dual hd le_rfl
  have n2 : nea ∉ rootPath F1 n nfra := by
    rw [rootPath_rep hR1 hL.dual.f_lt hL.dual.e_lt hL.hf]
    exact not_mem_tpath_off hL.dual hd' le_rfl
  have n3 : nea ∉ rootPath F2 n nfra := by
    have : rootPath F2 n nfra = rootPath F1 n nfra := rootPath_congr (show F2.par = F1.par from rfl) nfra
    rw [this]; exact n2
  have hnz : nea ≠ nz := by
    rw [hnz]; unfold cutNode; split_ifs
    · exact (hL.dual.fe _ _).symm
    · exact (hL.dual.fe _ _).symm
  have hneb : nea ≠ neb := fun h => by
    rcases hL.dual.e_eq _ _ h with h' | h'
    · exact hbT (h' ▸ hTa)
    · obtain ⟨x', hx', h''⟩ := hTa
      refine hbT ⟨x', hx', ?_⟩
      rcases h'' with h'' | h''
      · right; rw [h', h'']; rfl
      · left
        have h3 : a = M.rev (T.par x') := h''
        rw [h', h3, M.rev_rev]
  have ag : Agree Fo F3 nea :=
    ((agree_evert n1).trans (agree_addPath n2 _)).trans (agree_addPath2 n3 _)
  have e1 : F5.val nea = v₁ := by
    show (cut (cut F3 n nz) n neb).val nea = v₁
    simp only [cut]; rw [ag.2.1, hv₁]
  have e2 : F5.val2 nea = v₂ := by
    show (cut (cut F3 n nz) n neb).val2 nea = v₂
    simp only [cut]; rw [ag.2.2, hv₂]
  -- the values of `ngb` at the end, from the stored reparented tree
  have hry : y ≠ (T.reparent y b hy hby hna).root := hy
  have hpy : (T.reparent y b hy hby hna).par y = b := by
    rw [DTree.reparent_par, ite_eq_left (rfl : y = y)]
  have f1 := hS'.tree.ve y hry
  have f2 := hS'.tree.ve2 y hry
  rw [hpy] at f1 f2
  have g1 : |F12.val ngb + (δ₃ : ℝ)| ≤ Tb := by
    have : F13.val ngb = F12.val ngb + (δ₃ : ℝ) := by
      show (if ngb ∈ rootPath F12 n ngb then _ else _) = _
      rw [rootPath_root hngb p14, ite_eq_left (List.mem_singleton_self _)]
    rw [← this]
    have h := f1
    change F13.val ngb = _ at h
    rw [h]
    have hb : M.rev (M.dual.rev b) = b := M.rev_rev b
    rw [hb]; exact ht₃
  have g2 : |F13.val2 ngb + (δ₄ : ℝ)| ≤ Tb := by
    have : F14.val2 ngb = F13.val2 ngb + (δ₄ : ℝ) := by
      show (if ngb ∈ rootPath F13 n ngb then _ else _) = _
      have : rootPath F13 n ngb = rootPath F12 n ngb := rootPath_congr (show F13.par = F12.par from rfl) ngb
      rw [this, rootPath_root hngb p14,
        ite_eq_left (List.mem_singleton_self _)]
    rw [← this]
    have h := f2
    change F14.val2 ngb = _ at h
    rw [h]
    simpa using ht₄
  -- the chain of bounds
  set W' := max (U + |(c : ℝ)|) Tb
  have b3 : VBnd (U + |(c : ℝ)|) n F3 :=
    vbnd_addBoth (vbnd_evert hU nfa) nfra (by push_cast; rw [abs_neg]) nfra
  have b5 : VBnd W' n F5 := (vbnd_cut (vbnd_cut b3 nz) neb).mono (le_max_left _ _)
  have hδ₁ : (v₁ : ℝ) + (δ₁ : ℝ) = ((wt a - φ a - c : ℤ) : ℝ) := by
    have : δ₁ = wt a - φ a - c - v₁ := rfl
    rw [this]; push_cast; ring
  have hδ₂ : (v₂ : ℝ) + (δ₂ : ℝ) = ((wt (M.rev a) + φ a + c : ℤ) : ℝ) := by
    have : δ₂ = wt (M.rev a) + φ a + c - v₂ := rfl
    rw [this]; push_cast; ring
  have b6 : VBnd W' n F6 := vbnd_set b5 hnea p7 (by
    rw [e1, hδ₁]; exact ht₁.trans (le_max_right _ _))
  have b7 : VBnd W' n F7 := vbnd_set2 b6 hnea p7 (by
    show |F5.val2 nea + _| ≤ _
    rw [e2, hδ₂]; exact ht₂.trans (le_max_right _ _))
  have b12 : VBnd W' n F12 :=
    vbnd_cut (vbnd_cut (vbnd_evert (vbnd_link (vbnd_link b7 _ _) _ _) _) _) _
  have b13 : VBnd W' n F13 := vbnd_set b12 hngb p14 (g1.trans (le_max_right _ _))
  have b14 : VBnd W' n F14 := vbnd_set2 b13 hngb p14 (g2.trans (le_max_right _ _))
  exact vbnd_link (vbnd_link b14 _ _) _ _

end Klein

end PlanarFlow
