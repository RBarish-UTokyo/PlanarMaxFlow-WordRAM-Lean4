module

public import PlanarFlow.Klein.ProgInitC
public import PlanarFlow.Klein.NL.ProgInit
public import PlanarFlow.Klein.NL.ProgMove
public import PlanarFlow.Klein.NL.ProgNext
public import PlanarFlow.Klein.NL.ProgPivot
public import PlanarFlow.Klein.NL.ProgWeight
public import PlanarFlow.Klein.NL.Input

/-! Copy of `PlanarFlow.Klein.ProgInitC` for `KInputNL` (generated mechanically). -/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs

section
variable {P : Input} {W H B n : ℕ}

end

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {nD : ℕ} {σ : D ≃ Fin nD}

section
variable {P : Input} {W H B n : ℕ}

/-- `inT_orun` with bounded comparisons. -/
theorem inT_orunCNL (hW : B + 16 * (n + 1) ≤ W) {k : ℕ} (hWa : 9 * nD + 7 * n + k + 4 ≤ W)
    (hB : n + 2 * nD ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W) {S : Finset D} {ℓ : D → ℤ}
    {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInputNL M S ℓ σ ιv ιg ιf ιe P) {T : DTree M.dual} {C : DTree M} {vs ts : List V}
    {fs cs : List F} (hI : KInit M σ ιv ιf n k T C vs ts fs cs P) {φ : D → ℤ}
    (hv : ValidOpsE n (Forest.init n) (treeOpsL T ιv ιg φ vs ts)) {Vb : ℝ} (hH : 2 * Vb ≤ H)
    (hA : AllV Vb n (Forest.init n) (treeOpsL T ιv ιg φ vs ts)) {c : Config}
    (hc : WordsBounded W c) {G : List VT} (hS : LCTE B n (Forest.init n) G c)
    (hph : ∀ d, c.rmem (aPH nD + σ d) = φ d) :
    ∃ c' G', ORunC P W H B n (inTS B nD n k) c (Forest.init n) G c' (treeOpsL T ιv ιg φ vs ts)
        G' (6 * Fintype.card V) (45 * Fintype.card V + 16) ∧
      (∀ r, r < 110 → c'.nreg r = c.nreg r ∧ c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a := by
  have hvl := hI.oT.flen
  have htl := hI.oT.ylen
  have hVn : 2 * Fintype.card V ≤ n := hL.hv
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  rw [treeOpsL_eq T φ hI.oT] at hv hA ⊢
  obtain ⟨hvAB, hvC⟩ := (validOpsE_append_iff n _ _ _).1 hv
  obtain ⟨hvA, hvB⟩ := (validOpsE_append_iff n _ _ _).1 hvAB
  rw [runOpsE_fst_append] at hvC
  have hAAB := AllV.left hA
  have hAA := AllV.left hAAB
  have hAB := AllV.right hAAB
  have hAC := AllV.right hA
  rw [runOpsE_fst_append] at hAC
  -- the values of the nodes of the vertices
  obtain ⟨c₁, k₁, e₁, hk₁, p120, p121, p110, g₁⟩ : ∃ c' k', Exec P W
      (block (.constR 110 0 :: ldI (iHD nD n k))) c c' k' ∧ k' = 4 ∧ c'.nreg 120 = 0 ∧
      c'.nreg 121 = vs.length ∧ c'.rreg 110 = ((0 : ℤ) : ℝ) ∧ GFr 110 122 c c' := by
    unfold ldI
    exec_block
    · omega
    · unfold iHD iIV; omega
    · config_simp; exact hP _
    · exact ⟨rfl, by config_simp, by config_simp; exact hI.l0, by config_simp, by gfr_tac⟩
  have o₁ := ORunC.ofGFr (H := H) e₁ hS g₁ (by omega) (by rfl)
  obtain ⟨c₂, G₂, o₂, q₂⟩ := listLoop_orunC (P := P) (W := W) (H := H) (B := B) (n := n)
    (ra := 120) (rb := 121) vs (fun y => [EOp.add (ιv y) 0, .add2 (ιv y) 0]) hvA hAA
    (fun _ c' => IFr B n c₁ c')
    (body := bodyNV B (iIV nD n k) 110) (mb := 2) (hb := 5)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi hAi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := bodyNV_orunC hW hP hI.iv (by unfold iIV; omega) hi hc'
        hS' h120 (z := 0) (by rw [hQ.2.1 110 (by omega), p110]) (by omega) hvi hH hAi
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega), p121]⟩)
    e₁.wb_right o₁.1.2.lcte (IFr.refl _ _ _) p120 p121
  -- the values of the nodes of the edges
  obtain ⟨c₃, k₃, e₃, hk₃, s120, s121, g₃⟩ := ldI_exec (P := P) o₂.1.2.wb hP
    (off := iHD nD n k + 1) (by unfold iHD iIV; omega)
  have o₃ := ORunC.ofGFr (H := H) e₃ o₂.1.2.lcte g₃ (by omega) (by rfl)
  have hph₃ : ∀ d, c₃.rmem (aPH nD + σ d) = φ d := fun d => by
    have := hσ d
    rw [g₃.2.2.1, (q₂.2.2.2 _ (Or.inl (by unfold aPH; omega))).2, g₁.2.2.1, hph]
  obtain ⟨c₄, G₄, o₄, q₄⟩ := listLoop_orunC (P := P) (W := W) (H := H) (B := B) (n := n)
    (ra := 120) (rb := 121) ts
    (fun y => eopsDV false (ιg (T.par y)) (φ (T.par y)) (φ (M.rev (T.par y))))
    hvB hAB (fun _ c' => IFr B n c₃ c') (body := bodyDV B nD (iIT nD n k) (iNG nD) (aPH nD)
      (opsDV false)) (mb := 2) (hb := 17)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi hAi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := bodyDV_orunC (aA := aPH nD) (A := φ) hW hP hK.rv
        hI.it (by unfold iIT iIV; omega) hK.ng (by unfold iNG; omega)
        (by unfold aPH; omega) false hi hc' hS' h120 (fun d => by
          have := hσ d
          rw [(hQ.2.2.2 _ (Or.inl (by unfold aPH; omega))).2, hph₃]) hvi hH hAi
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega), s121,
        hI.l1]⟩)
    e₃.wb_right o₃.1.2.lcte (IFr.refl _ _ _) s120 (by rw [s121, hI.l1])
  -- the links
  obtain ⟨c₅, k₅, e₅, hk₅, t120, t121, g₅⟩ := ldI_exec (P := P) o₄.1.2.wb hP
    (off := iHD nD n k + 1) (by unfold iHD iIV; omega)
  have o₅ := ORunC.ofGFr (H := H) e₅ o₄.1.2.lcte g₅ (by omega) (by rfl)
  obtain ⟨c₆, G₆, o₆, q₆⟩ := listLoop_orunC (P := P) (W := W) (H := H) (B := B) (n := n)
    (ra := 120) (rb := 121) ts (fun y => [EOp.link (ιg (T.par y)) (ιv (M.tail (T.par y))),
      .link (ιv (M.tail (M.rev (T.par y)))) (ιg (T.par y))])
    hvC hAC (fun _ c' => IFr B n c₅ c') (body := bodyLK B nD (iIT nD n k) (iNG nD) (iNT nD))
    (mb := 2) (hb := 17)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi hAi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := bodyLK_orunC hW hP hK.rv hI.it
        (by unfold iIT iIV; omega) hK.ng (by unfold iNG; omega) hK.nt (by unfold iNT; omega)
        hi hc' hS' h120 hvi hH hAi
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega), t121,
        hI.l1]⟩)
    e₅.wb_right o₅.1.2.lcte (IFr.refl _ _ _) t120 (by rw [t121, hI.l1])
  have o := o₁.seq (o₂.seq (o₃.seq (o₄.seq (o₅.seq o₆))))
  simp only [List.nil_append] at o
  have hfr : IFr0 B n c c₆ := (((((g₁.to0 (by omega)).trans q₂.to0).trans
    (g₃.to0 (by omega))).trans q₄.to0).trans (g₅.to0 (by omega))).trans q₆.to0
  refine ⟨c₆, G₆, ?_, hfr.1, hfr.2.1, hfr.2.2⟩
  rw [List.append_assoc]; exact o.mono (by omega) (by omega)

/-- `inC_orun` with bounded comparisons. -/
theorem inC_orunCNL (hW : B + 16 * (n + 1) ≤ W) {k : ℕ} (hWa : 9 * nD + 7 * n + k + 4 ≤ W)
    (hB3 : 3 * nD + 3 ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W) {S : Finset D} {ℓ : D → ℤ}
    {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInputNL M S ℓ σ ιv ιg ιf ιe P) {T : DTree M.dual} {C : DTree M} {vs ts : List V}
    {fs cs : List F} (hI : KInit M σ ιv ιf n k T C vs ts fs cs P) {val : D → ℤ} {H₀ : ℤ}
    {F₁ : Forest} (hv : ValidOpsE n F₁ (cotOpsL C ιf ιe val H₀ fs cs)) {Vb : ℝ}
    (hH : 2 * Vb ≤ H) (hA : AllV Vb n F₁ (cotOpsL C ιf ιe val H₀ fs cs)) {c : Config}
    (hc : WordsBounded W c) {G : List VT} (hS : LCTE B n F₁ G c)
    (hvl : ∀ d, c.rmem (aVL nD + σ d) = val d) (hH0 : c.rmem (aH0 nD) = H₀) :
    ∃ c' G', ORunC P W H B n (inCS B nD n k) c F₁ G c' (cotOpsL C ιf ιe val H₀ fs cs) G'
        (6 * Fintype.card F) (45 * Fintype.card F + 17) ∧ IFr0 B n c c' := by
  have hfl := hI.oC.flen
  have hcl := hI.oC.ylen
  have hFn : 2 * Fintype.card F ≤ n := hL.hf
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  rw [cotOpsL_eq C val H₀ hI.oC] at hv hA ⊢
  obtain ⟨hvAB, hvC⟩ := (validOpsE_append_iff n _ _ _).1 hv
  obtain ⟨hvA, hvB⟩ := (validOpsE_append_iff n _ _ _).1 hvAB
  rw [runOpsE_fst_append] at hvC
  have hAAB := AllV.left hA
  have hAA := AllV.left hAAB
  have hAB := AllV.right hAAB
  have hAC := AllV.right hA
  rw [runOpsE_fst_append] at hAC
  -- the values of the nodes of the faces
  obtain ⟨c₁, k₁, e₁, hk₁, p120, p121, p111, g₁⟩ : ∃ c' k', Exec P W
      (block ([.constN 122 (aH0 nD), .loadR 111 122] ++ ldI (iHD nD n k + 2))) c c' k' ∧
      k' = 5 ∧ c'.nreg 120 = 0 ∧ c'.nreg 121 = fs.length ∧ c'.rreg 111 = (H₀ : ℝ) ∧
      GFr 111 123 c c' := by
    unfold ldI
    exec_block
    · unfold aH0; omega
    · omega
    · unfold iHD iIV; omega
    · config_simp; exact hP _
    · exact ⟨rfl, by config_simp, by config_simp; exact hI.l2, by config_simp; exact hH0,
        by gfr_tac⟩
  have o₁ := ORunC.ofGFr (H := H) e₁ hS g₁ (by omega) (by rfl)
  obtain ⟨c₂, G₂, o₂, q₂⟩ := listLoop_orunC (P := P) (W := W) (H := H) (B := B) (n := n)
    (ra := 120) (rb := 121) fs (fun y => [EOp.add (ιf y) H₀, .add2 (ιf y) H₀]) hvA hAA
    (fun _ c' => IFr B n c₁ c') (body := bodyNV B (iIF nD n k) 111) (mb := 2) (hb := 5)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi hAi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := bodyNV_orunC hW hP hI.if_ (by unfold iIF iIV; omega) hi
        hc' hS' h120 (z := H₀) (by rw [hQ.2.1 111 (by omega), p111]) (by omega) hvi hH hAi
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega), p121]⟩)
    e₁.wb_right o₁.1.2.lcte (IFr.refl _ _ _) p120 p121
  -- the values of the nodes of the edges
  obtain ⟨c₃, k₃, e₃, hk₃, s120, s121, g₃⟩ := ldI_exec (P := P) o₂.1.2.wb hP
    (off := iHD nD n k + 3) (by unfold iHD iIV; omega)
  have o₃ := ORunC.ofGFr (H := H) e₃ o₂.1.2.lcte g₃ (by omega) (by rfl)
  have hvl₃ : ∀ d, c₃.rmem (aVL nD + σ d) = val d := fun d => by
    have := hσ d
    rw [g₃.2.2.1, (q₂.2.2.2 _ (Or.inl (by unfold aVL; omega))).2, g₁.2.2.1, hvl]
  obtain ⟨c₄, G₄, o₄, q₄⟩ := listLoop_orunC (P := P) (W := W) (H := H) (B := B) (n := n)
    (ra := 120) (rb := 121) cs
    (fun y => eopsDV true (ιe (C.par y)) (val (C.par y)) (val (M.rev (C.par y))))
    hvB hAB (fun _ c' => IFr B n c₃ c') (body := bodyDV B nD (iIC nD n k) (iNE nD) (aVL nD)
      (opsDV true)) (mb := 2) (hb := 17)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi hAi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := bodyDV_orunC (aA := aVL nD) (A := val) hW hP hK.rv
        hI.ic (by unfold iIC iIV; omega) hK.ne (by unfold iNE; omega)
        (by unfold aVL; omega) true hi hc' hS' h120 (fun d => by
          have := hσ d
          rw [(hQ.2.2.2 _ (Or.inl (by unfold aVL; omega))).2, hvl₃]) hvi hH hAi
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega), s121,
        hI.l3]⟩)
    e₃.wb_right o₃.1.2.lcte (IFr.refl _ _ _) s120 (by rw [s121, hI.l3])
  -- the links
  obtain ⟨c₅, k₅, e₅, hk₅, t120, t121, g₅⟩ := ldI_exec (P := P) o₄.1.2.wb hP
    (off := iHD nD n k + 3) (by unfold iHD iIV; omega)
  have o₅ := ORunC.ofGFr (H := H) e₅ o₄.1.2.lcte g₅ (by omega) (by rfl)
  obtain ⟨c₆, G₆, o₆, q₆⟩ := listLoop_orunC (P := P) (W := W) (H := H) (B := B) (n := n)
    (ra := 120) (rb := 121) cs (fun y => [EOp.link (ιe (C.par y)) (ιf (M.face (C.par y))),
      .link (ιf (M.face (M.rev (C.par y)))) (ιe (C.par y))])
    hvC hAC (fun _ c' => IFr B n c₅ c') (body := bodyLK B nD (iIC nD n k) (iNE nD) (iNF nD))
    (mb := 2) (hb := 17)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi hAi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := bodyLK_orunC hW hP hK.rv hI.ic
        (by unfold iIC iIV; omega) hK.ne (by unfold iNE; omega) hK.nf (by unfold iNF; omega)
        hi hc' hS' h120 hvi hH hAi
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega), t121,
        hI.l3]⟩)
    e₅.wb_right o₅.1.2.lcte (IFr.refl _ _ _) t120 (by rw [t121, hI.l3])
  have o := o₁.seq (o₂.seq (o₃.seq (o₄.seq (o₅.seq o₆))))
  simp only [List.nil_append] at o
  have hfr : IFr0 B n c c₆ := (((((g₁.to0 (by omega)).trans q₂.to0).trans
    (g₃.to0 (by omega))).trans q₄.to0).trans (g₅.to0 (by omega))).trans q₆.to0
  refine ⟨c₆, G₆, ?_, hfr⟩
  rw [List.append_assoc]; exact o.mono (by omega) (by omega)

/-- `inP_orun` with bounded comparisons (the parent darts: no real test). -/
theorem inP_orunCNL (hW : B + 16 * (n + 1) ≤ W) {k : ℕ} (hWa : 9 * nD + 7 * n + k + 4 ≤ W)
    (hB : n + 2 * nD ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W) {S : Finset D} {ℓ : D → ℤ}
    {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInputNL M S ℓ σ ιv ιg ιf ιe P) {T : DTree M.dual} {C : DTree M} {vs ts : List V}
    {fs cs : List F} (hI : KInit M σ ιv ιf n k T C vs ts fs cs P) {c : Config}
    (hc : WordsBounded W c) {Fo : Forest} {G : List VT} (hS : LCTE B n Fo G c) :
    ∃ c' G', ORunC P W H B n (inPS nD n k) c Fo G c' [] G' 0 (13 * Fintype.card V + 5) ∧
      (∀ x, x ≠ T.root → c'.nmem (aTP + ιv x) = σ (T.par x)) ∧
      (∀ r, r < 110 → c'.nreg r = c.nreg r ∧ c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      c'.rmem = c.rmem ∧ (∀ a, n ≤ a → c'.nmem a = c.nmem a) := by
  obtain ⟨c', G', o, h⟩ := inP_orunNL hW hWa hB hP hL hK hI hc hS
  exact ⟨c', G', ORunC.of_noTestR o (by rfl), h⟩

/-- **The initialisation on the machine with bounded comparisons** (`in_orun`): when the total
size of the additions of its operations is at most `Vb` and `2 Vb ≤ H`, the run of `inS` is
compare-bounded by `H`, and the forest at the end has values at most `Vb`. -/
theorem in_orunCNL (hW : B + 16 * (n + 1) ≤ W) {k : ℕ} (hWa : 9 * nD + 7 * n + k + 4 ≤ W)
    (hB : n + 2 * nD ≤ B) (hB3 : 3 * nD + 3 ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W)
    {S : Finset D} {ℓ : D → ℤ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ}
    (hL : Layout M n ιv ιg ιf ιe) (hK : KInputNL M S ℓ σ ιv ιg ιf ιe P) {T : DTree M.dual}
    {C : DTree M} {vs ts : List V} {fs cs : List F} (hI : KInit M σ ιv ιf n k T C vs ts fs cs P)
    (hoff : ∀ x, x ≠ C.root → ¬ T.InT (C.par x)) {wt φ : D → ℤ} {H₀ : ℤ} {c : Config}
    (hc : WordsBounded W c) {G : List VT} (hS : LCTE B n (Forest.init n) G c)
    (hwt : ∀ d, c.rmem (aWT + σ d) = wt d) (hph : ∀ d, c.rmem (aPH nD + σ d) = φ d)
    (hH0 : c.rmem (aH0 nD) = H₀) {Vb : ℝ} (hH : 2 * Vb ≤ H)
    (hZ : zsum (treeOpsL T ιv ιg φ vs ts ++ cotOpsL C ιf ιe
      (fun d => wt d + T.psum φ (M.tail d) - T.psum φ (M.head d)) H₀ fs cs) ≤ Vb) :
    ∃ c' G' os, ORunC P W H B n (inS B nD n k) c (Forest.init n) G c' os G'
        (6 * (Fintype.card V + Fintype.card F) + 2 * nD)
        (60 * (Fintype.card V + Fintype.card F) + 20 * nD + 42) ∧
      os.length ≤ 6 * (Fintype.card V + Fintype.card F) ∧
      (runOpsE n (Forest.init n) os).2 = [] ∧
      Stored M n ιv ιg ιf ιe φ C.root H₀ (runOpsE n (Forest.init n) os).1 T
        (fun d => wt d + T.psum φ (M.tail d) - T.psum φ (M.head d)) ∧
      KMem M σ ιv T wt φ c' ∧
      (∀ r, r < 110 → c'.nreg r = c.nreg r ∧ c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → n ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (a < aVL nD ∨ aVL nD + nD ≤ a) →
        c'.rmem a = c.rmem a) ∧
      VBnd Vb n (runOpsE n (Forest.init n) os).1 := by
  set val : D → ℤ := fun d => wt d + T.psum φ (M.tail d) - T.psum φ (M.head d) with hval
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  have hV0 : VBnd 0 n (Forest.init n) := fun u _ => by simp [Forest.init]
  have hAll : AllV Vb n (Forest.init n) (treeOpsL T ιv ιg φ vs ts ++ cotOpsL C ιf ιe val H₀ fs
      cs) := (allV_of_vbnd _ hV0).mono (by linarith)
  have hAT := AllV.left hAll
  have hAC := AllV.right hAll
  obtain ⟨hlen, hv, ho, hSt⟩ := init_storedL hL hoff φ val H₀ hI.oT hI.oC
  obtain ⟨-, hvT, -, hRT, -, -, -⟩ := tree_storedL (ιf := ιf) (ιe := ιe) hL φ hI.oT
  obtain ⟨-, hvC⟩ := (validOpsE_append_iff n _ _ _).1 hv
  set F1 := (runOpsE n (Forest.init n) (treeOpsL T ιv ιg φ vs ts)).1 with hF1
  have hVF1 : VBnd Vb n F1 := hAC.vbnd
  -- the spanning tree
  obtain ⟨c₁, G₁, o₁, r₁, out₁, m₁⟩ := inT_orunCNL hW hWa hB hP hL hK hI hvT hH hAT hc hS hph
  -- its parent darts
  obtain ⟨c₂, G₂, o₂, tp₂, r₂, out₂, rm₂, nm₂⟩ := inP_orunCNL (H := H) hW hWa hB hP hL hK hI
    o₁.1.2.wb o₁.1.2.lcte
  -- the values of the darts
  obtain ⟨c₃, G₃, o₃, vl₃, r₃, out₃, nm₃, rm₃⟩ := inV_orunC (P := P) (σ := σ) hW (by omega) hB3
    hP hL.prim.f_lt hK.nt hK.nh o₂.1.2.wb o₂.1.2.lcte hVF1 hH
  have hvl : ∀ d, c₃.rmem (aVL nD + σ d) = ((val d : ℤ) : ℝ) := fun d => by
    have hd := hσ d
    rw [vl₃, rm₂, (m₁ _ (Or.inl (by unfold aWT; omega))).2, hwt]
    change (wt d : ℝ) + pathSum F1 n _ - pathSum F1 n _ = _
    rw [lct_label hRT hL.prim.f_lt hL.prim.e_lt hL.hv,
      lct_label hRT hL.prim.f_lt hL.prim.e_lt hL.hv]
    simp only [hval]; push_cast; ring
  have hH0₃ : c₃.rmem (aH0 nD) = H₀ := by
    rw [rm₃ _ (Or.inl (by unfold aH0; omega)) (Or.inr (by unfold aH0 aVL; omega)), rm₂,
      (m₁ _ (Or.inl (by unfold aH0; omega))).2, hH0]
  -- the cotree
  obtain ⟨c₄, G₄, o₄, f₄⟩ := inC_orunCNL hW hWa hB3 hP hL hK hI hvC hH hAC o₃.1.2.wb o₃.1.2.lcte
    hvl hH0₃
  have o := o₁.seq (o₂.seq (o₃.seq o₄))
  simp only [List.nil_append] at o
  refine ⟨c₄, G₄, _, o.mono (by omega) (by omega), hlen, ho, hSt, ⟨fun x hx => ?_, fun d => ?_,
    fun d => ?_⟩, fun r hr => ?_, ?_, fun a ha han => ?_, fun a ha ha' => ?_,
    (vbnd_runOps _ hV0).mono (by linarith)⟩
  · have := hL.prim.f_lt x
    rw [(f₄.2.2 _ (Or.inl (by unfold aTP; omega))).1, nm₃ _ (Or.inl (by unfold aTP; omega))]
    exact tp₂ x hx
  · have := hσ d
    rw [(f₄.2.2 _ (Or.inl (by unfold aWT; omega))).2,
      rm₃ _ (Or.inl (by unfold aWT; omega)) (Or.inl (by unfold aWT aVL; omega)), rm₂,
      (m₁ _ (Or.inl (by unfold aWT; omega))).2, hwt]
  · have := hσ d
    rw [(f₄.2.2 _ (Or.inl (by unfold aPH; omega))).2,
      rm₃ _ (Or.inl (by unfold aPH; omega)) (Or.inl (by unfold aPH aVL; omega)), rm₂,
      (m₁ _ (Or.inl (by unfold aPH; omega))).2, hph]
  · rw [(f₄.1 r hr).1, (f₄.1 r hr).2, (r₃ r hr).1, (r₃ r hr).2, (r₂ r hr).1, (r₂ r hr).2]
    exact r₁ r hr
  · rw [f₄.2.1, out₃, out₂, out₁]
  · rw [(f₄.2.2 a ha).1, nm₃ a ha, nm₂ a han, (m₁ a ha).1]
  · rw [(f₄.2.2 a ha).2, rm₃ a ha ha', rm₂, (m₁ a ha).2]

end

end Klein

end PlanarFlow
