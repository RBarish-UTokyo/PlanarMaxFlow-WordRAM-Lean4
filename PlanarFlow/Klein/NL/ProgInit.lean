module

public import PlanarFlow.Klein.ProgInit
public import PlanarFlow.Klein.NL.ProgMove
public import PlanarFlow.Klein.NL.ProgNext
public import PlanarFlow.Klein.NL.ProgPivot
public import PlanarFlow.Klein.NL.ProgWeight
public import PlanarFlow.Klein.NL.Input

/-! Copy of `PlanarFlow.Klein.ProgInit` for `KInputNL` (generated mechanically). -/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs

section
variable {P : Input} {W B n : ℕ}

end

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {nD : ℕ} {σ : D ≃ Fin nD}

section
variable {P : Input} {W B n : ℕ}

end

section
variable {P : Input} {W B n : ℕ}

/-- **The spanning tree stored on the machine**: `inTS` performs `treeOpsL`, counted `6 #V`
operations and `45 #V + 16` further steps. -/
theorem inT_orunNL (hW : B + 16 * (n + 1) ≤ W) {k : ℕ} (hWa : 9 * nD + 7 * n + k + 4 ≤ W)
    (hB : n + 2 * nD ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W) {S : Finset D} {ℓ : D → ℤ}
    {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInputNL M S ℓ σ ιv ιg ιf ιe P) {T : DTree M.dual} {C : DTree M} {vs ts : List V}
    {fs cs : List F} (hI : KInit M σ ιv ιf n k T C vs ts fs cs P) {φ : D → ℤ}
    (hv : ValidOpsE n (Forest.init n) (treeOpsL T ιv ιg φ vs ts)) {c : Config}
    (hc : WordsBounded W c) {G : List VT} (hS : LCTE B n (Forest.init n) G c)
    (hph : ∀ d, c.rmem (aPH nD + σ d) = φ d) :
    ∃ c' G', ORun P W B n (inTS B nD n k) c (Forest.init n) G c' (treeOpsL T ιv ιg φ vs ts)
        G' (6 * Fintype.card V) (45 * Fintype.card V + 16) ∧
      (∀ r, r < 110 → c'.nreg r = c.nreg r ∧ c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a := by
  have hvl := hI.oT.flen
  have htl := hI.oT.ylen
  have hVn : 2 * Fintype.card V ≤ n := hL.hv
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  rw [treeOpsL_eq T φ hI.oT] at hv ⊢
  obtain ⟨hvAB, hvC⟩ := (validOpsE_append_iff n _ _ _).1 hv
  obtain ⟨hvA, hvB⟩ := (validOpsE_append_iff n _ _ _).1 hvAB
  rw [runOpsE_fst_append] at hvC
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
  have o₁ := ORun.ofGFr e₁ hS g₁ (by omega)
  obtain ⟨c₂, G₂, o₂, q₂⟩ := listLoop_orun (P := P) (W := W) (B := B) (n := n) (ra := 120)
    (rb := 121) vs (fun y => [EOp.add (ιv y) 0, .add2 (ιv y) 0]) hvA (fun _ c' => IFr B n c₁ c')
    (body := bodyNV B (iIV nD n k) 110) (mb := 2) (hb := 5)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := bodyNV_orun hW hP hI.iv (by unfold iIV; omega) hi hc' hS'
        h120 (z := 0) (by rw [hQ.2.1 110 (by omega), p110]) (by omega) hvi
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega), p121]⟩)
    e₁.wb_right o₁.2.lcte (IFr.refl _ _ _) p120 p121
  -- the values of the nodes of the edges
  obtain ⟨c₃, k₃, e₃, hk₃, s120, s121, g₃⟩ := ldI_exec (P := P) o₂.2.wb hP
    (off := iHD nD n k + 1) (by unfold iHD iIV; omega)
  have o₃ := ORun.ofGFr e₃ o₂.2.lcte g₃ (by omega)
  have hph₃ : ∀ d, c₃.rmem (aPH nD + σ d) = φ d := fun d => by
    have := hσ d
    rw [g₃.2.2.1, (q₂.2.2.2 _ (Or.inl (by unfold aPH; omega))).2, g₁.2.2.1, hph]
  obtain ⟨c₄, G₄, o₄, q₄⟩ := listLoop_orun (P := P) (W := W) (B := B) (n := n) (ra := 120)
    (rb := 121) ts (fun y => eopsDV false (ιg (T.par y)) (φ (T.par y)) (φ (M.rev (T.par y))))
    hvB (fun _ c' => IFr B n c₃ c') (body := bodyDV B nD (iIT nD n k) (iNG nD) (aPH nD)
      (opsDV false)) (mb := 2) (hb := 17)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := bodyDV_orun (aA := aPH nD) (A := φ) hW hP hK.rv
        hI.it (by unfold iIT iIV; omega) hK.ng (by unfold iNG; omega)
        (by unfold aPH; omega) false hi hc' hS' h120 (fun d => by
          have := hσ d
          rw [(hQ.2.2.2 _ (Or.inl (by unfold aPH; omega))).2, hph₃]) hvi
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega), s121,
        hI.l1]⟩)
    e₃.wb_right o₃.2.lcte (IFr.refl _ _ _) s120 (by rw [s121, hI.l1])
  -- the links
  obtain ⟨c₅, k₅, e₅, hk₅, t120, t121, g₅⟩ := ldI_exec (P := P) o₄.2.wb hP
    (off := iHD nD n k + 1) (by unfold iHD iIV; omega)
  have o₅ := ORun.ofGFr e₅ o₄.2.lcte g₅ (by omega)
  obtain ⟨c₆, G₆, o₆, q₆⟩ := listLoop_orun (P := P) (W := W) (B := B) (n := n) (ra := 120)
    (rb := 121) ts (fun y => [EOp.link (ιg (T.par y)) (ιv (M.tail (T.par y))),
      .link (ιv (M.tail (M.rev (T.par y)))) (ιg (T.par y))])
    hvC (fun _ c' => IFr B n c₅ c') (body := bodyLK B nD (iIT nD n k) (iNG nD) (iNT nD))
    (mb := 2) (hb := 17)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := bodyLK_orun hW hP hK.rv hI.it
        (by unfold iIT iIV; omega) hK.ng (by unfold iNG; omega) hK.nt (by unfold iNT; omega)
        hi hc' hS' h120 hvi
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega), t121,
        hI.l1]⟩)
    e₅.wb_right o₅.2.lcte (IFr.refl _ _ _) t120 (by rw [t121, hI.l1])
  have o := o₁.seq (o₂.seq (o₃.seq (o₄.seq (o₅.seq o₆))))
  simp only [List.nil_append] at o
  have hfr : IFr0 B n c c₆ := (((((g₁.to0 (by omega)).trans q₂.to0).trans
    (g₃.to0 (by omega))).trans q₄.to0).trans (g₅.to0 (by omega))).trans q₆.to0
  refine ⟨c₆, G₆, ?_, hfr.1, hfr.2.1, hfr.2.2⟩
  rw [List.append_assoc]; exact o.mono (by omega) (by omega)

/-- **The cotree stored on the machine**: `inCS` performs `cotOpsL` (the values from `VL` and
`H0`), counted `6 #F` operations and `45 #F + 17` further steps. -/
theorem inC_orunNL (hW : B + 16 * (n + 1) ≤ W) {k : ℕ} (hWa : 9 * nD + 7 * n + k + 4 ≤ W)
    (hB3 : 3 * nD + 3 ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W) {S : Finset D} {ℓ : D → ℤ}
    {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInputNL M S ℓ σ ιv ιg ιf ιe P) {T : DTree M.dual} {C : DTree M} {vs ts : List V}
    {fs cs : List F} (hI : KInit M σ ιv ιf n k T C vs ts fs cs P) {val : D → ℤ} {H₀ : ℤ}
    {F₁ : Forest} (hv : ValidOpsE n F₁ (cotOpsL C ιf ιe val H₀ fs cs)) {c : Config}
    (hc : WordsBounded W c) {G : List VT} (hS : LCTE B n F₁ G c)
    (hvl : ∀ d, c.rmem (aVL nD + σ d) = val d) (hH0 : c.rmem (aH0 nD) = H₀) :
    ∃ c' G', ORun P W B n (inCS B nD n k) c F₁ G c' (cotOpsL C ιf ιe val H₀ fs cs) G'
        (6 * Fintype.card F) (45 * Fintype.card F + 17) ∧ IFr0 B n c c' := by
  have hfl := hI.oC.flen
  have hcl := hI.oC.ylen
  have hFn : 2 * Fintype.card F ≤ n := hL.hf
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  rw [cotOpsL_eq C val H₀ hI.oC] at hv ⊢
  obtain ⟨hvAB, hvC⟩ := (validOpsE_append_iff n _ _ _).1 hv
  obtain ⟨hvA, hvB⟩ := (validOpsE_append_iff n _ _ _).1 hvAB
  rw [runOpsE_fst_append] at hvC
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
  have o₁ := ORun.ofGFr e₁ hS g₁ (by omega)
  obtain ⟨c₂, G₂, o₂, q₂⟩ := listLoop_orun (P := P) (W := W) (B := B) (n := n) (ra := 120)
    (rb := 121) fs (fun y => [EOp.add (ιf y) H₀, .add2 (ιf y) H₀]) hvA
    (fun _ c' => IFr B n c₁ c') (body := bodyNV B (iIF nD n k) 111) (mb := 2) (hb := 5)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := bodyNV_orun hW hP hI.if_ (by unfold iIF iIV; omega) hi hc'
        hS' h120 (z := H₀) (by rw [hQ.2.1 111 (by omega), p111]) (by omega) hvi
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega), p121]⟩)
    e₁.wb_right o₁.2.lcte (IFr.refl _ _ _) p120 p121
  -- the values of the nodes of the edges
  obtain ⟨c₃, k₃, e₃, hk₃, s120, s121, g₃⟩ := ldI_exec (P := P) o₂.2.wb hP
    (off := iHD nD n k + 3) (by unfold iHD iIV; omega)
  have o₃ := ORun.ofGFr e₃ o₂.2.lcte g₃ (by omega)
  have hvl₃ : ∀ d, c₃.rmem (aVL nD + σ d) = val d := fun d => by
    have := hσ d
    rw [g₃.2.2.1, (q₂.2.2.2 _ (Or.inl (by unfold aVL; omega))).2, g₁.2.2.1, hvl]
  obtain ⟨c₄, G₄, o₄, q₄⟩ := listLoop_orun (P := P) (W := W) (B := B) (n := n) (ra := 120)
    (rb := 121) cs (fun y => eopsDV true (ιe (C.par y)) (val (C.par y)) (val (M.rev (C.par y))))
    hvB (fun _ c' => IFr B n c₃ c') (body := bodyDV B nD (iIC nD n k) (iNE nD) (aVL nD)
      (opsDV true)) (mb := 2) (hb := 17)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := bodyDV_orun (aA := aVL nD) (A := val) hW hP hK.rv
        hI.ic (by unfold iIC iIV; omega) hK.ne (by unfold iNE; omega)
        (by unfold aVL; omega) true hi hc' hS' h120 (fun d => by
          have := hσ d
          rw [(hQ.2.2.2 _ (Or.inl (by unfold aVL; omega))).2, hvl₃]) hvi
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega), s121,
        hI.l3]⟩)
    e₃.wb_right o₃.2.lcte (IFr.refl _ _ _) s120 (by rw [s121, hI.l3])
  -- the links
  obtain ⟨c₅, k₅, e₅, hk₅, t120, t121, g₅⟩ := ldI_exec (P := P) o₄.2.wb hP
    (off := iHD nD n k + 3) (by unfold iHD iIV; omega)
  have o₅ := ORun.ofGFr e₅ o₄.2.lcte g₅ (by omega)
  obtain ⟨c₆, G₆, o₆, q₆⟩ := listLoop_orun (P := P) (W := W) (B := B) (n := n) (ra := 120)
    (rb := 121) cs (fun y => [EOp.link (ιe (C.par y)) (ιf (M.face (C.par y))),
      .link (ιf (M.face (M.rev (C.par y)))) (ιe (C.par y))])
    hvC (fun _ c' => IFr B n c₅ c') (body := bodyLK B nD (iIC nD n k) (iNE nD) (iNF nD))
    (mb := 2) (hb := 17)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := bodyLK_orun hW hP hK.rv hI.ic
        (by unfold iIC iIV; omega) hK.ne (by unfold iNE; omega) hK.nf (by unfold iNF; omega)
        hi hc' hS' h120 hvi
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega), t121,
        hI.l3]⟩)
    e₅.wb_right o₅.2.lcte (IFr.refl _ _ _) t120 (by rw [t121, hI.l3])
  have o := o₁.seq (o₂.seq (o₃.seq (o₄.seq (o₅.seq o₆))))
  simp only [List.nil_append] at o
  have hfr : IFr0 B n c c₆ := (((((g₁.to0 (by omega)).trans q₂.to0).trans
    (g₃.to0 (by omega))).trans q₄.to0).trans (g₅.to0 (by omega))).trans q₆.to0
  refine ⟨c₆, G₆, ?_, hfr⟩
  rw [List.append_assoc]; exact o.mono (by omega) (by omega)

/-- **The parent darts of the spanning tree into `TP`** (no operation). -/
theorem inP_orunNL (hW : B + 16 * (n + 1) ≤ W) {k : ℕ} (hWa : 9 * nD + 7 * n + k + 4 ≤ W)
    (hB : n + 2 * nD ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W) {S : Finset D} {ℓ : D → ℤ}
    {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInputNL M S ℓ σ ιv ιg ιf ιe P) {T : DTree M.dual} {C : DTree M} {vs ts : List V}
    {fs cs : List F} (hI : KInit M σ ιv ιf n k T C vs ts fs cs P) {c : Config}
    (hc : WordsBounded W c) {Fo : Forest} {G : List VT} (hS : LCTE B n Fo G c) :
    ∃ c' G', ORun P W B n (inPS nD n k) c Fo G c' [] G' 0 (13 * Fintype.card V + 5) ∧
      (∀ x, x ≠ T.root → c'.nmem (aTP + ιv x) = σ (T.par x)) ∧
      (∀ r, r < 110 → c'.nreg r = c.nreg r ∧ c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      c'.rmem = c.rmem ∧ (∀ a, n ≤ a → c'.nmem a = c.nmem a) := by
  have htl := hI.oT.ylen
  have hVn : 2 * Fintype.card V ≤ n := hL.hv
  have hvn := hL.prim.f_lt
  obtain ⟨c₁, k₁, e₁, hk₁, p120, p121, g₁⟩ := ldI_exec (P := P) hc hP
    (off := iHD nD n k + 1) (by unfold iHD iIV; omega)
  have o₁ := ORun.ofGFr e₁ hS g₁ (by omega)
  have hhd : ∀ i (h : i < ts.length), M.head (T.par ts[i]) = ts[i] := fun i h =>
    tpar_head T ((hI.oT.ymem _).1 (List.getElem_mem h))
  obtain ⟨c₂, G₂, o₂, q₁, q₂, q₃, q₄, q₅, q₆⟩ := listLoop_orun (P := P) (W := W) (B := B) (n := n)
    (ra := 120) (rb := 121) ts (fun _ => ([] : List EOp)) (F₀ := Fo)
    (by rw [flatMap_nil']; trivial)
    (fun i c' => (∀ r, (r < 120 ∨ r = 121 ∨ r = 151) → c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output ∧
      (∀ a, (∀ x : V, a ≠ aTP + ιv x) → c'.nmem a = c₁.nmem a) ∧
      ∀ i' (h : i' < ts.length), i' < i → c'.nmem (aTP + ιv ts[i']) = σ (T.par ts[i']))
    (body := block (bodyTP nD n k)) (mb := 0) (hb := 11)
    (fun i hi c' G' hQ hc' hS' h120 _ _ => by
      obtain ⟨c₃, k₃, e₃, hk₃, q120, qn, qr, qm, qrm, qout⟩ := bodyTP_exec (P := P) hP hvn hK.nh
        (by unfold iNH; omega) hI.it (by unfold iIT iIV; omega) hi hc' h120 (by omega)
      rw [hhd i hi] at qm
      subst hk₃
      refine ⟨c₃, G', ORun.glue e₃ hS' (fun a ha _ => ⟨?_, by rw [qrm]⟩) (qn 151 (by omega)),
        ⟨fun r hr => by rw [qn r hr]; exact hQ.1 r hr, by rw [qr]; exact hQ.2.1,
          by rw [qrm]; exact hQ.2.2.1, by rw [qout]; exact hQ.2.2.2.1, fun a ha => ?_,
          fun i' h hi' => ?_⟩, q120, by rw [qn 121 (by omega), hQ.1 121 (by omega), p121,
          hI.l1]⟩
      · rw [qm, upd_other _ _ _ (by have := hvn ts[i]; unfold aTP; omega)]
      · rw [qm, upd_other _ _ _ (ha _)]; exact hQ.2.2.2.2.1 a ha
      · rw [qm]
        rcases Nat.lt_or_ge i' i with h' | h'
        · have hne : ts[i'] ≠ ts[i] := fun h'' => by
            have := (List.Nodup.getElem_inj_iff hI.oT.ynd).1 h''; omega
          rw [upd_other _ _ _ (fun h'' => hne (hL.prim.f_inj (by unfold aTP at h''; omega)))]
          exact hQ.2.2.2.2.2 i' h h'
        · obtain rfl : i' = i := by omega
          rw [upd_same])
    e₁.wb_right o₁.2.lcte ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl,
      fun _ _ h => absurd h (Nat.not_lt_zero _)⟩ p120 (by rw [p121, hI.l1])
  rw [flatMap_nil'] at o₂
  have o := o₁.seq o₂
  refine ⟨c₂, G₂, o.mono (by simp) (by omega), fun x hx => ?_, fun r hr => ?_, ?_, ?_,
    fun a ha => ?_⟩
  · obtain ⟨i', h, rfl⟩ := List.getElem_of_mem ((hI.oT.ymem x).2 hx)
    exact q₆ i' h h
  · rw [q₁ r (by omega), q₂, (g₁.1 r (by omega)).1, (g₁.1 r (by omega)).2]; exact ⟨rfl, rfl⟩
  · rw [q₄, g₁.2.2.2]
  · rw [q₃, g₁.2.2.1]
  · rw [q₅ a (fun x h => by have := hvn x; unfold aTP at h; omega), g₁.2.1]

/-- **The initialisation on the machine.** From the empty forest stored at `B` (and `r151 = n`),
the input holding the map (`KInputNL`) and the initial trees (`KInit`, the cotree `C` with its
parent darts off `T`), the real memory holding weights `wt` in `WT`, `φ` in `PH` and `H₀` in
`H0`, the program `inS` performs the operations `treeOpsL ++ cotOpsL` of `init_storedL` (at most
`6 (#V + #F)`), counted `6 (#V + #F) + 2 nD` operations and `60 (#V + #F) + 20 nD + 42` further
steps; the forest stores `T` with the weights `φ` and `C` with the values
`wt d + psum (tail d) - psum (head d)` and `H₀` at the nodes of the faces, and `TP`, `WT`, `PH`
hold `T`, `wt`, `φ` (`KMem`). It keeps the registers below `r110`, the output, the natural
memory outside the structure from `n` on, and the real memory outside the structure and `VL`. -/
theorem in_orunNL (hW : B + 16 * (n + 1) ≤ W) {k : ℕ} (hWa : 9 * nD + 7 * n + k + 4 ≤ W)
    (hB : n + 2 * nD ≤ B) (hB3 : 3 * nD + 3 ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W)
    {S : Finset D} {ℓ : D → ℤ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ}
    (hL : Layout M n ιv ιg ιf ιe) (hK : KInputNL M S ℓ σ ιv ιg ιf ιe P) {T : DTree M.dual}
    {C : DTree M} {vs ts : List V} {fs cs : List F} (hI : KInit M σ ιv ιf n k T C vs ts fs cs P)
    (hoff : ∀ x, x ≠ C.root → ¬ T.InT (C.par x)) {wt φ : D → ℤ} {H₀ : ℤ} {c : Config}
    (hc : WordsBounded W c) {G : List VT} (hS : LCTE B n (Forest.init n) G c)
    (hwt : ∀ d, c.rmem (aWT + σ d) = wt d) (hph : ∀ d, c.rmem (aPH nD + σ d) = φ d)
    (hH0 : c.rmem (aH0 nD) = H₀) :
    ∃ c' G' os, ORun P W B n (inS B nD n k) c (Forest.init n) G c' os G'
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
        c'.rmem a = c.rmem a) := by
  set val : D → ℤ := fun d => wt d + T.psum φ (M.tail d) - T.psum φ (M.head d) with hval
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  obtain ⟨hlen, hv, ho, hSt⟩ := init_storedL hL hoff φ val H₀ hI.oT hI.oC
  obtain ⟨-, hvT, -, hRT, -, -, -⟩ := tree_storedL (ιf := ιf) (ιe := ιe) hL φ hI.oT
  obtain ⟨-, hvC⟩ := (validOpsE_append_iff n _ _ _).1 hv
  set F1 := (runOpsE n (Forest.init n) (treeOpsL T ιv ιg φ vs ts)).1 with hF1
  -- the spanning tree
  obtain ⟨c₁, G₁, o₁, r₁, out₁, m₁⟩ := inT_orunNL hW hWa hB hP hL hK hI hvT hc hS hph
  -- its parent darts
  obtain ⟨c₂, G₂, o₂, tp₂, r₂, out₂, rm₂, nm₂⟩ := inP_orunNL hW hWa hB hP hL hK hI o₁.2.wb
    o₁.2.lcte
  -- the values of the darts
  obtain ⟨c₃, G₃, o₃, vl₃, r₃, out₃, nm₃, rm₃⟩ := inV_orun (P := P) (σ := σ) hW (by omega) hB3 hP
    hL.prim.f_lt hK.nt hK.nh o₂.2.wb o₂.2.lcte
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
  obtain ⟨c₄, G₄, o₄, f₄⟩ := inC_orunNL hW hWa hB3 hP hL hK hI hvC o₃.2.wb o₃.2.lcte hvl hH0₃
  have o := o₁.seq (o₂.seq (o₃.seq o₄))
  simp only [List.nil_append] at o
  refine ⟨c₄, G₄, _, o.mono (by omega) (by omega), hlen, ho, hSt, ⟨fun x hx => ?_, fun d => ?_,
    fun d => ?_⟩, fun r hr => ?_, ?_, fun a ha han => ?_, fun a ha ha' => ?_⟩
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
