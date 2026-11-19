module

public import PlanarFlow.BKMNW.MbLab
public import PlanarFlow.BKMNW.MbSide
public import PlanarFlow.BKMNW.ExistCertD
public import PlanarFlow.BKMNW.ItemsD

/-!
# Miller's base, step 6: what the marks and labels mean

Pure lemmas turning the arrays computed by `kmk`/`lbl` into the objects of `scBase`:

* **`itemRep_two`**: labels `1` on `X`, `2` on `Y` (disjoint), `0` elsewhere represent `{X, Y}`;
* **`kmHit_iff`**: a key is marked by the cycle codes iff it is the key of a dart whose vertex is
  on the separator cycle (the codes `3 q`, `3 q + 1` of `stNum`; the vertex of `φ q` is that of
  `α q`);
* **`onC_iff`** (marked key of `x` ⟺ the vertex of `x` is on the cycle), **`nh_iff`** (marked key
  of `v` ⟺ `v ∈ newHole Hs (corePath C).mverts`, by `stellar_cycle_path'` and
  `mem_newHole_iff`);
* **`core_iff`** (the two sides from the cycle and the face mark of the triangle of `x`),
  **`zmark_iff`** (the normalised face mark), **`lab_eq`** (the value `lbV` is the label of the
  item of `x`);
* **`sepC_facts`** (the separator `sepC` returns on a piece map: a cycle separator, its path
  simple), `psep_hsc`, `psep_hsm`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset

/-! ### Two items as labels -/

section ItemTwo

variable {D : Type*} [DecidableEq D]

/-- **Two disjoint items as labels `1`, `2`.** -/
theorem itemRep_two {e : ℕ → D} {n : ℕ} {X Y : Finset D} {lab : ℕ → ℕ}
    (hXY : Disjoint X Y) (hX : ∀ d ∈ X, ∃ i < n, e i = d) (hY : ∀ d ∈ Y, ∃ i < n, e i = d)
    (hlab : ∀ i < n, lab i = if e i ∈ X then 1 else if e i ∈ Y then 2 else 0) :
    ItemRep e n {X, Y} lab := by
  have c1 : clsL e n lab 1 = X := by
    ext d; rw [mem_clsL]; constructor
    · rintro ⟨j, hj, h, rfl⟩
      rw [hlab j hj] at h
      split_ifs at h with h1 h2
      all_goals first | assumption | omega
    · intro hd
      obtain ⟨i, hi, rfl⟩ := hX d hd
      exact ⟨i, hi, by rw [hlab i hi, iteT hd], rfl⟩
  have c2 : clsL e n lab 2 = Y := by
    ext d; rw [mem_clsL]; constructor
    · rintro ⟨j, hj, h, rfl⟩
      rw [hlab j hj] at h
      split_ifs at h with h1 h2
      all_goals first | assumption | omega
    · intro hd
      obtain ⟨i, hi, rfl⟩ := hY d hd
      have : e i ∉ X := fun h => disjoint_left.1 hXY h hd
      exact ⟨i, hi, by rw [hlab i hi, iteF this, iteT hd], rfl⟩
  unfold ItemRep
  ext S
  rw [mem_labItems, mem_erase, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hne, rfl | rfl⟩
    · obtain ⟨d, hd⟩ := nonempty_iff_ne_empty.2 hne
      obtain ⟨i, hi, rfl⟩ := hX d hd
      exact ⟨i, hi, by rw [hlab i hi, iteT hd]; omega, by rw [hlab i hi, iteT hd, c1]⟩
    · obtain ⟨d, hd⟩ := nonempty_iff_ne_empty.2 hne
      obtain ⟨i, hi, rfl⟩ := hY d hd
      have : e i ∉ X := fun h => disjoint_left.1 hXY h hd
      exact ⟨i, hi, by rw [hlab i hi, iteF this, iteT hd]; omega,
        by rw [hlab i hi, iteF this, iteT hd, c2]⟩
  · rintro ⟨i, hi, hl, rfl⟩
    have hl' := hlab i hi
    split_ifs at hl' with h1 h2
    · rw [hl', c1]; exact ⟨ne_empty_of_mem h1, Or.inl rfl⟩
    · rw [hl', c2]; exact ⟨ne_empty_of_mem h2, Or.inr rfl⟩
    · exact absurd hl' hl

end ItemTwo

/-! ### The cycle marks -/

section Marks

open Function Equiv Orbit CombMap PlanarSeparator PlanarSeparator.Map PlanarSeparator.StDart

variable {X Q : Type*} [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
  {Mp : PlanarSeparator.Map X Q}

lemma stNum_up_φ {m : ℕ} (cd : X ≃ Fin m) (z : X) :
    Mp.stNum cd (up (Mp.φ z)) = 3 * cd z + 1 := by
  simp [stNum]

/-- **The keys marked by the cycle codes**: `x` is marked iff it is the key `K y` of a dart `y`
whose vertex is on the cycle. -/
theorem kmHit_iff {m : ℕ} (cd : X ≃ Fin m) (C : Mp.stellar.SCycle) (K : X → ℕ)
    (hKv : ∀ y y', Mp.vert y = Mp.vert y' → K y = K y') {mem : ℕ → ℕ} {CYb TKCb CRb : ℕ}
    (hCY : ∀ l < C.k, mem (CYb + l) = Mp.stNum cd (C.d l))
    (hT : ∀ y, mem (TKCb + cd y) = K y) (hCR : ∀ y, mem (CRb + cd y) = cd (Mp.α y)) (x : ℕ) :
    (∃ l < C.k, kmHit mem CYb TKCb CRb l x) ↔
      ∃ l < C.k, ∃ y, Mp.stellar.vert (C.d l) = .inl (Mp.vert y) ∧ K y = x := by
  constructor
  · rintro ⟨l, hl, h⟩
    refine ⟨l, hl, ?_⟩
    unfold kmHit at h
    rw [hCY l hl] at h
    rcases hd : C.d l with y | e' | d
    · rw [hd] at h
      simp only [stNum] at h
      have h3 : 3 * (cd y : ℕ) / 3 = cd y := by omega
      rw [h3, hT] at h
      refine ⟨y, rfl, ?_⟩
      rcases h with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · omega
    · rw [hd] at h
      obtain ⟨z, rfl⟩ : ∃ z, e' = Mp.φ z := ⟨Mp.φ.symm e', by simp⟩
      rw [stNum_up_φ] at h
      have h3 : (3 * (cd z : ℕ) + 1) / 3 = cd z := by omega
      simp only [h3, hCR, hT] at h
      refine ⟨Mp.α z, ?_, ?_⟩
      · simp only [stellar_vert_up, Sum.inl.injEq, φ_apply, Mp.vert_σ]
      · rcases h with ⟨h, -⟩ | ⟨-, h⟩
        · omega
        · exact h
    · rw [hd] at h
      simp only [stNum] at h
      omega
  · rintro ⟨l, hl, y, hv, hy⟩
    refine ⟨l, hl, ?_⟩
    unfold kmHit
    rw [hCY l hl]
    rcases hd : C.d l with y' | e' | d
    · rw [hd] at hv
      simp only [stellar_vert_old, Sum.inl.injEq] at hv
      simp only [stNum]
      have h3 : 3 * (cd y' : ℕ) / 3 = cd y' := by omega
      simp only [h3, hT]
      rw [← hKv _ _ hv] at hy
      exact Or.inl ⟨by omega, hy⟩
    · rw [hd] at hv
      obtain ⟨z, rfl⟩ : ∃ z, e' = Mp.φ z := ⟨Mp.φ.symm e', by simp⟩
      simp only [stellar_vert_up, Sum.inl.injEq, φ_apply, Mp.vert_σ] at hv
      rw [stNum_up_φ]
      have h3 : (3 * (cd z : ℕ) + 1) / 3 = cd z := by omega
      simp only [h3, hCR, hT]
      rw [← hKv _ _ hv] at hy
      exact Or.inr ⟨by omega, hy⟩
    · rw [hd] at hv
      simp at hv

/-- **A marked key is a vertex on the cycle.** -/
theorem onC_iff (C : Mp.stellar.SCycle) (K : X → ℕ)
    (hKv : ∀ y y', K y = K y' ↔ Mp.vert y = Mp.vert y') (x : X) :
    (∃ l < C.k, ∃ y, Mp.stellar.vert (C.d l) = .inl (Mp.vert y) ∧ K y = K x) ↔
      (.inl (Mp.vert x) : Q ⊕ Mp.Face) ∈ C.verts := by
  rw [SCycle.mem_verts]
  constructor
  · rintro ⟨l, hl, y, hv, hy⟩
    exact ⟨l, hl, by rw [hv, (hKv y x).1 hy]⟩
  · rintro ⟨l, hl, hv⟩
    exact ⟨l, hl, x, hv, rfl⟩

/-- The face numbering of the triangle of a dart. -/
lemma stFn_old {m : ℕ} (cd : X ≃ Fin m) (x : X) :
    (Mp.stFn cd (Mp.stellar.face (old x)) : ℕ) = cd x := by
  rw [stFn_face]; simp only [stCode_val, stNum]; omega

/-- **The normalised face mark of the triangle of `x`.** -/
theorem zmark_iff {m : ℕ} (cd : X ≃ Fin m) (Z : Finset Mp.stellar.Face) {mem : ℕ → ℕ}
    {ZFb z z44 : ℕ} (hZ : ∀ G, G ∈ Z ↔ (mem (ZFb + Mp.stFn cd G) ≠ z ↔ z44 = 1)) (x : X) :
    lbZ (mem (ZFb + cd x)) z (1 - ((z44 - 1) + (1 - z44))) = 1 ↔ Mp.stellar.face (old x) ∈ Z := by
  rw [hZ, stFn_old, lbZ_eq (by omega)]
  by_cases h44 : z44 = 1
  · have : 1 - ((z44 - 1) + (1 - z44)) = 1 := by omega
    simp only [this, h44]
    split_ifs with h <;> simp_all
  · have : 1 - ((z44 - 1) + (1 - z44)) = 0 := by omega
    simp only [this, h44]
    split_ifs with h <;> simp_all

end Marks

section Core

open Function Equiv Orbit CombMap PlanarSeparator PlanarSeparator.Map PlanarSeparator.StDart

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {σ : Perm D} {N : Finset D} (hσ : Stable σ N) (hB : Stable (revPerm M) N)

/-- **The two sides of a cycle separator at a dart.** -/
theorem core_iff {C : (psep M hσ hB).stellar.SCycle} {Z : Finset (psep M hσ hB).stellar.Face}
    (hsep : IsCycleSep C Z (sideIn C Z) (sideOut C Z)) (x : SDart N) :
    (Quotient.mk _ x ∈ coreI hσ hB C Z ↔
      ((.inl ((psep M hσ hB).vert x) : SVert σ N ⊕ (psep M hσ hB).Face) ∉ C.verts ∧
        (psep M hσ hB).stellar.face (old x) ∈ Z)) ∧
    (Quotient.mk _ x ∈ coreO hσ hB C Z ↔
      ((.inl ((psep M hσ hB).vert x) : SVert σ N ⊕ (psep M hσ hB).Face) ∉ C.verts ∧
        (psep M hσ hB).stellar.face (old x) ∉ Z)) := by
  have hI : Quotient.mk _ x ∈ coreI hσ hB C Z ↔
      (Sum.inl ((psep M hσ hB).vert x) : SVert σ N ⊕ (psep M hσ hB).Face) ∈ sideIn C Z := by
    simp [coreI, psep_vert]
  have hO : Quotient.mk _ x ∈ coreO hσ hB C Z ↔
      (Sum.inl ((psep M hσ hB).vert x) : SVert σ N ⊕ (psep M hσ hB).Face) ∈ sideOut C Z := by
    simp [coreO, psep_vert]
  have hin : (Sum.inl ((psep M hσ hB).vert x) : SVert σ N ⊕ (psep M hσ hB).Face) ∈ sideIn C Z ↔
      ((.inl ((psep M hσ hB).vert x) : SVert σ N ⊕ (psep M hσ hB).Face) ∉ C.verts ∧
        (psep M hσ hB).stellar.face (old x) ∈ Z) := by
    constructor
    · intro h
      exact ⟨(mem_sideIn.1 h).1, hsep.inA (old x) (by simpa using h)⟩
    · rintro ⟨h1, h2⟩
      exact mem_sideIn.2 ⟨h1, old x, by simp, h2⟩
  refine ⟨hI.trans hin, hO.trans ?_⟩
  rw [mem_sideOut, hin]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 ⟨h1, h⟩⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 h.2⟩

/-- **The label of the item of a dart** (`lbV` of the marks of its two ends and the face marks
of the triangles of the dart and of its reverse). -/
theorem lab_eq {C : (psep M hσ hB).stellar.SCycle} {Z : Finset (psep M hσ hB).stellar.Face}
    (hsep : IsCycleSep C Z (sideIn C Z) (sideOut C Z)) (x : SDart N)
    {kmi vi kmj vj z one : ℕ}
    (h1 : kmi = 0 ↔ (.inl ((psep M hσ hB).vert x) : SVert σ N ⊕ (psep M hσ hB).Face) ∉ C.verts)
    (h2 : kmj = 0 ↔ (.inl ((psep M hσ hB).vert ((psep M hσ hB).α x)) :
      SVert σ N ⊕ (psep M hσ hB).Face) ∉ C.verts)
    (h3 : lbZ vi z one = 1 ↔ (psep M hσ hB).stellar.face (old x) ∈ Z)
    (h4 : lbZ vj z one = 1 ↔ (psep M hσ hB).stellar.face (old ((psep M hσ hB).α x)) ∈ Z) :
    lbV kmi vi kmj vj z one =
      if x.1 ∈ sideItem hσ hB (coreI hσ hB C Z) then 1
      else if x.1 ∈ sideItem hσ hB (coreO hσ hB C Z) then 2 else 0 := by
  have hm : ∀ S : Finset (SVert σ N), x.1 ∈ sideItem hσ hB S ↔
      Quotient.mk _ x ∈ S ∨ Quotient.mk _ ((psep M hσ hB).α x) ∈ S := fun S => by
    rw [mem_sideItem]
    constructor
    · rintro ⟨h, hx⟩; exact hx
    · intro hx; exact ⟨x.2, hx⟩
  have e1 := core_iff hσ hB hsep x
  have e2 := core_iff hσ hB hsep ((psep M hσ hB).α x)
  have c1 : ((kmi = 0 ∧ lbZ vi z one = 1) ∨ (kmj = 0 ∧ lbZ vj z one = 1)) ↔
      x.1 ∈ sideItem hσ hB (coreI hσ hB C Z) := by
    rw [hm, e1.1, e2.1, h1, h2, h3, h4]
  have c2 : ((kmi = 0 ∧ lbZ vi z one ≠ 1) ∨ (kmj = 0 ∧ lbZ vj z one ≠ 1)) ↔
      x.1 ∈ sideItem hσ hB (coreO hσ hB C Z) := by
    simp only [ne_eq]
    rw [hm, e1.2, e2.2, h1, h2, h3, h4]
  rw [lbV_eq]
  exact if_congr c1 rfl (if_congr c2 rfl rfl)

end Core

/-! ### The separator on a piece map -/

section SepFacts

open Function Equiv Orbit CombMap PlanarSeparator PlanarSeparator.Map PlanarSeparator.StDart

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- The vertices of the piece map are the classes of the tails. -/
lemma psep_hsc {N : Finset D} {Hs : List (Finset V)} {τ : Perm D} (hN : PMap M N Hs τ)
    (x y : SDart N) :
    (psep M hN.stable hN.rev).vert x = (psep M hN.stable hN.rev).vert y ↔
      HRel Hs (M.tail x.1) (M.tail y.1) :=
  (psep_vert_eq _ _).trans (hN.vert _ x.2 _ y.2)

open Classical in
/-- **The separator `sepC` on a piece map without cut-vertex holes**: a cycle separator whose
path `corePath` is simple. -/
theorem sepC_facts (hloopM : ∀ d, M.head d ≠ M.tail d) {Hs : List (Finset V)}
    (hd : Hs.Pairwise Disjoint) (e : ℕ → D) (n Bz : ℕ) {N : Finset D} {τ : Perm D}
    (hN : PMap M N Hs τ) (hne : N.Nonempty) (hnc : NoCut M N Hs) (ex : D → ℕ)
    {C : (psep M hN.stable hN.rev).stellar.SCycle} {Z : Finset (psep M hN.stable hN.rev).stellar.Face}
    (h : sepC M e n Bz N τ hN.stable hN.rev ex = some (C, Z)) :
    IsCycleSep C Z (sideIn C Z) (sideOut C Z) ∧ (corePath hN.stable hN.rev C).Simple Hs := by
  obtain ⟨C', Z', h', hk, hsep, hin, hout⟩ := sepC_ok hloopM e n Bz Hs N τ hN ex hne hnc
  rw [h] at h'
  simp only [Option.some.injEq, Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  obtain ⟨x₀, hx₀⟩ := hne
  have hsmall := hN.small_of_noCut hd hloopM hx₀ hnc
  have hloop : ∀ x ∈ N, ¬ HRel Hs (M.head x) (M.tail x) := by
    rintro x hx (e | ⟨H, hH, h1, h2⟩)
    · exact hloopM x e
    · exact hN.inner x hx ⟨H, hH, h2, h1⟩
  exact ⟨hsep, (exists_core_cycle' hN.stable hN.rev hN.vert hloop hsmall (fun _ => 1)
    (fun _ => le_rfl) (coreExW τ N ex) C Z hk hsep hin hout).1⟩

/-- **A marked key is a vertex of the new hole**: with keys `K` of the darts of the piece
(`K y = x ↔ HRel (tail y) v`), `x` is the key of a dart whose vertex is on the cycle iff `v` is in
the new hole of the path `corePath C`. -/
theorem nh_iff (hloopM : ∀ d, M.head d ≠ M.tail d) {Hs : List (Finset V)}
    (hd : Hs.Pairwise Disjoint) {N : Finset D} {τ : Perm D} (hN : PMap M N Hs τ)
    (hne : N.Nonempty) (hnc : NoCut M N Hs) (C : (psep M hN.stable hN.rev).stellar.SCycle)
    (hsim : (corePath hN.stable hN.rev C).Simple Hs) (K : SDart N → ℕ) {x : ℕ} {v : V}
    (hK : ∀ y, K y = x ↔ HRel Hs (M.tail y.1) v) :
    (∃ l < C.k, ∃ y, (psep M hN.stable hN.rev).stellar.vert (C.d l) =
        .inl ((psep M hN.stable hN.rev).vert y) ∧ K y = x) ↔
      v ∈ newHole Hs (corePath hN.stable hN.rev C).mverts := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hsmall := hN.small_of_noCut hd hloopM hx₀ hnc
  have hsc := psep_hsc hN
  have hl : ∀ d, (psep M hN.stable hN.rev).vert ((psep M hN.stable hN.rev).α d) ≠ (psep M hN.stable hN.rev).vert d := (psep_run_conds hloopM hN ⟨x₀, hx₀⟩).1
  have hsm : ∀ x y, (psep M hN.stable hN.rev).face x = (psep M hN.stable hN.rev).face y → y = x ∨ y = (psep M hN.stable hN.rev).φ x ∨ y = (psep M hN.stable hN.rev).φ.symm x := by
    intro x y h
    have hy : y.1 ∈ pface M τ N x.1 := mem_pface.2 ⟨y.2, (psep_face_eq hN.stable hN.rev).1 h⟩
    rcases hsmall x.1 x.2 y.1 hy with e | e | e
    · exact Or.inl (Subtype.ext e)
    · exact Or.inr (Or.inl (Subtype.ext (by rw [e, psep_φ]; rfl)))
    · exact Or.inr (Or.inr (Subtype.ext (by rw [e, psep_φ_symm])))
  obtain ⟨hn0, -, -, -, hcov⟩ := Map.stellar_cycle_path' hl hsm C
  rw [mem_newHole_iff hd hsim]
  have hkk : (corePath hN.stable hN.rev C).k = Map.stN C - 1 := rfl
  have hpp : ∀ j, (corePath hN.stable hN.rev C).p j = M.tail (Map.stE C j).1 := fun j => rfl
  constructor
  · rintro ⟨l, hl', y, hv, hy⟩
    obtain ⟨j, hj, hj'⟩ := (hcov ((psep M hN.stable hN.rev).vert y)).1 ⟨l, hl', hv⟩
    refine ⟨j, by rw [hkk]; omega, ?_⟩
    rw [hpp]
    exact hRel_trans' hd (hRel_symm ((hK y).1 hy)) ((hsc y _).1 hj'.symm)
  · rintro ⟨j, hj, hr⟩
    rw [hkk] at hj
    rw [hpp] at hr
    obtain ⟨l, hl', hv⟩ := (hcov ((psep M hN.stable hN.rev).vert (Map.stE C j))).2 ⟨j, by omega, rfl⟩
    exact ⟨l, hl', Map.stE C j, hv, (hK _).2 (hRel_symm hr)⟩

end SepFacts

end BKMNW

end PlanarFlow
