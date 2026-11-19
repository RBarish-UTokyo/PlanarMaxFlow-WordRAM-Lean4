module

public import PlanarFlow.BKMNW.MbBase

/-!
# Miller's base program meets `MbSpec'`

**`mbBase_spec`**: for the separator `sepC M e n Bz` (the one the machine computes, `sepC_ok`),
`mbBase` meets `MbSpec'` within `mbT n Bz T₀` steps, the path described by the flags of its new
hole (`PathNH`), given: the rotation array of `τ` (stable on the enumerated darts `B`) at
`SGb` below `b` in the kept memory `m₀`, the base registers `5200 … 5203` (`SGb`, `Hb`, `Bz`,
`SVb`) in the kept registers `r₀`, `encB' n ≤ Bz`, and the layout
`SGb + n ≤ b`, `b + 7 n ≤ ITEMb`, `ITEMb + n ≤ NHb`, `NHb + n ≤ Hb`,
`Bz + 25 n + 3 T₀ + 15 ≤ Hb`, `Hb + 13 n ≤ SVb`, `SVb + Bz + 25 n + 3 T₀ + 16 ≤ W`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

section Spec

open Function Equiv Orbit CombMap PlanarSeparator PlanarSeparator.Map PlanarSeparator.StDart

variable {P : Input} {W : ℕ}
variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- The length of a simple cycle of the stellar subdivision of a piece map. -/
lemma sCycle_k_le {σ : Perm D} {N : Finset D} (hσ : Stable σ N) (hB : Stable (revPerm M) N)
    (C : (psep M hσ hB).stellar.SCycle) : C.k ≤ 2 * #N := by
  classical
  have h1 : #C.verts ≤ Fintype.card (SVert σ N ⊕ (psep M hσ hB).Face) := card_le_univ _
  rw [C.card_verts, Fintype.card_sum] at h1
  have h2 := card_sVert_le (σ := σ) (N := N)
  have h3 := card_face_le (psep M hσ hB)
  rw [Fintype.card_coe] at h3
  omega

open Classical in
set_option maxHeartbeats 3200000 in
/-- **Miller's base program meets the revised base specification** for the separator `sepC` it
computes. -/
theorem mbBase_spec (hloopM : ∀ d, M.head d ≠ M.tail d) {Hs : List (Finset V)}
    (hd : Hs.Pairwise Disjoint) (e : ℕ → D) (n Bz : ℕ) (τ : Perm D) (N₀ : Finset D)
    {b A W₀ ITEMb NHb T₀ SGb Hb SVb : ℕ} (B : Finset D) (m₀ r₀ : ℕ → ℕ)
    (hr0 : r₀ 5200 = SGb) (hr1 : r₀ 5201 = Hb) (hr2 : r₀ 5202 = Bz) (hr3 : r₀ 5203 = SVb)
    (hSG : ∀ i < n, m₀ (SGb + i) < n ∧ e (m₀ (SGb + i)) = τ (e i)) (hτB : Stable τ B)
    (hBz : encB' n ≤ Bz)
    (lay : SGb + n ≤ b ∧ b + 7 * n ≤ ITEMb ∧ ITEMb + n ≤ NHb ∧ NHb + n ≤ Hb ∧
      Bz + 25 * n + 3 * T₀ + 15 ≤ Hb ∧ Hb + 13 * n ≤ SVb ∧ SVb + Bz + 25 * n + 3 * T₀ + 16 ≤ W) :
    MbSpec' P W M (scChoiceE M (sepC M e n Bz) e n Hs A W₀) Hs τ N₀ mbBase (mbT n Bz T₀) n b A
      W₀ ITEMb NHb T₀ e B m₀ r₀ (PathNH M e n NHb Hs) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := lay
  intro s c hc hR hI hnc hN hne hret _ hT₀ hS r55 r56 hlow hregs
  obtain ⟨N, σ, ex⟩ := s
  dsimp only at hI hnc hN hne hret hT₀ ⊢
  have hNn : #N ≤ n := card_le_of_lvIn hI
  have hsN : ∀ d ∈ N, ∃ i, i < n ∧ e i = d := fun d hd => hI.surj d (hI.sub hd)
  set S := ∑ d ∈ N, ex d with hSdef
  have hS₀ : #N + S ≤ T₀ := by
    have : ∑ d ∈ N, (1 + ex d) = #N + S := by rw [sum_add_distrib]; simp [hSdef]
    omega
  have rg : ∀ x, 4975 < x → c.nreg x = r₀ x := fun x hx =>
    hregs x (by unfold SlFr LvFr; omega) (by omega)
  obtain ⟨d, t₁, eA, ht₁, ⟨C, Z⟩, hsepR, h641, h640, hZ, hsv, hRKd, hCRd, hmemd, d00, d04, d12,
      d40, d45, d46, dreg, -, -, -⟩ :=
    mbA_exec (P := P) (W := W) hloopM e (SGb := SGb) (Hb := Hb) (Bz := Bz) (SVb := SVb) hN hne
      hret c hc hI hR.p0 hR.p1 hR.p3 (by rw [rg _ (by omega), hr0]) (by rw [rg _ (by omega), hr1])
      (by rw [rg _ (by omega), hr2]) (by rw [rg _ (by omega), hr3]) hτB
      (fun i hi => by rw [hlow _ (by omega)]; exact hSG i hi) hBz
      ⟨by omega, by omega, by omega, by omega, by omega⟩ hS
  have hw₁ := eA.wb_right
  dsimp only at h641 h640
  set Wr := Bz + 25 * #N + 3 * S + 14 with hWr
  have hk : C.k ≤ 2 * #N := sCycle_k_le hN.stable hN.rev C
  obtain ⟨hl, hP, hm2⟩ := psep_run_conds hloopM hN hne
  have hm2' : 2 ≤ #N := hm2
  obtain ⟨d₂, t₂, eB, ht₂, hCY₂, hZF₂, hrest, hkeep₂, hreg₂, -, -, -⟩ :=
    mbB_exec (P := P) d hw₁ (k := C.k) (p0 := d.nreg 640) (p2 := d.nreg 642) (m := #N)
      (Wr := Wr) h641 rfl rfl d00 d04 d12 d40 d45 d46
      ⟨by omega, by omega, hNn, by omega, by omega, by omega⟩
  have hw₂ := eB.wb_right
  -- the memory of `d₂`
  have hlo : ∀ a < Hb, d₂.nmem a = c.nmem a := fun a ha => by
    by_cases h : a ≤ Wr
    · rw [hrest a h, hsv a h]
    · rw [hkeep₂ a (by omega) (by omega) (by omega), hmemd a (by omega) (by omega) (by omega)]
  have hRK₂ : ∀ j < n, d₂.nmem (Hb + j) = eRk e n N (e j) := fun j hj => by
    rw [hkeep₂ _ (by omega) (by omega) (by omega), hRKd j hj]
  have hCR₂ : ∀ i < n, e i ∈ N →
      d₂.nmem (Hb + 4 * n + eRk e n N (e i)) = eRk e n N (M.rev (e i)) := fun i hi hiN => by
    have := eRk_lt (e := e) (n := n) hiN
    rw [hkeep₂ _ (by omega) (by omega) (by omega), hCRd i hi hiN]
  have dr : ∀ x, mbU x = false → (x < 4910 ∨ (4916 < x ∧ x < 5000)) → d₂.nreg x = c.nreg x :=
    fun x h1 h2 => by rw [hreg₂ x (by omega), dreg x h1 (by omega)]
  have mbU_f : ∀ x, 4700 ≤ x → mbU x = false := fun x hx => by simp [mbU]; omega
  -- facts on the arrays
  have hnf₂ : ∀ i < n, (d₂.nmem (b + i) ≠ 0 ↔ e i ∈ N) := fun i hi => by
    rw [hlo _ (by omega)]; exact hI.nf i hi
  have hrv₂ : ∀ i < n, d₂.nmem (b + 2 * n + i) < n ∧ e (d₂.nmem (b + 2 * n + i)) = M.rev (e i) :=
    fun i hi => by rw [hlo _ (by omega)]; exact hI.rv0 i hi
  have htk₂ : ∀ i < n, d₂.nmem (b + 6 * n + i) < n := fun i hi => by
    rw [hlo _ (by omega)]; exact hI.tk i hi
  have hkey₂ : ∀ i < n, ∀ j < n, (d₂.nmem (b + 6 * n + i) = d₂.nmem (b + 6 * n + j) ↔
      HRel Hs (M.tail (e i)) (M.tail (e j))) := fun i hi j hj => by
    rw [hlo _ (by omega), hlo _ (by omega)]; exact hI.key i hi j hj
  have hrkN : ∀ i < n, e i ∈ N → eRk e n N (e i) < #N := fun i _ h => eRk_lt h
  -- stage C
  obtain ⟨c', t₃, eC, ht₃, ⟨m₂, hm₂t, hm₂a, hKMc⟩, hNHc, hITc, hkeepC, f70, f44, f43, f02, fregC,
      -, -, -⟩ :=
    mbC_exec (P := P) d₂ hw₂ (n := n) (b := b) (Hb := Hb) (k := C.k) (z := d.nreg 643)
      (z44 := d.nreg 644) (ITb := ITEMb) (NHb := NHb) (mN := #N)
      (by rw [hreg₂ _ (by omega), d00])
      (by rw [dr _ (mbU_f _ (by omega)) (by omega), hR.p1])
      (by rw [dr _ (mbU_f _ (by omega)) (by omega), hR.p3])
      (by rw [hreg₂ _ (by omega), d04]) (by rw [hreg₂ _ (by omega), h641])
      (by rw [hreg₂ _ (by omega)]) (by rw [hreg₂ _ (by omega)])
      (by rw [dr _ (mbU_f _ (by omega)) (by omega), r55])
      (by rw [dr _ (mbU_f _ (by omega)) (by omega), r56])
      ⟨by omega, by omega, by omega, by omega, by omega, hNn, by omega⟩ htk₂
      (fun i hi => (hrv₂ i hi).1)
      (fun i hi hF => by
        have hiN := (hnf₂ i hi).1 hF
        obtain ⟨hr, hre⟩ := hrv₂ i hi
        rw [hRK₂ i hi, hRK₂ _ hr, hre]
        exact ⟨eRk_lt hiN, eRk_lt (hN.rev _ hiN)⟩)
      (fun i hi j hj hFi hFj h => by
        rw [hRK₂ i hi, hRK₂ j hj] at h
        have hiN := (hnf₂ i hi).1 hFi
        have hjN := (hnf₂ j hj).1 hFj
        have hc : (cNe e n N ⟨e i, hiN⟩ : ℕ) = cNe e n N ⟨e j, hjN⟩ := by
          rw [cNe_apply hsN, cNe_apply hsN]; exact h
        have := (cNe e n N).injective (Fin.ext hc)
        exact hI.inj i hi j hj (congrArg Subtype.val this))
      (fun q hq => by
        obtain ⟨y, hy⟩ := (cNe e n N).surjective ⟨q, hq⟩
        obtain ⟨i, hi, hei⟩ := hsN y.1 y.2
        refine ⟨i, hi, (hnf₂ i hi).2 (hei ▸ y.2), ?_⟩
        rw [hRK₂ i hi, hei, ← cNe_apply hsN y, hy])
      (fun l hl => by
        rw [hCY₂ l hl, h640 l hl]; exact (stCode _ _ _).2)
      (fun q hq => by
        obtain ⟨y, hy⟩ := (cNe e n N).surjective ⟨q, hq⟩
        obtain ⟨i, hi, hei⟩ := hsN y.1 y.2
        have hiN : e i ∈ N := hei ▸ y.2
        have hq' : q = eRk e n N (e i) := by rw [hei, ← cNe_apply hsN y, hy]
        rw [hq', hCR₂ i hi hiN]
        exact eRk_lt (hN.rev _ hiN))
  -- the semantic part
  have hKv : ∀ y y' : SDart N, (psep M hN.stable hN.rev).vert y =
      (psep M hN.stable hN.rev).vert y' →
      d₂.nmem (b + 6 * n + eIdx e n y.1) = d₂.nmem (b + 6 * n + eIdx e n y'.1) := fun y y' h => by
    obtain ⟨j, hj, hej⟩ := hsN y.1 y.2
    obtain ⟨j', hj', hej'⟩ := hsN y'.1 y'.2
    rw [← hej, ← hej', eIdx_e hI.inj hj, eIdx_e hI.inj hj', hkey₂ j hj j' hj', hej, hej']
    exact (psep_hsc hN y y').1 h
  have hKM : ∀ x < n, (c'.nmem (Hb + 12 * n + x) ≠ 0 ↔ ∃ l < C.k, ∃ y : SDart N,
      (psep M hN.stable hN.rev).stellar.vert (C.d l) = .inl ((psep M hN.stable hN.rev).vert y) ∧
        d₂.nmem (b + 6 * n + eIdx e n y.1) = x) := fun x hx => by
    rw [hKMc x hx]
    refine kmHit_iff (cNe e n N) C (fun y => d₂.nmem (b + 6 * n + eIdx e n y.1)) hKv
      (fun l hl => ?_) (fun y => ?_) (fun y => ?_) x
    · rw [hm₂a _ (Or.inr ⟨by omega, by omega⟩), hCY₂ l hl, h640 l hl, stCode_val]
    · obtain ⟨i, hi, hei⟩ := hsN y.1 y.2
      have hiN : e i ∈ N := hei ▸ y.2
      have := hm₂t i hi ((hnf₂ i hi).2 hiN)
      rw [hRK₂ i hi, hei, ← cNe_apply hsN y] at this
      rw [this, ← hei, eIdx_e hI.inj hi]
    · obtain ⟨i, hi, hei⟩ := hsN y.1 y.2
      have hiN : e i ∈ N := hei ▸ y.2
      have hlt := eRk_lt (e := e) (n := n) hiN
      rw [cNe_apply hsN y, cNe_apply hsN, ← hei, hm₂a _ (Or.inl (by omega)), hCR₂ i hi hiN,
        psep_α, hei]
  obtain ⟨hIR, hNH, hlt3⟩ := mb_sem (lab := fun i => c'.nmem (ITEMb + i))
    (nh := fun i => c'.nmem (NHb + i)) (TK := fun i => d₂.nmem (b + 6 * n + i))
    (RV := fun i => d₂.nmem (b + 2 * n + i)) (NF := fun i => d₂.nmem (b + i))
    (RK := fun i => d₂.nmem (Hb + i)) (KM := fun x => c'.nmem (Hb + 12 * n + x))
    (ZFm := fun q => d₂.nmem (Hb + 11 * n + q)) (z := d.nreg 643) (z44 := d.nreg 644)
    (C := C) (Z := Z) (ex := ex) (Bz := Bz) (e := e) (n := n)
    hloopM hd hN hne hnc hsepR hI.inj hsN hkey₂
    (fun i hi => hrv₂ i hi) hnf₂ (fun i hi _ => hRK₂ i hi) htk₂ hKM
    (fun G => by
      have hG := ((psep M hN.stable hN.rev).stFn (cNe e n N) G).2
      rw [hZ G, hZF₂ _ hG])
    (fun i hi => hITc i hi) (fun i hi => hNHc i hi)
  -- the cost
  have hcQ : Fintype.card (SVert σ N) + Fintype.card (psep M hN.stable hN.rev).Face ≤ 2 * n := by
    have h2 := card_sVert_le (σ := σ) (N := N)
    have h3 := card_face_le (psep M hN.stable hN.rev)
    rw [Fintype.card_coe] at h3
    omega
  have hmsT := msT_mono hNn hcQ
  have hbase : scBase (scChoiceE M (sepC M e n Bz) e n Hs A W₀) Hs (N, σ, ex) =
      some (corePath hN.stable hN.rev C, {sideItem hN.stable hN.rev (coreI hN.stable hN.rev C Z),
        sideItem hN.stable hN.rev (coreO hN.stable hN.rev C Z)}) := by
    simp only [scBase, hnc, ↓reduceIte]
    rw [dite_eq_left_of_eq_true (eq_true ⟨hN.stable, hN.rev⟩)]
    show (sepC M e n Bz N σ hN.stable hN.rev ex).map _ = _
    rw [hsepR]; rfl
  refine ⟨c', t₁ + (t₂ + t₃), .seq eA (.seq eB eC), ?_, fun a ha => ?_, fun x hx => ?_,
    Or.inr ⟨f70, _, _, hbase, hIR, ?_, hNH, by omega, by omega, fun i hi => ?_, f43, f02,
      hNH⟩⟩
  · have hSS : (∑ d ∈ N, ex d) = S := hSdef.symm
    have he1 : encT #N = 217 * #N + 160 := rfl
    have he2 : encT n = 217 * n + 160 := rfl
    unfold mbT
    omega
  · rw [hkeepC a (by omega) (by omega) (by omega), hlo a (by omega)]
  · rw [fregC x (by unfold MbCFr; omega), dr x (mbU_f _ (by omega)) (by omega)]
  · intro X hX
    simp only [mem_insert, mem_singleton] at hX
    rcases hX with rfl | rfl <;> exact sideItem_subset _ _ _
  · rw [f44]; exact hlt3 i hi

end Spec

end BKMNW

end PlanarFlow
