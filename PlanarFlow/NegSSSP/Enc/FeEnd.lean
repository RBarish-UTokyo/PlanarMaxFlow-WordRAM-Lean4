module

public import PlanarFlow.NegSSSP.Enc.FeMid

/-!
# The composed encoder, phase D: the initial tree `T`, its orders, the cotree and its orders

`feEndProg p`: the parent array of `T` by **Bellman–Ford** on the isolating lengths
(`ptProg`, `O(#V' · #D')`), a word at the root of the array, the orders of `T` (`feTo`), the
cotree `C` of `T` with its orders (`feCot`, in the slot), and the lengths `HD₀`, `HD₁` written
again (the cotree's run reuses their words as scratch).

* **`feEnd_exec`**: from the words of `feMid_exec`: **a tree `T` meeting `Klein.Compat`** rooted
  at the first root, **a cotree `C` of `T`** rooted at the face of `g' 0`, their orders, and the
  words `IV`, `IT`, `IF`, `IC`, `HD` of `Klein.KInit` in the slot; the memory changes only in
  `[β + iIV, β + iHD + 4)`, `[PA, PA + A)` and `[DB, END)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

/-- More facts on the layout (the arrays of the orders in the slot). -/
lemma FeP.ord2 (p : FeP) :
    p.β + iIV p.N p.NN p.k + p.A ≤ p.β + iIT p.N p.NN p.k ∧
    p.β + iIT p.N p.NN p.k + p.A ≤ p.β + iIF p.N p.NN p.k ∧
    p.β + iIF p.N p.NN p.k + p.FN ≤ p.β + iIC p.N p.NN p.k ∧
    p.β + iIC p.N p.NN p.k + p.FN ≤ p.β + iHD p.N p.NN p.k ∧
    p.β + iHD p.N p.NN p.k + 4 ≤ p.SL ∧ p.β + 6 * p.N + p.N ≤ p.β + iOB p.N p.NN p.k ∧
    p.β + iOL p.N p.NN p.k + p.N ≤ p.β + iIV p.N p.NN p.k ∧ p.A + p.N + p.FN ≤ p.ZT ∧
    p.nV + 2 < p.A ∨ p.k < 2 := by
  simp only [FeP.N, FeP.A, FeP.FN, FeP.AE, FeP.NN, FeP.β, FeP.Bw, FeP.Kw, FeP.SL, FeP.ONE, FeP.ZV,
    FeP.PA, FeP.O1, FeP.ZC, FeP.WW, FeP.ZI, FeP.RD, FeP.MK, FeP.ISO, FeP.RK, FeP.DB, FeP.ZS,
    FeP.ZT, iOB, iOL, iXT, iHD, iIV, iIT, iIF, iIC, kBL, aOUT]
  by_cases h : p.k < 2
  · exact Or.inr h
  · left
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- **Phase D** (without the final clamp). -/
def feEndProg (p : FeP) : Stmt :=
  .seq (ptProg p.N (p.β + 6 * p.N) (p.β + 4 * p.N) (p.β + 5 * p.N) p.ISO p.DB p.MK p.PA p.A p.A
    p.Inf p.nV (p.PA + (p.nV + 2)) p.nD) <|
  .seq (feStore (p.PA + p.nV) 0) <| .seq (feTo p) <|
  .seq (feCot p.N p.FN (p.A - 1) (p.β + iIT p.N p.NN p.k) p.β (p.β + p.N) (p.A + p.N) p.ZT
    (p.β + iIF p.N p.NN p.k) (p.β + iIC p.N p.NN p.k) (p.β + iHD p.N p.NN p.k + 2) p.nD) <|
  .seq (feStore (p.β + iHD p.N p.NN p.k) p.A) (feStore (p.β + iHD p.N p.NN p.k + 1) (p.A - 1))

theorem feEndProg_natOnly (p : FeP) : natOnly (feEndProg p) = true := by
  simp only [feEndProg, natOnly, ptProg_natOnly, feStore_natOnly, feTo_natOnly, feCot_natOnly,
    Bool.and_self]

/-- The cost bound of phase D. -/
def feEndCost (p : FeP) : ℕ :=
  (p.A * (24 * p.N + 6) + 5 * p.A + 29 * p.N + 17 + 21) + 3 + (16 + toCost p.A) +
    (44 + cotCost p.N p.FN (p.A - 1)) + 6

set_option maxHeartbeats 8000000 in
open Classical in
/-- **Phase D on the machine** (see the module docstring). -/
theorem feEnd_exec {X : Finset D} {B : Finset V} (fd : FaceData N X B) (ℓ : D → ℤ)
    (σ₀ : fd.DQ ≃ Fin (Fintype.card fd.DQ)) (νv₀ : fd.VQ ≃ Fin (Fintype.card fd.VQ))
    (τ₀ : fd.FQ ≃ Fin (Fintype.card fd.FQ)) (p : FeP) (hD : p.nD = Fintype.card fd.DQ)
    (hk : p.k = fd.k) (hV : p.nV = Fintype.card fd.VQ) (hF : p.nF = Fintype.card fd.FQ)
    (hW : p.END ≤ W)
    (hLm : feIsoB p.A p.N p.FN (srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ)).toNat ≤ p.Lmax)
    (hIW : p.Inf + p.Lmax ≤ W)
    {w : SrcD fd.DQ fd.k → ℤ}
    (hw : MSSP.IsoW (srcMap fd.inst.cycle) ((srcMap fd.inst.cycle).face (srcG fd.inst.cycle 0)) w)
    (hwB : ∀ d, |w d| ≤ Fintype.card (SrcF fd.FQ fd.k))
    (C₀ : STFlow.DTree (srcMap fd.inst.cycle).dual)
    (hC₀r : C₀.root = tripSrc (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0)
    (c : Config) (hc : WordsBounded W c)
    (hA : SrcArrM fd.Q fd.k fd.g (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) σ₀ νv₀ τ₀ p.β p.SL p.N
      p.A p.AE c.nmem)
    (hPA : ∀ y, y ≠ C₀.root → c.nmem (p.PA + srcVNum νv₀ y) = srcNum σ₀ (C₀.par y))
    (hISO : ∀ d, c.nmem (p.ISO + srcNum σ₀ d) = ((srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w (srcNum σ₀)) d).toNat)
    (hMK : ∀ y, c.nmem (p.MK + srcVNum νv₀ y) =
      if MSSP.Reach (MSSP.pieceGraph (srcMap fd.inst.cycle) (srcPiece fd.k (fd.P'.image fd.e)) (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w (srcNum σ₀)))
        (tripSrc (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0) y then 1 else 0) :
    ∃ c' t, Exec P W (feEndProg p) c c' t ∧ t ≤ feEndCost p ∧
      ∃ (T : STFlow.DTree (srcMap fd.inst.cycle).dual) (C : STFlow.DTree (srcMap fd.inst.cycle)) (ys : List (SrcV fd.VQ fd.k))
        (cs : List (SrcF fd.FQ fd.k)),
        Compat T (tripSrc (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0)
          (tripDst (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0) (srcG fd.inst.cycle (0 % fd.k))
          (tpar (MSSP.pieceGraph (srcMap fd.inst.cycle) (srcPiece fd.k (fd.P'.image fd.e)) (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w (srcNum σ₀))) (tripSrc (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0)) ∧
        Orders T ((List.finRange (Fintype.card (SrcV fd.VQ fd.k))).map (srcVNum νv₀).symm) ys ∧
        Orders C ((List.finRange (Fintype.card (SrcF fd.FQ fd.k))).map (srcFNum τ₀).symm) cs ∧
        C.root = (srcMap fd.inst.cycle).face (srcG fd.inst.cycle 0) ∧
        (∀ x, x ≠ C.root → ¬ T.InT (C.par x)) ∧
        (∀ i (h : i < ((List.finRange (Fintype.card (SrcV fd.VQ fd.k))).map
            (srcVNum νv₀).symm).length),
          c'.nmem (p.β + iIV p.N p.NN p.k + i) = srcVNum νv₀
            ((List.finRange (Fintype.card (SrcV fd.VQ fd.k))).map (srcVNum νv₀).symm)[i]) ∧
        (∀ i (h : i < ys.length), c'.nmem (p.β + iIT p.N p.NN p.k + i) =
          srcNum σ₀ (T.par ys[i])) ∧
        (∀ i (h : i < ((List.finRange (Fintype.card (SrcF fd.FQ fd.k))).map
            (srcFNum τ₀).symm).length),
          c'.nmem (p.β + iIF p.N p.NN p.k + i) = (p.A + p.N) + srcFNum τ₀
            ((List.finRange (Fintype.card (SrcF fd.FQ fd.k))).map (srcFNum τ₀).symm)[i]) ∧
        (∀ i (h : i < cs.length), c'.nmem (p.β + iIC p.N p.NN p.k + i) =
          srcNum σ₀ (C.par cs[i])) ∧
        c'.nmem (p.β + iHD p.N p.NN p.k) = ((List.finRange (Fintype.card (SrcV fd.VQ fd.k))).map
            (srcVNum νv₀).symm).length ∧
        c'.nmem (p.β + iHD p.N p.NN p.k + 1) = ys.length ∧
        c'.nmem (p.β + iHD p.N p.NN p.k + 2) = ((List.finRange (Fintype.card (SrcF fd.FQ fd.k))).map
            (srcFNum τ₀).symm).length ∧
        c'.nmem (p.β + iHD p.N p.NN p.k + 3) = cs.length ∧
        (∀ a, (a < p.β + iIV p.N p.NN p.k ∨ p.β + iHD p.N p.NN p.k + 4 ≤ a) →
          (a < p.PA ∨ p.PA + p.A ≤ a) → (a < p.DB ∨ p.END ≤ a) → c'.nmem a = c.nmem a) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hnnQ : ∀ y, 0 ≤ faceLen fd.P' fd.e ℓ y := fun y => faceLen_nonneg _ _ _ y
  obtain ⟨cD, cV, cF⟩ := fe_cards (k := fd.k) (D := fd.DQ) (V := fd.VQ) (F := fd.FQ) p hD hk hV hF
  have ho := p.ord
  have h2k : 2 ≤ p.k := by rw [hk]; exact fd.inst.cycle.two_le
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ : _ := (p.ord2).resolve_right (by omega)
  obtain ⟨H, -⟩ := srcIso_hyp fd.inst.cycle fd.inst.plane fd.inst.rot (fun d _ => hnnQ d) hw hwB
    (srcNum σ₀)
  obtain ⟨ru, rv, re, -⟩ := fe_roots (σ₀ := σ₀) (νv₀ := νv₀) fd.inst.cycle
  have hσN : ∀ d : SrcD fd.DQ fd.k, (srcNum σ₀ d : ℕ) < p.N := fun d => by
    have := (srcNum σ₀ d).2; clear * - this cD; omega
  have hτA : ∀ y : SrcV fd.VQ fd.k, (srcVNum νv₀ y : ℕ) < p.A := fun y => by
    have := (srcVNum νv₀ y).2; clear * - this cV; omega
  have hinj : Function.Injective fun y : SrcV fd.VQ fd.k => (srcVNum νv₀ y : ℕ) :=
    fun a b h => (srcVNum νv₀).injective (Fin.ext h)
  have arr := fun d => hA.arrays fd.inst.cycle d
  have hIso : ∀ d, ((srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w (srcNum σ₀)) d).toNat ≤ p.Lmax := fun d => by
    have := srcIso_le (V := fd.VQ) (F := fd.FQ) (S := fd.P'.image fd.e) hnnQ
      (faceLen_le_srcW fd ℓ) hwB (srcNum σ₀) d
    rw [cD, cV, cF] at this; omega
  have hInf : p.Inf = p.A * p.Lmax + 1 := rfl
  -- 1. the parent array of `T`
  have hLay : BFLay (Fintype.card (SrcD fd.DQ fd.k)) p.A (p.β + 6 * p.N) (p.β + 4 * p.N)
      (p.β + 5 * p.N) p.ISO p.DB p.Inf p.Lmax W := by
    rw [cD]
    exact ⟨by clear * - ho hW; omega, by clear * - ho hW; omega, by clear * - ho hW; omega,
      by clear * - ho hW; omega, by clear * - ho hW; omega, by clear * - ho hW; omega, hIW,
      by clear * - ho; omega, by clear * - ho; omega, by clear * - ho; omega,
      by clear * - ho; omega⟩
  have hTP : TPLay (Fintype.card (SrcD fd.DQ fd.k)) p.A (p.β + 6 * p.N) (p.β + 4 * p.N)
      (p.β + 5 * p.N) p.ISO p.MK p.DB p.PA W := by
    rw [cD]
    exact ⟨by clear * - ho hW; omega, by clear * - ho hW; omega, by clear * - ho hW; omega,
      by clear * - ho hW; omega, by clear * - ho hW; omega, by clear * - ho hW; omega,
      by clear * - ho hW; omega, by clear * - ho hW; omega, by clear * - ho; omega,
      by clear * - ho; omega, by clear * - ho; omega, by clear * - ho; omega,
      by clear * - ho; omega, by clear * - ho; omega⟩
  obtain ⟨c₁, k₁, e₁, hk₁, hP₁, hm₁, hr₁, hrm₁, ho₁⟩ :=
    ptProg_parT (P := P) (u := tripSrc (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0)
      (v := tripDst (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0) (e := srcG fd.inst.cycle (0 % fd.k)) C₀ hinj
      hτA (srcNum σ₀) H.pos (fun d _ => hIso d) H.uniq hLay hTP
      (Or.inl (by clear * - ho; omega)) (by rw [cV]) (by rw [hInf]; omega)
      (by clear * - ho hW; omega) c hc
      (fun d => by rw [(arr d).2.2.2.2.1]; split_ifs with h <;> simp [h])
      (fun d => (arr d).2.2.1) (fun d => (arr d).2.2.2.1)
      (fun d _ => hISO d)
      (fun x => by rw [hMK x]; split_ifs with h <;> simp [h])
      (fun y hy => hPA y (by rw [hC₀r]; exact hy))
  rw [ru, rv, re, cD, ← hV, ← hD] at e₁
  obtain ⟨T, hT, hTr, hPT⟩ := ptProg_tree H C₀ hC₀r (srcNum σ₀) (ιv := fun y => (srcVNum νv₀ y : ℕ))
    (mem := c₁.nmem) (Pb := p.PA) hP₁
  -- 2. the root word
  obtain ⟨c₂, k₂, e₂, hk₂, hm₂, -, hr₂, hrm₂, ho₂⟩ :=
    feStore_exec (P := P) (a := p.PA + p.nV) (v := 0) (by clear * - ho hW q9; omega)
      (by omega) c₁ e₁.wb_right
  have hPT₂ : ∀ y, y ≠ T.root → c₂.nmem (p.PA + srcVNum νv₀ y) = srcNum σ₀ (T.par y) :=
    fun y hy => by
      have hne : (srcVNum νv₀ y : ℕ) ≠ p.nV := fun h => hy (by
        rw [hTr]; apply (srcVNum νv₀).injective; ext; rw [h, ru, hV])
      rw [hm₂, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      exact hPT y hy
  have hNT₂ : ∀ d, c₂.nmem (p.β + 4 * p.N + srcNum σ₀ d) = srcVNum νv₀ ((srcMap fd.inst.cycle).tail d) :=
    fun d => by
      have := hσN d
      rw [hm₂, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by clear * - this ho; omega)),
        hm₁ _ (by clear * - this ho; omega) (by clear * - this ho; omega)]
      exact (arr d).2.2.1
  -- 3. the orders of `T`
  obtain ⟨c₃, k₃, e₃, hk₃, ys, hOT, hIV₃, hIT₃, hH0₃, hH1₃, hm₃, hr₃, hrm₃, ho₃⟩ :=
    feTo_exec (P := P) fd.inst.cycle p hD hk hV hF hW T hTr c₂ e₂.wb_right hPT₂
      (by rw [hm₂, upd_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl)]; omega) hNT₂
  -- 4. the cotree of `T` and its orders
  have hys : ys.length = p.A - 1 := by rw [orders_ylen_eq hOT, cV]
  have hRV₃ : ∀ d, c₃.nmem (p.β + srcNum σ₀ d) = srcNum σ₀ ((srcMap fd.inst.cycle).rev d) := fun d => by
    have := hσN d
    rw [hm₃ _ (by clear * - this ho; omega) (by clear * - this ho q1 q2 q3 q4 q7; omega), hm₂,
      upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by clear * - this ho; omega)),
      hm₁ _ (by clear * - this ho; omega) (by clear * - this ho; omega)]
    exact (arr d).1
  have hNF₃ : ∀ d, c₃.nmem (p.β + p.N + srcNum σ₀ d) =
      (p.A + p.N) + srcFNum τ₀ ((srcMap fd.inst.cycle).face d) := fun d => by
    have := hσN d
    rw [hm₃ _ (by clear * - this ho; omega) (by clear * - this ho q1 q2 q3 q4 q7; omega), hm₂,
      upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by clear * - this ho; omega)),
      hm₁ _ (by clear * - this ho; omega) (by clear * - this ho; omega)]
    exact (arr d).2.1
  obtain ⟨c₄, k₄, e₄, hk₄, C, cs, hCr, hoff, hOC, hIF₄, hIC₄, hH2₄, hH3₄, hm₄, hr₄, hrm₄, ho₄⟩ :=
    feCot_exec (P := P) (σ₀ := σ₀) (τ₀ := τ₀) (A' := p.A) (N := p.N) (FN := p.FN) (A := p.A - 1)
      (ITb := p.β + iIT p.N p.NN p.k) (RVb := p.β) (NFb := p.β + p.N) (Z := p.ZT)
      (IVb := p.β + iIF p.N p.NN p.k) (ITc := p.β + iIC p.N p.NN p.k)
      (HDc := p.β + iHD p.N p.NN p.k + 2) fd.inst.cycle fd.inst.plane T (ts := ys) hOT.ymem cD cF
      hys c₃ e₃.wb_right hIT₃ hRV₃ hNF₃ (by clear * - ho q1 q2 q3 q4 q5; omega)
      (by clear * - ho q5; omega) (by clear * - ho q5; omega) (by clear * - ho q5; omega)
      (by clear * - q3; omega) (by clear * - q4; omega) (by clear * - ho hW; omega)
      (by clear * - ho hW q8; omega)
  rw [← hD] at e₄
  -- 5. the lengths of the orders of `T` again
  obtain ⟨c₅, k₅, e₅, hk₅, hm₅, -, hr₅, hrm₅, ho₅⟩ :=
    feStore_exec (P := P) (a := p.β + iHD p.N p.NN p.k) (v := p.A)
      (by clear * - ho hW q5; omega) (by clear * - ho hW; omega) c₄ e₄.wb_right
  obtain ⟨c₆, k₆, e₆, hk₆, hm₆, -, hr₆, hrm₆, ho₆⟩ :=
    feStore_exec (P := P) (a := p.β + iHD p.N p.NN p.k + 1) (v := p.A - 1)
      (by clear * - ho hW q5; omega) (by clear * - ho hW; omega) c₅ e₅.wb_right
  have k56 : ∀ a, a ≠ p.β + iHD p.N p.NN p.k → a ≠ p.β + iHD p.N p.NN p.k + 1 →
      c₆.nmem a = c₄.nmem a := fun a h1 h2 => by
    rw [hm₆, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false h2), hm₅, upd_apply,
      ite_eq_right_of_eq_false _ _ (eq_false h1)]
  refine ⟨c₆, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + k₆)))),
    Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ e₆)))), ?_, T, C, ys, cs,
    hT, hOT, hOC, hCr, hoff, fun i h => ?_, fun i h => ?_, fun i h => ?_, fun i h => ?_, ?_, ?_,
    ?_, ?_, fun a h1 h2 h3 => ?_, by rw [hr₆, hr₅, hr₄, hr₃, hr₂, hr₁],
    by rw [hrm₆, hrm₅, hrm₄, hrm₃, hrm₂, hrm₁], by rw [ho₆, ho₅, ho₄, ho₃, ho₂, ho₁]⟩
  · unfold feEndCost; rw [cD] at hk₁
    clear * - hk₁ hk₂ hk₃ hk₄ hk₅ hk₆; omega
  · have hl : i < p.A := by
      have h' := h; simp only [List.length_map, List.length_finRange] at h'; omega
    rw [k56 _ (by clear * - hl q1 q2 q3 q4; omega) (by clear * - hl q1 q2 q3 q4; omega),
      hm₄ _ (by clear * - hl q1 q2 q3 q4 q5 ho; omega) (by clear * - hl q1 q2 q3 q4; omega)]
    exact hIV₃ i h
  · have hl : i < p.A := by rw [hys] at h; omega
    rw [k56 _ (by clear * - hl q1 q2 q3 q4; omega) (by clear * - hl q1 q2 q3 q4; omega),
      hm₄ _ (by clear * - hl q1 q2 q3 q4 q5 ho; omega) (by clear * - hl q1 q2 q3 q4; omega)]
    exact hIT₃ i h
  · have hl : i < p.FN := by
      have h' := h; simp only [List.length_map, List.length_finRange] at h'; omega
    rw [k56 _ (by clear * - hl q1 q2 q3 q4; omega) (by clear * - hl q1 q2 q3 q4; omega)]
    exact hIF₄ i h
  · have hl : i < p.FN := by have := orders_ylen_eq hOC; omega
    rw [k56 _ (by clear * - hl q1 q2 q3 q4; omega) (by clear * - hl q1 q2 q3 q4; omega)]
    exact hIC₄ i h
  · rw [hm₆, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hm₅, upd_apply,
      ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    simp [cV]
  · rw [hm₆, upd_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl), hys]
  · rw [k56 _ (by omega) (by omega), hH2₄]; simp
  · rw [k56 _ (by omega) (by omega), show p.β + iHD p.N p.NN p.k + 3 =
      p.β + iHD p.N p.NN p.k + 2 + 1 by omega, hH3₄]
  · rw [k56 _ (by clear * - h1 q1 q2 q3 q4; omega) (by clear * - h1 q1 q2 q3 q4; omega),
      hm₄ _ (by clear * - h3 ho; omega) (by clear * - h1 q1 q2 q3 q4; omega),
      hm₃ _ (by clear * - h3 ho; omega) (by clear * - h1 q1 q2 q3 q4; omega), hm₂, upd_apply,
      ite_eq_right_of_eq_false _ _ (eq_false (by clear * - h2 q9; omega)),
      hm₁ _ (by clear * - h3 ho; omega) (by clear * - h2; omega)]

end NegSSSP

end PlanarFlow
