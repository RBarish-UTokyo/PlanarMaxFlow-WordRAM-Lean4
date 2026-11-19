module

public import PlanarFlow.NegSSSP.Enc.FeMid
public import PlanarFlow.NegSSSP.Enc.DkPar

/-!
# The composed encoder, phase D, with the distances by Dijkstra

A copy of `FeEnd.lean` (`feEnd_exec`) in which the parent array of the initial tree `T` is
computed with **Dijkstra in memory** (`dkpProg`, `O((A + N) log A)`) instead of Bellman–Ford
(`ptProg`, `O(A · N)`): the out-lists of the piece in the slot (`FeOut`, written in phase C)
are an extra hypothesis; the Dijkstra scratch (`3 A` words) is `[ZS, ZS + 3 A)` (the scratch of
the orders, used afterwards).

* `FeP.ordDk`; `feEndProgDk`, `feEndCostDk`; **`feEndDk_exec`**: the conclusion of `feEnd_exec`
  (same frame) within `feEndCostDk p` steps.
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

/-- The order of the regions read and written by Dijkstra. -/
lemma FeP.ordDk (p : FeP) :
    p.β + iOB p.N p.NN p.k + p.A ≤ p.β + iOE p.N p.NN p.k ∧
    p.β + iOE p.N p.NN p.k + p.A ≤ p.β + iOL p.N p.NN p.k ∧
    p.β + iOL p.N p.NN p.k + p.N ≤ p.ISO ∧ p.β + 7 * p.N ≤ p.β + iOB p.N p.NN p.k ∧
    p.ISO + p.N ≤ p.DB ∧ p.DB + p.A ≤ p.ZS ∧ p.ZS + 3 * p.A ≤ p.ZT ∧ p.ZT ≤ p.END ∧
    p.MK + p.A ≤ p.DB ∧ p.PA + p.A ≤ p.DB := by
  simp only [FeP.N, FeP.A, FeP.FN, FeP.AE, FeP.NN, FeP.β, FeP.Bw, FeP.Kw, FeP.SL, FeP.ONE, FeP.ZV,
    FeP.PA, FeP.O1, FeP.ZC, FeP.WW, FeP.ZI, FeP.RD, FeP.MK, FeP.ISO, FeP.RK, FeP.DB, FeP.ZS,
    FeP.ZT, FeP.OS, FeP.END, iOB, iOE, iOL, kBL, aOUT]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- **Phase D** (without the final clamp), the distances by Dijkstra. -/
def feEndProgDk (p : FeP) : Stmt :=
  .seq (dkpProg p.N (p.β + 6 * p.N) (p.β + 4 * p.N) (p.β + 5 * p.N) p.ISO p.DB p.ZS
    (p.β + iOB p.N p.NN p.k) (p.β + iOE p.N p.NN p.k) (p.β + iOL p.N p.NN p.k) p.MK p.PA p.A
    p.Inf p.nV (p.PA + (p.nV + 2)) p.nD) <|
  .seq (feStore (p.PA + p.nV) 0) <| .seq (feTo p) <|
  .seq (feCot p.N p.FN (p.A - 1) (p.β + iIT p.N p.NN p.k) p.β (p.β + p.N) (p.A + p.N) p.ZT
    (p.β + iIF p.N p.NN p.k) (p.β + iIC p.N p.NN p.k) (p.β + iHD p.N p.NN p.k + 2) p.nD) <|
  .seq (feStore (p.β + iHD p.N p.NN p.k) p.A) (feStore (p.β + iHD p.N p.NN p.k + 1) (p.A - 1))

theorem feEndProgDk_natOnly (p : FeP) : natOnly (feEndProgDk p) = true := by
  simp only [feEndProgDk, natOnly, dkpProg_natOnly, feStore_natOnly, feTo_natOnly, feCot_natOnly,
    Bool.and_self]

/-- The cost bound of phase D with Dijkstra. -/
def feEndCostDk (p : FeP) : ℕ :=
  dkpCost p.N p.A p.N + 3 + (16 + toCost p.A) +
    (44 + cotCost p.N p.FN (p.A - 1)) + 6

set_option maxHeartbeats 8000000 in
open Classical in
/-- **Phase D on the machine, the distances by Dijkstra** (see the module docstring). -/
theorem feEndDk_exec {X : Finset D} {B : Finset V} (fd : FaceData N X B) (ℓ : D → ℤ)
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
        (tripSrc (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0) y then 1 else 0)
    (hO : FeOut (fd.P'.image fd.e) σ₀ νv₀ fd.inst.cycle p c.nmem) :
    ∃ c' t, Exec P W (feEndProgDk p) c c' t ∧ t ≤ feEndCostDk p ∧
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
  -- 1. the parent array of `T`, by Dijkstra
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := p.ordDk
  obtain ⟨hO1, mm, hmm, hOBE, hOL, hdeg⟩ := hO
  obtain ⟨hOut1, hOut2⟩ := outMem_snd fd.inst.cycle hO1
  have hDk : DkLay p.A (Fintype.card (SrcD fd.DQ fd.k)) mm p.DB p.ZS (p.β + iOB p.N p.NN p.k)
      (p.β + iOE p.N p.NN p.k) (p.β + iOL p.N p.NN p.k) (p.β + 5 * p.N) p.ISO p.Inf p.Lmax W := by
    rw [cD]
    have hA1 : 1 ≤ p.A := by have := hτA (tripSrc (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0); omega
    refine ⟨hA1, by clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 hW hmm; omega, by clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 hW hmm; omega,
      by clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 hW hmm; omega, hIW, by clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 hW hmm; omega,
      by clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 hW hmm; omega, by clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 hW hmm; omega,
      by clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 hW hmm; omega, by clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 hW hmm; omega,
      ⟨by clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 hW hmm; omega, by clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 hW hmm; omega⟩,
      ⟨by clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 hW hmm; omega, by clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 hW hmm; omega⟩,
      ⟨by clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 hW hmm; omega, by clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 hW hmm; omega⟩,
      ⟨by clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 hW hmm; omega, by clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 hW hmm; omega⟩,
      ⟨by clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 hW hmm; omega, by clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 hW hmm; omega⟩⟩
  have hTP : TPLay (Fintype.card (SrcD fd.DQ fd.k)) p.A (p.β + 6 * p.N) (p.β + 4 * p.N)
      (p.β + 5 * p.N) p.ISO p.MK p.DB p.PA W := by
    rw [cD]
    exact ⟨by clear * - ho hW; omega, by clear * - ho hW; omega, by clear * - ho hW; omega,
      by clear * - ho hW; omega, by clear * - ho hW; omega, by clear * - ho hW; omega,
      by clear * - ho hW; omega, by clear * - ho hW; omega, by clear * - ho; omega,
      by clear * - ho; omega, by clear * - ho; omega, by clear * - ho; omega,
      by clear * - ho; omega, by clear * - ho; omega⟩
  have hsurj : ∀ y < p.A, ∃ x : SrcV fd.VQ fd.k, (srcVNum νv₀ x : ℕ) = y := fun y hy =>
    ⟨(srcVNum νv₀).symm ⟨y, by rw [cV]; exact hy⟩, by simp⟩
  obtain ⟨c₁, k₁, e₁, hk₁, hP₁, hm₁, hr₁, hrm₁, ho₁⟩ :=
    dkpProg_parT (P := P) (u := tripSrc (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0)
      (v := tripDst (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0)
      (e := srcG fd.inst.cycle (0 % fd.k)) C₀ hinj hτA hsurj (srcNum σ₀) H.pos
      (fun d _ => hIso d) H.uniq hDk hTP
      ⟨Or.inl (by rw [cD]; clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10; omega), Or.inl (by rw [cD]; clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10; omega),
        Or.inl (by clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10; omega), Or.inl (by rw [cD]; clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10; omega),
        Or.inl (by rw [cD]; clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10; omega), Or.inl (by clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10; omega),
        Or.inl (by clear * - d1 d2 d3 d4 d5 d6 d7 d8 d9 d10; omega)⟩
      (by rw [cV, hInf]; omega) c hc
      (fun d => by rw [(arr d).2.2.2.2.1]; split_ifs with h <;> simp [h])
      (fun d => (arr d).2.2.1) (fun d => (arr d).2.2.2.1)
      (fun d _ => hISO d)
      (fun x => by rw [hMK x]; split_ifs with h <;> simp [h])
      (fun y hy => hPA y (by rw [hC₀r]; exact hy))
      hOut1 hOut2 (fun y hy => hOBE y hy) hdeg
  rw [ru, rv, re, cD, ← hV, ← hD] at e₁
  have hk₁' : k₁ ≤ dkpCost p.N p.A p.N := by
    rw [cD] at hk₁; refine hk₁.trans ?_; unfold dkpCost
    have := Nat.mul_le_mul_left (13 * Heap.lg (2 * p.A) + 20) hmm; omega
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
        hm₁ _ (by clear * - this ho; omega) (by clear * - this ho d6; omega)
        (by clear * - this ho; omega)]
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
      hm₁ _ (by clear * - this ho; omega) (by clear * - this ho d6; omega)
        (by clear * - this ho; omega)]
    exact (arr d).1
  have hNF₃ : ∀ d, c₃.nmem (p.β + p.N + srcNum σ₀ d) =
      (p.A + p.N) + srcFNum τ₀ ((srcMap fd.inst.cycle).face d) := fun d => by
    have := hσN d
    rw [hm₃ _ (by clear * - this ho; omega) (by clear * - this ho q1 q2 q3 q4 q7; omega), hm₂,
      upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by clear * - this ho; omega)),
      hm₁ _ (by clear * - this ho; omega) (by clear * - this ho d6; omega)
        (by clear * - this ho; omega)]
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
  · unfold feEndCostDk
    clear * - hk₁' hk₂ hk₃ hk₄ hk₅ hk₆; omega
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
      hm₁ _ (by clear * - h3 ho; omega) (by clear * - h3 ho d6 d7 d8; omega) (by clear * - h2; omega)]

end NegSSSP

end PlanarFlow
