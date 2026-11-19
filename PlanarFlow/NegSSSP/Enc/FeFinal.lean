module

public import PlanarFlow.NegSSSP.Enc.FeKVal
public import PlanarFlow.NegSSSP.NL.KPartNRun

/-!
# The composed encoder of a one-face instance (distances by Bellman–Ford)

`feProg p = feMidProg p ; feEndProg p ; feClamp β (Kw + 1) Kw`: **one natural-word program**
(`feProg_natOnly`) which, from the plain arrays of the map `fd.Q` of a one-face instance (`RV`,
`NT`, `NF`, `IS`, `LN` by a numbering `σ₀` of its darts, the darts `G` of its face) at `I0`,
writes Klein's encoding of the instance for the isolating lengths:

* **`fencNatNL_BF_exec`**: within `feCost p` steps, for the numbering `srcNum σ₀` of the darts of
  the map with the sources copied and some isolating weight `w`, the input words
  `fePk p c'.nmem` (the slot `[β, β + Kw]`) meet **`FEncNatNL fd ℓ NN Bw (srcNum σ₀) w`**
  (`NN = 2 (#V' + #F' + #D')`, the **linear** word bound `Bw = kBL #D' NN k k 0`), and for
  `Hc = kcnHc A FN (tripW …) k`: **`fdHI ≤ Hc ≤ kcnHc A FN (N · Lmax) k`** and **`KSlotN`** (the
  slot at `β`, the residues of the real constants at `RK` modulo `2 Hc + 1`) — the inputs of
  `node_exec_natNNL` for this instance. The memory changes only in `[β, END)`.

The distances of the first root (for the initial tree `T`) are computed by **Bellman–Ford**,
`O(#V' · #D')` (the term `A (24 N + 6)` of `feEndCost`): weaker than the `O(q log q)` of a heap
Dijkstra. The other phases are linear in the size of the map with the sources copied (plus the
`k²` of `Kw` in the final clamp).

Word-size hypotheses: `END ≤ W` (the layout), `Lmax ≤ W`, `Inf + Lmax ≤ W` (`Inf = A Lmax + 1`),
`2 kcnHc A FN (N Lmax) k + 1 ≤ W`, with `Lmax ≥ feIsoB A N FN (srcW …)` (a bound on the isolating
lengths): all polynomial in the size of the instance and the sum of its lengths.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- **The composed encoder.** -/
def feProg (p : FeP) : Stmt := .seq (feMidProg p) (.seq (feEndProg p) (feClamp p.β (p.Kw + 1) p.Kw))

theorem feProg_natOnly (p : FeP) : natOnly (feProg p) = true := by
  simp only [feProg, natOnly, feMidProg_natOnly, feEndProg_natOnly, feClamp_natOnly,
    Bool.and_self]

/-- **The cost bound of the encoder** (Bellman–Ford: `O(#V' · #D')`). -/
def feCost (p : FeP) : ℕ := feMidCost p + feEndCost p + (8 * (p.Kw + 1) + 7)

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

set_option maxHeartbeats 8000000 in
open Classical in
/-- **The composed encoder of a one-face instance** (see the module docstring). -/
theorem fencNatNL_BF_exec {X : Finset D} {B : Finset V} (fd : FaceData N X B) (ℓ : D → ℤ)
    (σ₀ : fd.DQ ≃ Fin (Fintype.card fd.DQ)) (νv₀ : fd.VQ ≃ Fin (Fintype.card fd.VQ))
    (τ₀ : fd.FQ ≃ Fin (Fintype.card fd.FQ)) (p : FeP) (hD : p.nD = Fintype.card fd.DQ)
    (hk : p.k = fd.k) (hV : p.nV = Fintype.card fd.VQ) (hF : p.nF = Fintype.card fd.FQ)
    (hW : p.END ≤ W)
    (hLm : feIsoB p.A p.N p.FN (srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ)).toNat ≤ p.Lmax)
    (hLW : p.Lmax ≤ W) (hIW : p.Inf + p.Lmax ≤ W)
    (hH : 2 * kcnHc p.A p.FN (p.N * p.Lmax) p.k + 1 ≤ W)
    (c : Config) (hc : WordsBounded W c)
    (hQRV : ∀ d, c.nmem (p.I0 + σ₀ d) = σ₀ (fd.Q.rev d))
    (hQNT : ∀ d, c.nmem (p.I0 + p.nD + σ₀ d) = νv₀ (fd.Q.tail d))
    (hQNF : ∀ d, c.nmem (p.I0 + 2 * p.nD + σ₀ d) = τ₀ (fd.Q.face d))
    (hQIS : ∀ d, c.nmem (p.I0 + 3 * p.nD + σ₀ d) = if d ∈ fd.P'.image fd.e then 1 else 0)
    (hQLN : ∀ d, c.nmem (p.I0 + 4 * p.nD + σ₀ d) = (faceLen fd.P' fd.e ℓ d).toNat)
    (hQG : ∀ i < fd.k, c.nmem (p.I0 + 5 * p.nD + i) = σ₀ (fd.g i)) :
    ∃ c' t, Exec P W (feProg p) c c' t ∧ t ≤ feCost p ∧
      ∃ (w : SrcD fd.DQ fd.k → ℤ) (Hc : ℕ),
        FEncNatNL fd ℓ p.NN p.Bw (srcNum σ₀) w (fePk p c'.nmem) ∧
        fdHI fd ℓ (srcNum σ₀) w ≤ (Hc : ℝ) ∧ Hc ≤ kcnHc p.A p.FN (p.N * p.Lmax) p.k ∧
        KSlotN (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) (srcPiece fd.k (fd.P'.image fd.e)) (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w (srcNum σ₀)) (srcNum σ₀) p.Bw p.NN p.β p.RK
          (2 * Hc + 1) (fePk p c'.nmem) c' ∧
        (∀ a, a < p.β ∨ p.END ≤ a → c'.nmem a = c.nmem a) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨cD, cV, cF⟩ := fe_cards (k := fd.k) (D := fd.DQ) (V := fd.VQ) (F := fd.FQ) p hD hk hV hF
  have hkw := p.kw_eq
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15⟩ := p.ord3
  have ho := p.ord
  have hSL : p.SL = p.β + p.Kw + 1 := rfl
  have hk2 : 2 ≤ p.k := by rw [hk]; exact fd.inst.cycle.two_le
  -- phases A to C
  obtain ⟨c₁, k₁, e₁, hk₁, C₀, w, hC₀r, hPA, hw, hwB, hA, hO, hISO, hRK, hHI, hHle, hMK, hXR,
    hm₁, hr₁, hrm₁, ho₁⟩ :=
    feMid_exec (P := P) fd ℓ σ₀ νv₀ τ₀ p hD hk hV hF hW hLm hLW hH c hc hQRV hQNT hQNF hQIS hQLN
      hQG
  -- phase D
  obtain ⟨c₂, k₂, e₂, hk₂, T, C, ys, cs, hT, hOT, hOC, hCr, hoff, hIV, hIT, hIF, hIC, hH0, hH1,
    hH2, hH3, hm₂, hr₂, hrm₂, ho₂⟩ :=
    feEnd_exec (P := P) fd ℓ σ₀ νv₀ τ₀ p hD hk hV hF hW hLm hIW hw hwB C₀ hC₀r c₁ e₁.wb_right hA
      hPA hISO hMK
  -- the clamp of the slot
  obtain ⟨c₃, k₃, e₃, hk₃, hcl, hm₃, -, hr₃, hrm₃, ho₃⟩ :=
    feClamp_exec (P := P) (Dst := p.β) (len := p.Kw + 1) (B := p.Kw)
      (by clear * - ho hW hSL; omega) (by clear * - ho hW hSL; omega)
      (by clear * - ho hW hSL; omega) c₂ e₂.wb_right
  have hCA : ∀ x, ClampAg c₂.nmem c₃.nmem p.Kw x := fun x => by
    by_cases h : p.β ≤ x ∧ x < p.β + (p.Kw + 1)
    · right; have := hcl (x - p.β) (by clear * - h; omega)
      rwa [show p.β + (x - p.β) = x by clear * - h; omega] at this
    · left; exact hm₃ x (by clear * - h; omega)
  have hKwA : 2 * p.AE ≤ p.Kw := by clear * - o14 o15; omega
  -- the words of phase A, the out-lists, through phase D and the clamp
  have hA₂ := hA.keep hD hk hV hF fun x hx => hm₂ x
    (by clear * - hx ho o1 o2 o3 o4 o5 o7; omega) (by clear * - hx ho; omega)
    (by clear * - hx ho; omega)
  have hA₃ := SrcArrM.of (Bd := p.Kw) (by rw [← hk]; clear * - o11 hD; omega)
    (by rw [← hk]; clear * - o12 hV; omega) (by rw [← hk]; clear * - o12 o13 o14 hF; omega) hKwA
    hA₂ (fun j _ => hCA _) (fun i _ => hCA _)
    (fun j hj => hm₃ _ (by clear * - hj ho hSL; omega))
  have hO₂ := FeOut.of fd.inst.cycle cV (Bd := p.N) le_rfl hO fun x h1 h2 =>
    ClampAg.of_eq (hm₂ x (by clear * - h2 ho o7; omega) (by clear * - h2 ho; omega)
      (by clear * - h2 ho; omega))
  have hO₃ := FeOut.of fd.inst.cycle cV (Bd := p.Kw) (by clear * - hKwA o14; omega) hO₂
    fun x _ _ => hCA x
  -- the words of `KInit` and the reach bits of the targets
  have hNA : p.N + p.A + p.FN ≤ p.Kw := by clear * - hKwA o14; omega
  have hys : ys.length ≤ p.A := by have := orders_ylen_eq hOT; clear * - this cV; omega
  have hcs : cs.length ≤ p.FN := by have := orders_ylen_eq hOC; clear * - this cF; omega
  have keep3 : ∀ x v, c₂.nmem x = v → v ≤ p.Kw → c₃.nmem x = v := fun x v h hv => (hCA x).eq h hv
  have hXR₃ : ∀ i < fd.k, c₃.nmem (p.β + iXT p.N p.NN p.k + p.k + i) =
      if MSSP.Reach (MSSP.pieceGraph (srcMap fd.inst.cycle) (srcPiece fd.k (fd.P'.image fd.e)) (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w (srcNum σ₀))) ((srcMap fd.inst.cycle).tail (srcG fd.inst.cycle 0))
        (.inl (fd.Q.tail (fd.g i))) then 1 else 0 := fun i hi => by
    refine keep3 _ _ ?_ (by split_ifs <;> clear * - hNA hk2 o12 <;> omega)
    rw [hm₂ _ (by clear * - hi hk o5; omega) (by clear * - hi hk ho; omega)
      (by clear * - hi hk ho o5 o6; omega)]
    exact hXR i hi
  have hbd : ∀ i ≤ p.Kw, c₃.nmem (p.β + i) ≤ p.Kw := fun i hi => by
    rw [hcl i (by clear * - hi; omega)]; exact min_le_right _ _
  have hIV₃ : ∀ i (h : i < ((List.finRange (Fintype.card (SrcV fd.VQ fd.k))).map
      (srcVNum νv₀).symm).length),
      c₃.nmem (p.β + iIV p.N p.NN p.k + i) = srcVNum νv₀
        ((List.finRange (Fintype.card (SrcV fd.VQ fd.k))).map (srcVNum νv₀).symm)[i] :=
    fun i h => keep3 _ _ (hIV i h) (by
      have := (srcVNum νv₀ ((List.finRange (Fintype.card (SrcV fd.VQ fd.k))).map
        (srcVNum νv₀).symm)[i]).2
      clear * - this cV hNA; omega)
  have hIT₃ : ∀ i (h : i < ys.length), c₃.nmem (p.β + iIT p.N p.NN p.k + i) =
      srcNum σ₀ (T.par ys[i]) :=
    fun i h => keep3 _ _ (hIT i h) (by have := (srcNum σ₀ (T.par ys[i])).2; clear * - this cD hNA; omega)
  have hIF₃ : ∀ i (h : i < ((List.finRange (Fintype.card (SrcF fd.FQ fd.k))).map
      (srcFNum τ₀).symm).length),
      c₃.nmem (p.β + iIF p.N p.NN p.k + i) = (p.A + p.N) + srcFNum τ₀
        ((List.finRange (Fintype.card (SrcF fd.FQ fd.k))).map (srcFNum τ₀).symm)[i] :=
    fun i h => keep3 _ _ (hIF i h) (by
      have := (srcFNum τ₀ ((List.finRange (Fintype.card (SrcF fd.FQ fd.k))).map
        (srcFNum τ₀).symm)[i]).2
      clear * - this cF hNA; omega)
  have hIC₃ : ∀ i (h : i < cs.length), c₃.nmem (p.β + iIC p.N p.NN p.k + i) =
      srcNum σ₀ (C.par cs[i]) :=
    fun i h => keep3 _ _ (hIC i h) (by have := (srcNum σ₀ (C.par cs[i])).2; clear * - this cD hNA; omega)
  have hH0₃ := keep3 _ _ hH0 (by simp only [List.length_map, List.length_finRange]; clear * - cV hNA; omega)
  have hH1₃ := keep3 _ _ hH1 (by clear * - hys hNA; omega)
  have hH2₃ := keep3 _ _ hH2 (by simp only [List.length_map, List.length_finRange]; clear * - cF hNA; omega)
  have hH3₃ := keep3 _ _ hH3 (by clear * - hcs hNA; omega)
  have hK := fe_kval fd ℓ σ₀ νv₀ τ₀ p hD hk hV hF w T C ys cs c₃.nmem hT hOT hOC hCr hoff hA₃ hO₃
    hXR₃ hIV₃ hIT₃ hIF₃ hIC₃ hH0₃ hH1₃ hH2₃ hH3₃ hbd
  refine ⟨c₃, k₁ + (k₂ + k₃), Exec.seq e₁ (Exec.seq e₂ e₃), ?_, w,
    kcnHc p.A p.FN (tripW (srcPiece fd.k (fd.P'.image fd.e)) (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w (srcNum σ₀))).toNat fd.k,
    ⟨by rw [cV, cF, cD]; clear * - o10; omega, hw, hwB, hK⟩, hHI, hHle,
    ⟨fun i hi => (fePk_getD_of_le (by rw [hkw.2]; exact hi)).symm, fun a ha => ?_⟩,
    fun a ha => ?_, by rw [hr₃, hr₂, hr₁], by rw [hrm₃, hrm₂, hrm₁], by rw [ho₃, ho₂, ho₁]⟩
  · unfold feCost; clear * - hk₁ hk₂ hk₃; omega
  · rw [cD] at ha
    rw [hm₃ _ (by clear * - ha ho hSL; omega), hm₂ _ (by clear * - ha ho o5 o6; omega)
      (by clear * - ha ho; omega) (by clear * - ha ho; omega)]
    exact hRK a ha
  · rw [hm₃ _ (by clear * - ha ho o5 o6 hSL; omega), hm₂ _ (by clear * - ha ho o5 o6; omega)
      (by clear * - ha ho; omega) (by clear * - ha ho; omega), hm₁ a ha]

end NegSSSP

end PlanarFlow
