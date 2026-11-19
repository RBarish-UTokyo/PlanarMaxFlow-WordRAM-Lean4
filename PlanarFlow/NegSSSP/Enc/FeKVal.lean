module

public import PlanarFlow.NegSSSP.Enc.FeEnd

/-!
# The composed encoder: Klein's encoding read off the memory

* `fePk p m`: the input words `m (β + i)`, `i ≤ Kw` (the slot copied by the node).
* **`fe_kval`**: if the memory holds the words of phase A (`SrcArrM`), the out-lists (`FeOut`),
  the reach bits `XR` of the targets, the orders `IV`, `IT`, `IF`, `IC`, `HD` of a tree `T`
  meeting `Klein.Compat` and of a cotree `C` of `T` rooted at the face of `g' 0`, and every word of
  the slot is at most `Kw`, then **`fePk p m` meets `Klein.KValNL`** for the map with the sources
  copied, the isolating lengths, the numbering `srcNum σ₀`, `n = NN` and the **linear** word bound
  `Bw = kBL N NN k k 0`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- **The input words of the slot.** -/
def fePk (p : FeP) (m : ℕ → ℕ) : Input :=
  ⟨List.ofFn (fun i : Fin (p.Kw + 1) => m (p.β + i)), fun _ => 0⟩

lemma fePk_getD (p : FeP) (m : ℕ → ℕ) (i : ℕ) :
    (fePk p m).data.getD i 0 = if i ≤ p.Kw then m (p.β + i) else 0 := by
  unfold fePk
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : i ≤ p.Kw
  · simp [h, show i < p.Kw + 1 by omega]
  · simp [h, show ¬ i < p.Kw + 1 by omega]

lemma fePk_getD_of_le {p : FeP} {m : ℕ → ℕ} {i : ℕ} (h : i ≤ p.Kw) :
    (fePk p m).data.getD i 0 = m (p.β + i) := by
  rw [fePk_getD]; simp [h]

/-- The offsets of Klein's input within the slot (for `omega`). -/
lemma FeP.ord3 (p : FeP) :
    iIV p.N p.NN p.k + p.A ≤ iIT p.N p.NN p.k ∧ iIT p.N p.NN p.k + p.A ≤ iIF p.N p.NN p.k ∧
    iIF p.N p.NN p.k + p.FN ≤ iIC p.N p.NN p.k ∧ iIC p.N p.NN p.k + p.FN ≤ iHD p.N p.NN p.k ∧
    iHD p.N p.NN p.k + 4 = iXT p.N p.NN p.k ∧ iXT p.N p.NN p.k + 2 * p.k ≤ p.Kw ∧
    iOL p.N p.NN p.k + p.N ≤ iIV p.N p.NN p.k ∧ p.A ≤ p.NN ∧ p.FN ≤ p.NN ∧
    p.NN = 2 * (p.A + p.N + p.FN) ∧ p.N = p.nD + 8 * p.k ∧ p.A = p.nV + 2 * p.k ∧
    p.FN = p.nF + 2 * p.k ∧ p.AE = p.A + p.N + p.FN ∧ 9 * p.N + 14 * p.AE + 2 * p.k + 4 ≤ p.Kw := by
  simp only [FeP.N, FeP.A, FeP.FN, FeP.AE, FeP.NN, FeP.Bw, FeP.Kw, iOL, iXT, iHD, iIV, iIT, iIF,
    iIC, kBL, aOUT]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | omega | trivial

/-- The bounds of `Klein.KValNL` on the word bound `Bw`. -/
lemma FeP.bw_bounds (p : FeP) :
    9 * p.N + 7 * p.NN + p.k + 4 + 2 * p.k ≤ p.Bw ∧ p.NN + 2 * p.N ≤ p.Bw ∧
      aOUT p.N + p.k * p.k ≤ p.Bw ∧ aRB p.NN + p.k * p.k ≤ p.Bw := by
  simp only [FeP.Bw, kBL, aOUT, aRB]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

set_option maxHeartbeats 8000000 in
open Classical in
/-- **Klein's encoding read off the memory** (see the module docstring). -/
theorem fe_kval {X : Finset D} {B : Finset V} (fd : FaceData N X B) (ℓ : D → ℤ)
    (σ₀ : fd.DQ ≃ Fin (Fintype.card fd.DQ)) (νv₀ : fd.VQ ≃ Fin (Fintype.card fd.VQ))
    (τ₀ : fd.FQ ≃ Fin (Fintype.card fd.FQ)) (p : FeP) (hD : p.nD = Fintype.card fd.DQ)
    (hk : p.k = fd.k) (hV : p.nV = Fintype.card fd.VQ) (hF : p.nF = Fintype.card fd.FQ)
    (w : SrcD fd.DQ fd.k → ℤ) (T : STFlow.DTree (srcMap fd.inst.cycle).dual) (C : STFlow.DTree (srcMap fd.inst.cycle))
    (ys : List (SrcV fd.VQ fd.k)) (cs : List (SrcF fd.FQ fd.k)) (m : ℕ → ℕ)
    (hT : Compat T (tripSrc (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0)
      (tripDst (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0) (srcG fd.inst.cycle (0 % fd.k))
      (tpar (MSSP.pieceGraph (srcMap fd.inst.cycle) (srcPiece fd.k (fd.P'.image fd.e)) (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w (srcNum σ₀))) (tripSrc (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0)))
    (hOT : Orders T ((List.finRange (Fintype.card (SrcV fd.VQ fd.k))).map (srcVNum νv₀).symm) ys)
    (hOC : Orders C ((List.finRange (Fintype.card (SrcF fd.FQ fd.k))).map (srcFNum τ₀).symm) cs)
    (hCr : C.root = (srcMap fd.inst.cycle).face (srcG fd.inst.cycle 0))
    (hoff : ∀ x, x ≠ C.root → ¬ T.InT (C.par x))
    (hA : SrcArrM fd.Q fd.k fd.g (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) σ₀ νv₀ τ₀ p.β p.SL p.N
      p.A p.AE m)
    (hO : FeOut (fd.P'.image fd.e) σ₀ νv₀ fd.inst.cycle p m)
    (hXR : ∀ i < fd.k, m (p.β + iXT p.N p.NN p.k + p.k + i) =
      if MSSP.Reach (MSSP.pieceGraph (srcMap fd.inst.cycle) (srcPiece fd.k (fd.P'.image fd.e)) (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w (srcNum σ₀))) ((srcMap fd.inst.cycle).tail (srcG fd.inst.cycle 0))
        (.inl (fd.Q.tail (fd.g i))) then 1 else 0)
    (hIV : ∀ i (h : i < ((List.finRange (Fintype.card (SrcV fd.VQ fd.k))).map
        (srcVNum νv₀).symm).length),
      m (p.β + iIV p.N p.NN p.k + i) = srcVNum νv₀
        ((List.finRange (Fintype.card (SrcV fd.VQ fd.k))).map (srcVNum νv₀).symm)[i])
    (hIT : ∀ i (h : i < ys.length), m (p.β + iIT p.N p.NN p.k + i) = srcNum σ₀ (T.par ys[i]))
    (hIF : ∀ i (h : i < ((List.finRange (Fintype.card (SrcF fd.FQ fd.k))).map
        (srcFNum τ₀).symm).length),
      m (p.β + iIF p.N p.NN p.k + i) = (p.A + p.N) + srcFNum τ₀
        ((List.finRange (Fintype.card (SrcF fd.FQ fd.k))).map (srcFNum τ₀).symm)[i])
    (hIC : ∀ i (h : i < cs.length), m (p.β + iIC p.N p.NN p.k + i) = srcNum σ₀ (C.par cs[i]))
    (hH0 : m (p.β + iHD p.N p.NN p.k) = ((List.finRange (Fintype.card (SrcV fd.VQ fd.k))).map
        (srcVNum νv₀).symm).length)
    (hH1 : m (p.β + iHD p.N p.NN p.k + 1) = ys.length)
    (hH2 : m (p.β + iHD p.N p.NN p.k + 2) = ((List.finRange (Fintype.card (SrcF fd.FQ fd.k))).map
        (srcFNum τ₀).symm).length)
    (hH3 : m (p.β + iHD p.N p.NN p.k + 3) = cs.length)
    (hbd : ∀ i ≤ p.Kw, m (p.β + i) ≤ p.Kw) :
    KValNL (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) (srcPiece fd.k (fd.P'.image fd.e)) (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w (srcNum σ₀)) (srcNum σ₀) p.NN p.Bw fd.k
      (fun i => .inl (fd.Q.tail (fd.g i))) (fePk p m) := by
  obtain ⟨cD, cV, cF⟩ := fe_cards (k := fd.k) (D := fd.DQ) (V := fd.VQ) (F := fd.FQ) p hD hk hV hF
  have hkw := p.kw_eq
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15⟩ := p.ord3
  have h2k : 2 ≤ fd.k := fd.inst.cycle.two_le
  have hNNe : 2 * (Fintype.card (SrcV fd.VQ fd.k) + Fintype.card (SrcD fd.DQ fd.k) +
      Fintype.card (SrcF fd.FQ fd.k)) = p.NN := by rw [cV, cD, cF]; clear * - o10; omega
  -- the words of phase A
  obtain ⟨hKI, hKB, hXN, hLay⟩ := srcArr_kinput (M := fd.Q) (k := fd.k) (g := fd.g)
    (S := fd.P'.image fd.e) (ℓ := faceLen fd.P' fd.e ℓ) (σ₀ := σ₀) (νv₀ := νv₀) (τ₀ := τ₀)
    fd.inst.cycle (β := p.β) (SLb := p.SL) (N := p.N) (a := p.A) (ae := p.AE)
    (by rw [← hk]; clear * - o11 hD; omega) (by rw [← hk]; clear * - o12 hV; omega)
    (by rw [← hk]; clear * - o12 o13 o14 hF; omega) hA.1 hA.2 (fePk p m)
    (fun i hi => fePk_getD_of_le (by rw [← hk] at hi; clear * - hi o15; omega)) (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w (srcNum σ₀))
  rw [hNNe] at hKB hXN hLay
  have hW : ∀ i, (fePk p m).data.getD i 0 ≤ p.Bw + 16 * (p.NN + 1) := fun i => by
    rw [fePk_getD, ← hkw.2]
    split_ifs with h
    · exact hbd i h
    · exact Nat.zero_le _
  -- the offsets
  have g : ∀ i, i ≤ p.Kw → (fePk p m).data.getD i 0 = m (p.β + i) := fun i h => fePk_getD_of_le h
  have oIV : iIV (Fintype.card (SrcD fd.DQ fd.k)) p.NN fd.k = iIV p.N p.NN p.k := by rw [cD, hk]
  have oIT : iIT (Fintype.card (SrcD fd.DQ fd.k)) p.NN fd.k = iIT p.N p.NN p.k := by rw [cD, hk]
  have oIF : iIF (Fintype.card (SrcD fd.DQ fd.k)) p.NN fd.k = iIF p.N p.NN p.k := by rw [cD, hk]
  have oIC : iIC (Fintype.card (SrcD fd.DQ fd.k)) p.NN fd.k = iIC p.N p.NN p.k := by rw [cD, hk]
  have oHD : iHD (Fintype.card (SrcD fd.DQ fd.k)) p.NN fd.k = iHD p.N p.NN p.k := by rw [cD, hk]
  have oXT : iXT (Fintype.card (SrcD fd.DQ fd.k)) p.NN fd.k = iXT p.N p.NN p.k := by rw [cD, hk]
  have lHD : iHD p.N p.NN p.k + 4 + 2 * p.k ≤ p.Kw := by
    clear * - o5 o6; omega
  have lA : p.A ≤ p.NN := o8
  have lF : p.FN ≤ p.NN := o9
  have hys : ys.length ≤ p.A := by have := orders_ylen_eq hOT; omega
  have hcs : cs.length ≤ p.FN := by have := orders_ylen_eq hOC; omega
  refine ⟨fun x => srcVNum νv₀ x, fun d => Fintype.card (SrcV fd.VQ fd.k) + eIx (srcMap fd.inst.cycle) (srcNum σ₀) d,
    fun y => Fintype.card (SrcV fd.VQ fd.k) + Fintype.card (SrcD fd.DQ fd.k) + srcFNum τ₀ y,
    fun d => Fintype.card (SrcV fd.VQ fd.k) + Fintype.card (SrcD fd.DQ fd.k) +
      Fintype.card (SrcF fd.FQ fd.k) + eIx (srcMap fd.inst.cycle) (srcNum σ₀) d, T, C,
    (List.finRange (Fintype.card (SrcV fd.VQ fd.k))).map (srcVNum νv₀).symm, ys,
    (List.finRange (Fintype.card (SrcF fd.FQ fd.k))).map (srcFNum τ₀).symm, cs,
    ?_, ?_, ?_, ?_, hW, hLay, hKI, hKB, ?_, ?_, ?_, hoff, hCr, hT⟩
  · rw [cD, ← hk]; exact p.bw_bounds.1
  · rw [cD]; exact p.bw_bounds.2.1
  · rw [cD, ← hk]; exact p.bw_bounds.2.2.1
  · rw [← hk]; exact p.bw_bounds.2.2.2
  · -- the out-lists
    have := FeOut.kout fd.inst.cycle cD hO (Pk := fePk p m)
      (fun i hi => g i (by clear * - hi o1 o2 o3 o4 o5 o6 o7; omega)) lA cV
    rwa [hk] at this
  · -- the targets
    refine ⟨fun i _ => ?_, fun i hi => hXN i hi, fun i hi => ?_⟩
    · rintro ⟨j, hj, hji⟩
      rw [srcTail_srcG fd.inst.cycle hj] at hji
      cases hji
    · rw [oXT, g _ (by clear * - hi o6 hk; omega),
        show p.β + (iXT p.N p.NN p.k + fd.k + i) = p.β + iXT p.N p.NN p.k + p.k + i by
          rw [hk]; ring]
      exact hXR i hi
  · -- the initial trees
    refine ⟨hOT, hOC, fun i h => ?_, fun i h => ?_, fun i h => ?_, fun i h => ?_, ?_, ?_, ?_, ?_⟩
    · have hl : i < p.A := by
        have h' := h; simp only [List.length_map, List.length_finRange] at h'; omega
      rw [oIV, g _ (by clear * - hl o1 o2 o3 o4 o5 o6; omega), ← Nat.add_assoc]
      exact hIV i h
    · rw [oIT, g _ (by clear * - h hys o1 o2 o3 o4 o5 o6; omega), ← Nat.add_assoc]
      exact hIT i h
    · have hl : i < p.FN := by
        have h' := h; simp only [List.length_map, List.length_finRange] at h'; omega
      rw [oIF, g _ (by clear * - hl o1 o2 o3 o4 o5 o6; omega), ← Nat.add_assoc, hIF i h,
        cV, cD]
    · rw [oIC, g _ (by clear * - h hcs o1 o2 o3 o4 o5 o6; omega), ← Nat.add_assoc]
      exact hIC i h
    · rw [oHD, g _ (by clear * - lHD; omega)]; exact hH0
    · rw [oHD, g _ (by clear * - lHD; omega), ← Nat.add_assoc]; exact hH1
    · rw [oHD, g _ (by clear * - lHD; omega), ← Nat.add_assoc]; exact hH2
    · rw [oHD, g _ (by clear * - lHD; omega), ← Nat.add_assoc]; exact hH3

end NegSSSP

end PlanarFlow
