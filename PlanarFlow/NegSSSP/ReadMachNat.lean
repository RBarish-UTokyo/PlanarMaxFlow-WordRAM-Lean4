module

public import PlanarFlow.BKMNW.ReadMach
public import PlanarFlow.Klein.DivRead
public import PlanarFlow.MSSP.Isolate

/-!
# Klein's answers at a node on natural words, read back by the machine's `divN`

`PlanarFlow/BKMNW/ReadMach.lean` realizes the calls of multiple-source shortest paths at a node
by Klein's program **with real registers** on the perturbed lengths (`MSSP.pert`, words of
`|D|` bits), read back by `NegSSSP.rdProg`, a binary search on the real side, within the field
`mssp` of `cNegMach` only for polynomially bounded reduced lengths (`1 + Σ ℓ ≤ m ^ e`). This file
replaces both by natural words:

* `Klein.src_exec_natD`: on the map with the sources copied, Klein's program **on natural
  words** (`kleinProgNDC`: no real instruction) on the **isolating** lengths `ℓ'` of the
  lengths with the sources copied (`MSSP.HypNN.exists_iso`, `0 < ℓ' < N₁ (ℓ + 1)`), followed by
  the read-back loop `divCutLoop` (`PlanarFlow/Klein/DivRead.lean`): the `k t` answer words
  divided by `N₁` with `divN`, the reach words cleared where the quotient is not below the cut
  `W = srcW` (by truncated subtractions and a product); its words are at most
  `kleinWN B n Hc + N₁ + W` (`Hc < kleinHI + 1`); the natural answers read at the end
  (`kOutNK`) **are the distances in the piece from the vertices of the face**, for all lengths.
* `faceInst_exec_natD`: the same on a one-face instance (`FaceInst`), within
  `4 · 2372500000 (q lg q + k² lg q) + 14 k² + 12` steps.
* `cNegMach_mssp_read_exec'`: **Klein's run on natural words with the read-back by `divN` is
  within the field `mssp` of `cNegMach`, with no hypothesis on the size of the lengths**: at a
  node meeting `SplitF`, for the part `X` with the reduced lengths `redLen N ℓ δ`, the answers
  read at the end are the values of `mssp` (any `PieceMSSPSpec`) between the shared vertices.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP WordRAM WordRAM.Machine

section Src

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {k : ℕ} {g : ℕ → D}
  (hf : FaceCycle M k g) {S : Finset D} {ℓ : D → ℤ}

include hf in
/-- **Klein's program on the map with the sources copied, on natural words, with the read-back
by the machine** (`src_exec` on natural words): there are isolating lengths `ℓ'` of the lengths
with the sources copied (`0 < ℓ' d < N₁ (srcLen ℓ W d + 1)` on the piece,
`N₁ = isoN1 #V' #D' #F'` of the map with the sources copied), a bound
`kleinHI ≤ Hc < kleinHI + 1`, an input and a starting configuration such that the natural-word
program `kleinProgNDC` (Klein's program modulo `2 Hc + 1`, then the `k t` answer words divided by
`N₁` with `divN` and cut off at `W = srcW S ℓ`) runs from `natCfg c₀` with words at most
`kleinWN B n Hc + N₁ + W` within `4 · 2372500000 (N lg N + k t lg N) + 14 k t + 12` steps,
`N = #V + #F + #D` the size of `M`, prints nothing, and for every `j < k` and `i < t` the natural
answer read at the end (`kOutNK`) is the distance in the piece of `M` from `tail (g j)` to `X i`.
No hypothesis bounds the lengths. -/
theorem src_exec_natD (hM : M.IsPlane) (hrot : M.RotTrans) (hnn : ∀ d ∈ S, 0 ≤ ℓ d) (t : ℕ)
    (X : ℕ → V) :
    ∃ (ℓ' : SrcD D k → ℤ) (n B Hc : ℕ) (P : Input) (c₀ c' : Config) (steps : ℕ),
      n = 2 * (Fintype.card (SrcV V k) + Fintype.card (SrcF F k) + Fintype.card (SrcD D k)) ∧
      (∀ d ∈ srcPiece k S, 0 < ℓ' d ∧ ℓ' d < isoN1 (Fintype.card (SrcV V k))
        (Fintype.card (SrcD D k)) (Fintype.card (SrcF F k)) * (srcLen ℓ (srcW S ℓ) d + 1)) ∧
      kleinHI (SrcV V k) (SrcF F k) (srcPiece k S) ℓ' k ≤ Hc ∧
      (Hc : ℝ) < kleinHI (SrcV V k) (SrcF F k) (srcPiece k S) ℓ' k + 1 ∧
      Exec P (kleinWN B n Hc + isoN1 (Fintype.card (SrcV V k)) (Fintype.card (SrcD D k))
          (Fintype.card (SrcF F k)) + (srcW S ℓ).toNat)
        (kleinProgNDC B (Fintype.card (SrcD D k)) n k t Hc (k * t)
          (isoN1 (Fintype.card (SrcV V k)) (Fintype.card (SrcD D k)) (Fintype.card (SrcF F k)))
          (srcW S ℓ).toNat)
        (natCfg 201 (B + 16 * (n + 1)) (2 * Hc + 1) (B + 16 * (n + 1) + 1) c₀) c' steps ∧
      steps ≤ 4 * (2372500000 * ((Fintype.card V + Fintype.card F + Fintype.card D) *
          BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D) +
        k * t * BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D))) +
          14 * (k * t) + 12 ∧
      (∀ j < k, ∀ i < t, kOutNK (Fintype.card (SrcD D k)) n t (B + 16 * (n + 1) + 1) c' j i =
          odist (pieceGraph M S ℓ) (M.tail (g j)) (X i)) ∧
      c'.output = c₀.output := by
  have H0 := srcMap_hypNN hf hM hrot hnn (srcW_pos hnn).le
  obtain ⟨w, -, -, hHyp, hlen, hdiv⟩ :=
    H0.exists_iso (Fintype.equivFin (SrcD D k)) ((srcMap hf).face (srcG hf 0))
  set ℓ' := isoLen (Fintype.card (SrcV V k)) (Fintype.card (SrcD D k)) (Fintype.card (SrcF F k))
    w (fun d => (Fintype.equivFin (SrcD D k) d : ℕ)) (srcLen ℓ (srcW S ℓ)) with hℓ'
  have hR := srcMap_sameReach hf (S := S) ℓ'
  have hX : ∀ i < t, ¬ IsRoot (srcMap hf) k (srcG hf) (.inl (X i)) := by
    rintro i - ⟨j, hj, hji⟩
    rw [srcTail_srcG hf hj] at hji
    cases hji
  obtain ⟨n, B, Hc, P, c₀, c', steps, hn, hHc, hHc', hE, hs, hd, hout⟩ :=
    klein_exec_exists_natDC hHyp hR t (fun i => .inl (X i)) hX
      (isoN1 (Fintype.card (SrcV V k)) (Fintype.card (SrcD D k)) (Fintype.card (SrcF F k)))
      (srcW S ℓ).toNat
  refine ⟨ℓ', n, B, Hc, P, c₀, c', steps, hn, hlen, hHc, hHc', hE, ?_, fun j hj i hi => ?_, hout⟩
  · set N := Fintype.card V + Fintype.card F + Fintype.card D with hN
    have hk : k ≤ Fintype.card V := by
      have hinj : Function.Injective fun i : Fin k => M.tail (g i) := fun i j h =>
        Fin.ext (hf.inj _ i.2 _ j.2 h)
      simpa using Fintype.card_le_of_injective _ hinj
    have hN1 : 1 ≤ N := by have := hf.two_le; omega
    have e : Fintype.card (SrcV V k) + Fintype.card (SrcF F k) + Fintype.card (SrcD D k) =
        N + 12 * k := by
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
        card_srcKind, hN]
      ring
    rw [e] at hs
    have h13 : N + 12 * k ≤ 13 * N := by omega
    have hl : BKMNW.lg (N + 12 * k) ≤ 5 * BKMNW.lg N := by
      have h1 := BKMNW.lg_mono (show N + 12 * k ≤ 16 * N by omega)
      have h2 := lg_sixteen_mul hN1
      have h3 := BKMNW.one_le_lg N
      omega
    have h4 : (N + 12 * k) * BKMNW.lg (N + 12 * k) ≤ 13 * N * (5 * BKMNW.lg N) :=
      Nat.mul_le_mul h13 hl
    have h5 : k * t * BKMNW.lg (N + 12 * k) ≤ k * t * (5 * BKMNW.lg N) :=
      Nat.mul_le_mul_left _ hl
    have e4 : 13 * N * (5 * BKMNW.lg N) = 65 * (N * BKMNW.lg N) := by ring
    have e5 : k * t * (5 * BKMNW.lg N) = 5 * (k * t * BKMNW.lg N) := by ring
    omega
  · have e : tripSrc (srcMap hf) k (srcG hf) j = .inr (⟨j, hj⟩, false) := by
      unfold tripSrc; rw [Nat.mod_eq_of_lt hj]; exact srcTail_srcG hf hj
    rw [hd j hj i hi, hdiv, e, Int.toNat_of_nonneg (srcW_pos hnn).le]
    exact odist_src hf hnn ⟨j, hj⟩ (X i)

end Src

end Klein

namespace NegSSSP

open Finset BKMNW CombMap WordRAM WordRAM.Machine

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

section Exec

variable {P : Finset D} {B : Finset V} {q k : ℕ} {DQ VQ FQ : Type u} [Fintype DQ]
  [DecidableEq DQ] [Fintype VQ] [DecidableEq VQ] [Fintype FQ] [DecidableEq FQ]
  {Q : CombMap DQ VQ FQ} {g : ℕ → DQ} {P' : Finset D} {e : D → DQ} {j : V → VQ}

/-- **Klein's program on a one-face instance, on natural words, with the read-back by `divN`**
(`faceInst_exec` on natural words): `kleinProgNDC` on the map of the instance with the sources
copied and the isolating lengths `ℓ'` of `faceLen` with the sources copied runs from `natCfg c₀`
with words at most `kleinWN Bw n Hc + N₁ + srcW` (`kleinHI ≤ Hc < kleinHI + 1`) within
`4 · 2372500000 (q lg q + k² lg q) + 14 k² + 12` steps, prints nothing, and for all sources `b`,
`b'` the natural answer read at the end (`kOutNK`) is the distance in the piece `P` from `b` to
`b'`. -/
theorem faceInst_exec_natD (h : FaceInst N P B q k Q g P' e j) {ℓ : D → ℤ}
    (hnn : ∀ d ∈ P, 0 ≤ ℓ d) :
    ∃ (ℓ' : Klein.SrcD DQ k → ℤ) (n Bw Hc : ℕ) (I : Input) (c₀ c' : Config) (steps : ℕ),
      (∀ d ∈ Klein.srcPiece k (P'.image e), 0 < ℓ' d ∧
        ℓ' d < MSSP.isoN1 (Fintype.card (Klein.SrcV VQ k)) (Fintype.card (Klein.SrcD DQ k))
          (Fintype.card (Klein.SrcF FQ k)) *
          (Klein.srcLen (faceLen P' e ℓ) (Klein.srcW (P'.image e) (faceLen P' e ℓ)) d + 1)) ∧
      Klein.kleinHI (Klein.SrcV VQ k) (Klein.SrcF FQ k) (Klein.srcPiece k (P'.image e)) ℓ' k ≤
        Hc ∧
      (Hc : ℝ) <
        Klein.kleinHI (Klein.SrcV VQ k) (Klein.SrcF FQ k) (Klein.srcPiece k (P'.image e)) ℓ' k +
          1 ∧
      Exec I (Klein.kleinWN Bw n Hc + MSSP.isoN1 (Fintype.card (Klein.SrcV VQ k))
          (Fintype.card (Klein.SrcD DQ k)) (Fintype.card (Klein.SrcF FQ k)) +
          (Klein.srcW (P'.image e) (faceLen P' e ℓ)).toNat)
        (Klein.kleinProgNDC Bw (Fintype.card (Klein.SrcD DQ k)) n k k Hc (k * k)
          (MSSP.isoN1 (Fintype.card (Klein.SrcV VQ k)) (Fintype.card (Klein.SrcD DQ k))
            (Fintype.card (Klein.SrcF FQ k))) (Klein.srcW (P'.image e) (faceLen P' e ℓ)).toNat)
        (Klein.natCfg 201 (Bw + 16 * (n + 1)) (2 * Hc + 1) (Bw + 16 * (n + 1) + 1) c₀) c' steps ∧
      steps ≤ 4 * (2372500000 * (q * lg q + k ^ 2 * lg q)) + 14 * k ^ 2 + 12 ∧
      (∀ b ∈ B, ∃ i < k, Q.tail (g i) = j b ∧ ∀ b' ∈ B, ∃ i' < k, Q.tail (g i') = j b' ∧
        Klein.kOutNK (Fintype.card (Klein.SrcD DQ k)) n k (Bw + 16 * (n + 1) + 1) c' i i' =
          MSSP.odist (MSSP.pieceGraph N P ℓ) b b') ∧
      c'.output = c₀.output := by
  have hnnQ : ∀ y ∈ P'.image e, 0 ≤ faceLen P' e ℓ y := fun y _ => faceLen_nonneg _ _ _ y
  obtain ⟨ℓ', n, Bw, Hc, I, c₀, c', steps, -, hlen, hHc, hHc', hE, hs, hd, hout⟩ :=
    Klein.src_exec_natD h.cycle h.plane h.rot hnnQ k fun i => Q.tail (g i)
  have hℓ : ∀ d ∈ P', faceLen P' e ℓ (e d) = ℓ d := fun d hd =>
    faceLen_e h.injE (fun d' hd' => hnn d' (h.sub hd')) hd
  refine ⟨ℓ', n, Bw, Hc, I, c₀, c', steps, hlen, hHc, hHc', hE, hs.trans ?_, fun b hb => ?_,
    hout⟩
  · have hN := h.card
    have hl := lg_mono hN
    have h1 : (Fintype.card VQ + Fintype.card FQ + Fintype.card DQ) *
        lg (Fintype.card VQ + Fintype.card FQ + Fintype.card DQ) ≤ q * lg q :=
      Nat.mul_le_mul hN hl
    have h2 : k * k * lg (Fintype.card VQ + Fintype.card FQ + Fintype.card DQ) ≤ k ^ 2 * lg q := by
      rw [← sq]; exact Nat.mul_le_mul_left _ hl
    have h3 := Nat.mul_le_mul_left 2372500000 (Nat.add_le_add h1 h2)
    have hkk : k * k = k ^ 2 := (sq k).symm
    rw [hkk] at hs h3
    omega
  · obtain ⟨i, hi, hib⟩ := h.src b hb
    have hD := h.isDist hℓ hb (isDist_odist (fun a => faceLen_nonneg _ _ _ a.1) _)
    have hE' := odist_eq_of_isDist (fun a => hnn a.1 a.2) hD
    refine ⟨i, hi, hib, fun b' hb' => ?_⟩
    obtain ⟨i', hi', hib'⟩ := h.src b' hb'
    refine ⟨i', hi', hib', ?_⟩
    rw [hd i hi i' hi', hib, hib', ← hE']
    simp [hb']

end Exec

/-! ### The node: Klein's run on natural words with the read-back, within the field `mssp` -/

/-- **The two calls of multiple-source shortest paths at a node on natural words, with the
answers read back by the machine (`divN`), within the field `mssp` of `cNegMach`, for all
lengths** (`cNegMach_mssp_read_exec` without the hypothesis `1 + Σ_X ℓ ≤ m ^ e`): at a node
meeting `SplitF` with shared vertices `B`, for the part `X` with the reduced lengths
`redLen N ℓ δ` (nonnegative), there are a one-face instance `fd`, isolating lengths `ℓ'` on its
map with the sources copied, a bound `kleinHI ≤ Hc < kleinHI + 1` and a run of the natural-word
program `kleinProgNDC` (Klein's program modulo `2 Hc + 1`, then the `k²` answer words divided by
`N₁` with `divN` and cut off at the bound `srcW` of the instance; no real instruction,
`kleinProgNDC_natOnly`) with words at most `kleinWN Bw n Hc + N₁ + srcW`, within
`cNegMach.mssp m b` steps, ending with **the values of `mssp`** (any `PieceMSSPSpec`) between the
shared vertices **in its natural answers** (`kOutNK`). -/
theorem cNegMach_mssp_read_exec' (C : ℕ) {P P₀ P₁ : Finset D} (h : SplitF N P P₀ P₁)
    (hB : (bdry N P₀ P₁).Nonempty) {ℓ : D → ℤ} {δ : V → ℤ} {X : Finset D}
    (hX : X = P₀ ∨ X = P₁) (hnn : ∀ d ∈ X, 0 ≤ redLen N ℓ δ d)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ} (hmssp : PieceMSSPSpec N mssp) :
    ∃ fd : FaceData N X (bdry N P₀ P₁), ∃ (ℓ' : Klein.SrcD fd.DQ fd.k → ℤ) (n Bw Hc : ℕ)
      (I : Input) (c₀ c' : Config) (steps : ℕ),
      (∀ d ∈ Klein.srcPiece fd.k (fd.P'.image fd.e), 0 < ℓ' d ∧
        ℓ' d < MSSP.isoN1 (Fintype.card (Klein.SrcV fd.VQ fd.k))
          (Fintype.card (Klein.SrcD fd.DQ fd.k)) (Fintype.card (Klein.SrcF fd.FQ fd.k)) *
          (Klein.srcLen (faceLen fd.P' fd.e (redLen N ℓ δ))
            (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e (redLen N ℓ δ))) d + 1)) ∧
      Klein.kleinHI (Klein.SrcV fd.VQ fd.k) (Klein.SrcF fd.FQ fd.k)
        (Klein.srcPiece fd.k (fd.P'.image fd.e)) ℓ' fd.k ≤ Hc ∧
      (Hc : ℝ) < Klein.kleinHI (Klein.SrcV fd.VQ fd.k) (Klein.SrcF fd.FQ fd.k)
        (Klein.srcPiece fd.k (fd.P'.image fd.e)) ℓ' fd.k + 1 ∧
      Exec I (Klein.kleinWN Bw n Hc + MSSP.isoN1 (Fintype.card (Klein.SrcV fd.VQ fd.k))
          (Fintype.card (Klein.SrcD fd.DQ fd.k)) (Fintype.card (Klein.SrcF fd.FQ fd.k)) +
          (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e (redLen N ℓ δ))).toNat)
        (Klein.kleinProgNDC Bw (Fintype.card (Klein.SrcD fd.DQ fd.k)) n fd.k fd.k Hc
          (fd.k * fd.k)
          (MSSP.isoN1 (Fintype.card (Klein.SrcV fd.VQ fd.k)) (Fintype.card (Klein.SrcD fd.DQ fd.k))
            (Fintype.card (Klein.SrcF fd.FQ fd.k)))
          (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e (redLen N ℓ δ))).toNat)
        (Klein.natCfg 201 (Bw + 16 * (n + 1)) (2 * Hc + 1) (Bw + 16 * (n + 1) + 1) c₀) c' steps ∧
      steps ≤ (cNegMach C).mssp P.card (bdry N P₀ P₁).card ∧
      c'.output = c₀.output ∧
      (∀ b ∈ bdry N P₀ P₁, ∃ i < fd.k, fd.Q.tail (fd.g i) = fd.j b ∧
        ∀ b' ∈ bdry N P₀ P₁, ∃ i' < fd.k, fd.Q.tail (fd.g i') = fd.j b' ∧
          Klein.kOutNK (Fintype.card (Klein.SrcD fd.DQ fd.k)) n fd.k (Bw + 16 * (n + 1) + 1) c'
            i i' = mssp X (redLen N ℓ δ) (bdry N P₀ P₁) b b') := by
  have h' := h
  obtain ⟨-, -, h0, -, -, -, -, -, hw⟩ := h'
  have hm : 1 ≤ P.card := by
    have := card_le_card (h.1 ▸ subset_union_left : P₀ ⊆ P); omega
  obtain ⟨k, hk, h₀, h₁⟩ := hw hB
  have hX' : OneFace N X (bdry N P₀ P₁) (18 * P.card) k := by
    rcases hX with rfl | rfl
    · exact h₀
    · exact h₁
  obtain ⟨DQ, VQ, FQ, i1, i2, i3, i4, i5, i6, Q, g, P', e, j, hI⟩ := hX'
  obtain ⟨ℓ', n, Bw, Hc, I, c₀, c', steps, hlen, hHc, hHc', hE, hs, hR, hout⟩ :=
    faceInst_exec_natD (ℓ := redLen N ℓ δ) hI hnn
  let fd : FaceData N X (bdry N P₀ P₁) := ⟨18 * P.card, k, DQ, VQ, FQ, Q, g, P', e, j, hI⟩
  refine ⟨fd, ℓ', n, Bw, Hc, I, c₀, c', steps, hlen, hHc, hHc', hE, hs.trans ?_, hout,
    fun b hb => ?_⟩
  · -- the cost
    set m := P.card with hmdef
    have hl := lg_eighteen_mul hm
    have hl1 := one_le_lg m
    have hkk : k ^ 2 * lg (18 * m) ≤ 1200 * m * (6 * lg m) := Nat.mul_le_mul hk hl
    have hqq : 18 * m * lg (18 * m) ≤ 18 * m * (6 * lg m) := Nat.mul_le_mul_left _ hl
    have hmX : m ≤ m * lg m := Nat.le_mul_of_pos_right _ (by omega)
    have e1 : 18 * m * (6 * lg m) + 1200 * m * (6 * lg m) = 7308 * (m * lg m) := by ring
    have hb2 : 0 ≤ (bdry N P₀ P₁).card ^ 2 * lg m := Nat.zero_le _
    show 4 * (2372500000 * (18 * m * lg (18 * m) + k ^ 2 * lg (18 * m))) + 14 * k ^ 2 + 12 ≤
      32886 * 2372500000 * (m * lg m + (bdry N P₀ P₁).card ^ 2 * lg m)
    have : 32886 * 2372500000 * (m * lg m + (bdry N P₀ P₁).card ^ 2 * lg m) =
        32886 * 2372500000 * (m * lg m) + 32886 * 2372500000 * ((bdry N P₀ P₁).card ^ 2 * lg m) :=
      by ring
    rw [this]
    omega
  · -- the answers
    obtain ⟨i, hi, hib, hK'⟩ := hR b hb
    refine ⟨i, hi, hib, fun b' hb' => ?_⟩
    obtain ⟨i', hi', hib', hK''⟩ := hK' b' hb'
    refine ⟨i', hi', hib', ?_⟩
    have hnn' : ∀ a, 0 ≤ (MSSP.pieceGraph N X (redLen N ℓ δ)).len a := fun a => hnn a.1 a.2
    have hms : mssp X (redLen N ℓ δ) (bdry N P₀ P₁) b b' =
        MSSP.odist (MSSP.pieceGraph N X (redLen N ℓ δ)) b b' := by
      have := odist_eq_of_isDist hnn' (hmssp X (redLen N ℓ δ) (bdry N P₀ P₁) hnn b hb)
      exact congrFun this b'
    rw [hms]
    exact hK''

end NegSSSP

end PlanarFlow
