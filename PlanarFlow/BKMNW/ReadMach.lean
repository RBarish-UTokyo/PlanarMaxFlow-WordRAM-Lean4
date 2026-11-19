module

public import PlanarFlow.BKMNW.MachCost
public import PlanarFlow.NegSSSP.ReadGlue
public import PlanarFlow.NegSSSP.BFExecP

/-!
# Reading Klein's answers at a node, and the field `mssp` of `cNegMach`

At a node of the decomposition by simple cycles (`SplitF`, shared vertices `B`, `b = |B|`), each
call of multiple-source shortest paths is realized by Klein's program on a one-face instance
(`NegSSSP.cNegMach_mssp_exec`), whose answers are perturbed: an answer is read back as the
integer part of a real divided by `2 ^ M` (`Klein.outNN`, `M` the darts of the instance with the
sources copied), cut off at the bound `Wc` of the instance (`Klein.srcOut`). The machine has no
real-to-integer rounding: `NegSSSP.rdProg` (`PlanarFlow/NegSSSP/ReadGlue.lean`) recovers the
integer part by a binary search over `L` bits on the real side, `O(L)` comparisons per answer.
This file proves:

* `rdOut_child`: the output of `rdProg` for the pair `(s, t)` is the entry of the matrices of
  `bfStartP` for the dense distance graph `childDDG` (the flag `finB (arcOf H β) s t` and the
  length `matOf H β s t`, with the shift `δ (β t) - δ (β s)`).
* `cNegMach_mssp_read_exec`: **Klein's run followed by the reading is within the field `mssp`**
  of `cNegMach` (`32886 · 2372500000 (m lg m + b² lg m)`) when the reduced lengths of the part
  are polynomially bounded, `1 + Σ_X ℓ ≤ m ^ e` with `e ≤ 10¹²`: the run of Klein's program is
  within `7308 · 2372500000 · m lg m` steps (`splitF_exec_read`, the bound of `splitF_exec`
  with `lg (18 m) ≤ 6 lg m`), and the reading within
  `rdCost b L M ≤ 38472 m + (12 e + 60) b² lg m` (`L = e lg m`, `M ≤ 9618 m`), which the term
  `b² lg m` of the field absorbs. The number of comparisons of the reading is
  `Θ(b² log Wc)`, and with only real comparisons the integer part of an answer below `Wc` needs
  `log₂ Wc` of them, so without a bound on the lengths the reading is not within the field.

**The interface** (`cNegMach_mssp_read_exec`): the one-face instance `fd` is the one of the run;
the caller gives an enumeration `β` of `B`, the **source indices** `σ s < fd.k` with
`fd.Q.tail (fd.g (σ s)) = fd.j (β s)` (the index of `β s` on the face of the instance, the same
data as the corner orders of step 3), the vertex numbers `ν s` with the potential `δ (β s)` at
`δb + ν s` (real memory), and a configuration holding Klein's answers at the pairs read
(`Klein.kOut … c (σ s) (σ t) = Klein.kOut … c' (σ s) (σ t)`, `c'` the end of Klein's run), with the
cut `Wc` of the instance in the real register `301` and `M`, `L` in the natural registers `310`,
`309` (`NegSSSP.RdIn`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine BKMNW Monge

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

/-! ### The output of the reading is the entry of `bfStartP` -/

lemma floor_div_two_pow (r : ℝ) (M : ℕ) : ⌊r⌋ / (2 : ℤ) ^ M = ⌊r / (2 : ℝ) ^ M⌋ := by
  have := Int.floor_div_natCast r (2 ^ M)
  push_cast at this
  exact this.symm

/-- **The output of `rdProg` for the pair `(s, t)` is the entry of `bfStartP`**: when the
lengths `H.len (β s) (β t)` are Klein's answer read back (`srcOut`), shifted by `d₁ - d₀`, the
nonnegative answers, and `d₀`, `d₁` the potentials read, the flag written is
`finB (arcOf H β) s t` and the value `matOf H β s t`. -/
theorem rdOut_child {R : Rd} {c c'' : Config} {H : DDG V} {β : ℕ → V} {s t nD n : ℕ} {Wc : ℤ}
    {d₀ d₁ : ℤ} (hRB : R.RBb = Klein.aRB n) (hOUT : R.OUTb = Klein.aOUT nD)
    (hW : R.Wr = Wc)
    (hlen : H.len (β s) (β t) =
      (Klein.srcOut Wc R.M (Klein.kOut nD n R.k c (R.σ s) (R.σ t))).map (· + (d₁ - d₀)))
    (hnn : ∀ z, Klein.srcOut Wc R.M (Klein.kOut nD n R.k c (R.σ s) (R.σ t)) = some z → 0 ≤ z)
    (hd₀ : c.rmem (R.δb + R.ν s) = d₀) (hd₁ : c.rmem (R.δb + R.ν t) = d₁)
    (hO : R.Out c c'' s t) :
    c''.nmem (R.Fb + (s * R.b + t)) = finB (arcOf H β) s t ∧
      c''.rmem (R.Lb + (s * R.b + t)) = (matOf H β s t : ℝ) := by
  obtain ⟨o1, o2, o3⟩ := hO
  have hk : Klein.kOut nD n R.k c (R.σ s) (R.σ t) =
      if c.nmem (R.RBb + R.ad s t) = 1 then some (c.rmem (R.OUTb + R.ad s t)) else none := by
    simp only [Klein.kOut, Rd.ad, hRB, hOUT, Nat.add_assoc]
  rw [hk] at hlen hnn
  unfold finB arcOf matOf
  rw [hlen]
  by_cases hf : c.nmem (R.RBb + R.ad s t) = 1
  · simp only [hf, ↓reduceIte] at hlen hnn ⊢
    set r := c.rmem (R.OUTb + R.ad s t) with hr
    have hsrc : Klein.srcOut Wc R.M (some r) =
        if ⌊r / (2 : ℝ) ^ R.M⌋ < Wc then some ⌊r / (2 : ℝ) ^ R.M⌋ else none := by
      simp only [Klein.srcOut, Klein.outNN, Option.map_some, Option.bind_some, Klein.cutW,
        floor_div_two_pow]
    rw [hsrc] at hnn ⊢
    by_cases hlt : r / (2 : ℝ) ^ R.M < Wc
    · have hA : R.A c s t := ⟨hf, by rw [hW]; exact hlt⟩
      have hfl : ⌊r / (2 : ℝ) ^ R.M⌋ < Wc := Int.floor_lt.2 hlt
      simp only [hfl, ↓reduceIte] at hnn ⊢
      have h0 : 0 ≤ r := by
        have := Int.floor_nonneg.1 (hnn _ rfl)
        have h2 : (0 : ℝ) < 2 ^ R.M := by positivity
        exact (div_nonneg_iff.1 this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 h2))
      refine ⟨by rw [o1, ite_eq_left_of_eq_true _ _ (eq_true hA)]; simp, ?_⟩
      rw [o3 hA h0, hd₀, hd₁]
      simp only [Option.map_some, Option.getD_some]
      push_cast; ring
    · have hA : ¬ R.A c s t := fun h => hlt (hW ▸ h.2)
      have hfl : ¬ ⌊r / (2 : ℝ) ^ R.M⌋ < Wc := fun h => hlt (Int.floor_lt.1 h)
      simp only [hfl, ↓reduceIte]
      refine ⟨by rw [o1, ite_eq_right_of_eq_false _ _ (eq_false hA)]; simp, ?_⟩
      rw [o2 hA]; simp
  · have hA : ¬ R.A c s t := fun h => hf h.1
    simp only [hf, ↓reduceIte]
    refine ⟨by rw [o1, ite_eq_right_of_eq_false _ _ (eq_false hA)]; simp [Klein.srcOut,
      Klein.outNN], ?_⟩
    rw [o2 hA]; simp [Klein.srcOut, Klein.outNN]

/-! ### Klein's run at a node, with a sharper count -/

lemma lg_eighteen_mul {m : ℕ} (hm : 1 ≤ m) : lg (18 * m) ≤ 6 * lg m := by
  have h1 : lg (18 * m) ≤ lg (m * 2 * 2 * 2 * 2 * 2) := lg_mono (by omega)
  have h2 : lg (m * 2 * 2 * 2 * 2 * 2) = lg m + 5 := by
    unfold lg
    rw [Nat.log_mul_base (by norm_num) (by omega), Nat.log_mul_base (by norm_num) (by omega),
      Nat.log_mul_base (by norm_num) (by omega), Nat.log_mul_base (by norm_num) (by omega),
      Nat.log_mul_base (by norm_num) (by omega)]
  have := one_le_lg m
  omega

lemma pow_le_two_pow_lg (m e : ℕ) : m ^ e ≤ 2 ^ (e * lg m) := by
  have h : m < 2 ^ lg m := Nat.lt_pow_succ_log_self (by norm_num) m
  calc m ^ e ≤ (2 ^ lg m) ^ e := Nat.pow_le_pow_left h.le e
    _ = 2 ^ (e * lg m) := by rw [← pow_mul, mul_comm]

/-- The cut of a one-face instance is at most `1 +` the total length of the part. -/
lemma srcW_le {P : Finset D} {B : Finset V} (fd : FaceData N P B) {ℓ : D → ℤ}
    (hnn : ∀ d ∈ P, 0 ≤ ℓ d) :
    Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) ≤ 1 + ∑ d ∈ P, ℓ d := by
  unfold Klein.srcW
  rw [sum_image fun x hx y hy hxy => fd.inst.injE hx hy hxy]
  have : ∑ d ∈ fd.P', faceLen fd.P' fd.e ℓ (fd.e d) = ∑ d ∈ fd.P', ℓ d :=
    sum_congr rfl fun d hd => faceLen_e fd.inst.injE (fun d' hd' => hnn d' (fd.inst.sub hd')) hd
  rw [this]
  have := sum_le_sum_of_subset_of_nonneg fd.inst.sub fun d hd _ => hnn d hd
  omega

/-- **Klein's program at a node**, as `splitF_exec`, with the sharper count
`7308 · 2372500000 · m lg m` (`lg (18 m) ≤ 6 lg m`), the darts of the instance with the sources
copied at most `9618 m`, and its cut at most `1 +` the total length of the part. -/
theorem splitF_exec_read {P P₀ P₁ : Finset D} (h : SplitF N P P₀ P₁)
    (hB : (bdry N P₀ P₁).Nonempty) {ℓ : D → ℤ} {X : Finset D} (hX : X = P₀ ∨ X = P₁)
    (hnn : ∀ d ∈ X, 0 ≤ ℓ d) :
    ∃ fd : FaceData N X (bdry N P₀ P₁), ∃ (n Bw : ℕ) (I : Input) (c₀ c' : Config) (steps : ℕ),
      Exec I (Bw + 16 * (n + 1))
        (Klein.kleinProg Bw (Fintype.card (Klein.SrcD fd.DQ fd.k)) n fd.k fd.k) c₀ c' steps ∧
      steps ≤ 7308 * 2372500000 * (P.card * lg P.card) ∧
      Fintype.card (Klein.SrcD fd.DQ fd.k) ≤ 9618 * P.card ∧
      Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) ≤ 1 + ∑ d ∈ X, ℓ d ∧
      (∀ b ∈ bdry N P₀ P₁, ∃ i < fd.k, fd.Q.tail (fd.g i) = fd.j b ∧
        ∀ b' ∈ bdry N P₀ P₁, ∃ i' < fd.k, fd.Q.tail (fd.g i') = fd.j b' ∧
          Klein.srcOut (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ))
            (Fintype.card (Klein.SrcD fd.DQ fd.k))
            (Klein.kOut (Fintype.card (Klein.SrcD fd.DQ fd.k)) n fd.k c' i i') =
          MSSP.odist (MSSP.pieceGraph N X ℓ) b b') ∧
      c'.output = c₀.output := by
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
  obtain ⟨n, Bw, I, c₀, c', steps, hE, hs, hR, hout⟩ := faceInst_exec hI hnn
  let fd : FaceData N X (bdry N P₀ P₁) := ⟨18 * P.card, k, DQ, VQ, FQ, Q, g, P', e, j, hI⟩
  refine ⟨fd, n, Bw, I, c₀, c', steps, hE, hs.trans ?_, ?_, srcW_le fd hnn, hR, hout⟩
  · have hl := lg_eighteen_mul hm
    have hkk : k ^ 2 * lg (18 * P.card) ≤ 1200 * P.card * (6 * lg P.card) := Nat.mul_le_mul hk hl
    have hqq : 18 * P.card * lg (18 * P.card) ≤ 18 * P.card * (6 * lg P.card) :=
      Nat.mul_le_mul_left _ hl
    have e1 : 7308 * 2372500000 * (P.card * lg P.card) = 2372500000 *
        (18 * P.card * (6 * lg P.card) + 1200 * P.card * (6 * lg P.card)) := by ring
    rw [e1]
    exact Nat.mul_le_mul_left _ (Nat.add_le_add hqq hkk)
  · have hcard := hI.card
    have hkk : k ≤ k ^ 2 := by nlinarith
    show Fintype.card (DQ ⊕ (Fin k × Klein.SrcKind)) ≤ 9618 * P.card
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
      show Fintype.card Klein.SrcKind = 8 from rfl]
    omega

/-! ### Klein's run and the reading within the field `mssp` -/

/-- **The two calls of multiple-source shortest paths at a node, with the reading of the
answers, within the field `mssp` of `cNegMach`**, for polynomially bounded reduced lengths
(`1 + Σ_X ℓ ≤ m ^ e`, `e ≤ 10¹²`): at a node meeting `SplitF` with shared vertices `B`, for the
part `X` with the reduced lengths `redLen N ℓ δ` (nonnegative), there are a one-face instance
`fd` and a run of `kleinProg` on it such that, for every enumeration `β` of `B` and every
configuration holding the answers of the run at the source indices `σ` of `β` (see the module
docstring for the interface), `rdProg` writes the flags `finB (arcOf H β)` and the lengths
`matOf H β` of the dense distance graph `H = childDDG N mssp X ℓ δ B` of the step in the
row-major layout of `bfStartP`, the two runs together within `cNegMach.mssp m b` steps. -/
theorem cNegMach_mssp_read_exec (C : ℕ) {P P₀ P₁ : Finset D} (h : SplitF N P P₀ P₁)
    (hB : (bdry N P₀ P₁).Nonempty) {ℓ : D → ℤ} {δ : V → ℤ} {X : Finset D}
    (hX : X = P₀ ∨ X = P₁) (hnn : ∀ d ∈ X, 0 ≤ redLen N ℓ δ d) {e : ℕ} (he : e ≤ 10 ^ 12)
    (hR : 1 + ∑ d ∈ X, redLen N ℓ δ d ≤ (P.card : ℤ) ^ e)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ} (hmssp : PieceMSSPSpec N mssp) :
    ∃ fd : FaceData N X (bdry N P₀ P₁), ∃ (n Bw : ℕ) (I : Input) (c₀ c' : Config) (steps : ℕ),
      Exec I (Bw + 16 * (n + 1))
        (Klein.kleinProg Bw (Fintype.card (Klein.SrcD fd.DQ fd.k)) n fd.k fd.k) c₀ c' steps ∧
      c'.output = c₀.output ∧
      ∀ (R : Rd) (β : ℕ → V) (W' : ℕ) (I' : Input) (c : Config),
        IsEnum R.b β (bdry N P₀ P₁) →
        (∀ s < R.b, R.σ s < fd.k ∧ fd.Q.tail (fd.g (R.σ s)) = fd.j (β s)) →
        R.k = fd.k → R.RBb = Klein.aRB n →
        R.OUTb = Klein.aOUT (Fintype.card (Klein.SrcD fd.DQ fd.k)) →
        R.M = Fintype.card (Klein.SrcD fd.DQ fd.k) →
        R.Wr = (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e (redLen N ℓ δ)) : ℝ) →
        R.L = e * lg P.card →
        RdLay R W' → WordsBounded W' c → RdIn R c →
        (∀ s < R.b, ∀ t < R.b,
          Klein.kOut (Fintype.card (Klein.SrcD fd.DQ fd.k)) n fd.k c (R.σ s) (R.σ t) =
            Klein.kOut (Fintype.card (Klein.SrcD fd.DQ fd.k)) n fd.k c' (R.σ s) (R.σ t)) →
        (∀ s < R.b, c.rmem (R.δb + R.ν s) = δ (β s)) →
        ∃ c'' k, Exec I' W' rdProg c c'' k ∧
          steps + k ≤ (cNegMach C).mssp P.card (bdry N P₀ P₁).card ∧
          ∀ s < R.b, ∀ t < R.b,
            c''.nmem (R.Fb + (s * R.b + t)) =
                finB (arcOf (childDDG N mssp X ℓ δ (bdry N P₀ P₁)) β) s t ∧
              c''.rmem (R.Lb + (s * R.b + t)) =
                (matOf (childDDG N mssp X ℓ δ (bdry N P₀ P₁)) β s t : ℝ) := by
  obtain ⟨fd, n, Bw, I, c₀, c', steps, hE, hs, hM, hWc, hK, hout⟩ :=
    splitF_exec_read (ℓ := redLen N ℓ δ) h hB hX hnn
  refine ⟨fd, n, Bw, I, c₀, c', steps, hE, hout, ?_⟩
  intro R β W' I' c hβ hσ hk hRB hOUT hMM hWr hLL hL hc hI hKc hδ
  set m := P.card with hmdef
  have hm : 1 ≤ m := by
    have := card_le_card (h.1 ▸ subset_union_left : P₀ ⊆ P); have := h.2.2.1; omega
  -- the cut is below `2 ^ L`
  have hWL : R.Wr ≤ (2 : ℝ) ^ R.L := by
    rw [hWr, hLL]
    have h1 := pow_le_two_pow_lg m e
    have h2 : Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e (redLen N ℓ δ)) ≤
        ((2 ^ (e * lg m) : ℕ) : ℤ) := by
      have : ((m ^ e : ℕ) : ℤ) ≤ ((2 ^ (e * lg m) : ℕ) : ℤ) := by exact_mod_cast h1
      push_cast at this ⊢
      exact hWc.trans (hR.trans this)
    have := (Int.cast_le (R := ℝ)).2 h2
    push_cast at this
    exact this
  obtain ⟨c'', k, hex, hkc, hO, -, -, -, -⟩ := rdProg_exec (P := I') hL hWL c hc hI
  have hb : R.b = (bdry N P₀ P₁).card := hβ.card
  refine ⟨c'', k, hex, ?_, fun s hs t ht => ?_⟩
  · -- the cost
    show steps + k ≤ 32886 * 2372500000 * (m * lg m + (bdry N P₀ P₁).card ^ 2 * lg m)
    rw [← hb]
    have hb1 : 1 ≤ R.b := by rw [hb]; exact card_pos.2 hB
    set Y := R.b ^ 2 * lg m with hY
    have hl1 := one_le_lg m
    have hY1 : lg m ≤ Y := Nat.le_mul_of_pos_left _ (by positivity)
    have hY2 : R.b * R.b ≤ Y := by
      rw [hY, ← sq]; exact Nat.le_mul_of_pos_right _ (by omega)
    have hbb : R.b ≤ R.b * R.b := Nat.le_mul_of_pos_left _ (by omega)
    have hmX : m ≤ m * lg m := Nat.le_mul_of_pos_right _ (by omega)
    have hL4 : R.L ≤ e * Y := by rw [hLL]; exact Nat.mul_le_mul_left _ hY1
    have hL8 : R.L * (R.b * R.b) = e * Y := by rw [hLL, hY]; ring
    have heY : e * Y ≤ 10 ^ 12 * Y := Nat.mul_le_mul_right _ he
    unfold rdCost at hkc
    have : (8 * R.L + 32) * (R.b * R.b) = 8 * (R.L * (R.b * R.b)) + 32 * (R.b * R.b) := by ring
    rw [this, hL8] at hkc
    rw [hMM] at hkc
    have hmY : 32886 * 2372500000 * (m * lg m + Y) =
        32886 * 2372500000 * (m * lg m) + 32886 * 2372500000 * Y := by ring
    rw [hmY]
    omega
  · -- the entries
    have hsB := hβ.mem s hs
    have htB := hβ.mem t ht
    obtain ⟨i, hi, hib, hK'⟩ := hK (β s) hsB
    obtain ⟨i', hi', hib', hK''⟩ := hK' (β t) htB
    have hii : i = R.σ s := fd.inst.cycle.inj i hi (R.σ s) (hσ s hs).1 (by rw [hib, (hσ s hs).2])
    have hii' : i' = R.σ t :=
      fd.inst.cycle.inj i' hi' (R.σ t) (hσ t ht).1 (by rw [hib', (hσ t ht).2])
    subst hii hii'
    have hnn' : ∀ a, 0 ≤ (MSSP.pieceGraph N X (redLen N ℓ δ)).len a := fun a => hnn a.1 a.2
    have hms : mssp X (redLen N ℓ δ) (bdry N P₀ P₁) (β s) (β t) =
        MSSP.odist (MSSP.pieceGraph N X (redLen N ℓ δ)) (β s) (β t) := by
      have := odist_eq_of_isDist hnn' (hmssp X (redLen N ℓ δ) (bdry N P₀ P₁) hnn (β s) hsB)
      exact congrFun this (β t)
    have hA : Klein.srcOut (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e (redLen N ℓ δ)))
        R.M (Klein.kOut (Fintype.card (Klein.SrcD fd.DQ fd.k)) n R.k c (R.σ s) (R.σ t)) =
        MSSP.odist (MSSP.pieceGraph N X (redLen N ℓ δ)) (β s) (β t) := by
      rw [hk, hKc s hs t ht, hMM]; exact hK''
    refine rdOut_child (Wc := Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e (redLen N ℓ δ)))
      hRB hOUT hWr ?_ ?_ (hδ s hs) (hδ t ht) (hO s hs t ht)
    · show (mssp X (redLen N ℓ δ) (bdry N P₀ P₁) (β s) (β t)).map (· + (δ (β t) - δ (β s))) = _
      rw [hms, hA]
    · intro z hz
      rw [hA] at hz
      unfold MSSP.odist at hz
      split_ifs at hz with hr
      · cases hz; exact MSSP.dist_nonneg hnn' hr

end NegSSSP

end PlanarFlow
