module

public import PlanarFlow.BKMNW.Nf7dI
public import PlanarFlow.BKMNW.Nf7dJ

/-!
# `fixP7` at a node call: the glue and the value bounds

* **`rtL_le_mul`**: lengths bounded by `B` give `rtL N ℓ ≤ #D · B` (`exists_minLen`);
* **`fpB_mono`**, **`callIn_AS_le`** (`AS ≤ m Z` from the frame), **`SPath.k_le_card'`**
  (`k ≤ #darts`), **`SPath.one_le_faces`** (`1 ≤ #faces` when `0 < k`);
* **`fx7f_lenK`**: at a plane piece map, for capacities `U ≥ 0` and a pseudoflow `f₀`, after
  `n ≤ k` stages of `fixPath` the lengths `U − s.1` are bounded by `16 fpB AS m k` (the `K` of the
  prologue); **`fx7f_rtL`**: hence `rtL (U − s.1) ≤ m · K`;
* **`fx7f_call`**: at a node call meeting `CallOk`, with a part `πj = L[j]`: the piece map is plane
  with transitive rotations and faces, its darts are nonempty, `j < #segs`, `πj.k = segs[j].k`
  and the darts of `πj` are those of `segs[j]`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit CombMap OrbLab NegSSSP NegSSSP.Frame MfDrv NsStep SPath
  WordRAM WordRAM.Machine WordRAM.Programs

universe w'

/-- **`rtL` of lengths bounded by `B`** is at most `#D · B`. -/
theorem rtL_le_mul {D' V' F' : Type w'} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
    [Fintype F'] [DecidableEq F'] (N : CombMap D' V' F') (ℓ : D' → ℤ) {B : ℕ}
    (hB : ∀ y, |ℓ y| ≤ B) : rtL N ℓ ≤ Fintype.card D' * B := by
  have h : ∑ y, |minLen N.dual ℓ y| ≤ ∑ _y : D', (B : ℤ) := sum_le_sum fun y _ => by
    obtain ⟨z, -, -, e⟩ := exists_minLen (N := N.dual) ℓ y
    rw [e]; exact hB z
  rw [sum_const, card_univ, nsmul_eq_mul] at h
  unfold rtL
  exact Int.toNat_le.2 (by push_cast; exact h)

/-- `fpB` is monotone. -/
lemma fpB_mono {A A' m m' k k' : ℕ} (hA : A ≤ A') (hm : m ≤ m') (hk : k ≤ k') :
    fpB A m k ≤ fpB A' m' k' := by
  unfold fpB; gcongr

/-- **A path has at most `#D` darts.** -/
lemma SPath.k_le_card' {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V']
    [DecidableEq V'] [Fintype F'] [DecidableEq F'] {N : CombMap D' V' F'} (P : SPath N) :
    P.k ≤ Fintype.card D' := by
  have := card_le_card_of_injOn P.d (s := range P.k) (t := univ)
    (fun _ _ => mem_coe.2 (mem_univ _))
    (fun i hi j hj e => P.d_inj (mem_range.1 hi) (mem_range.1 hj) e)
  simpa using this

/-- **A nonempty path has a face.** -/
lemma SPath.one_le_faces {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V']
    [DecidableEq V'] [Fintype F'] [DecidableEq F'] {N : CombMap D' V' F'} (P : SPath N)
    (hk : 0 < P.k) : 1 ≤ P.faces.card :=
  Finset.card_pos.2 ⟨_, P.face_mem (P.d_mem 0 hk)⟩

section Call

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {x : MCall M} {m : ℕ} {en : ℕ → D}
  {d : ℕ} {mem : ℕ → ℕ}

/-- **The sum of the capacities is at most `m Z`.** -/
theorem callIn_AS_le (hl : Lay M gid u S T Z x m en d mem) (Gb : ℕ) (π : HSep M) (j : ℕ) :
    (callIn d m Gb π j Z mem).AS ≤ m * Z := by
  have h : ∀ i ∈ range m, (callIn d m Gb π j Z mem).CP i ≤ Z := fun i hi => by
    have := (hl.cp i (mem_range.1 hi)).2
    simp only [FpIn.CP, callIn]
    rw [show d + 4 + m + m + m + i = d + 4 + 3 * m + i by omega]; exact this
  calc (callIn d m Gb π j Z mem).AS = ∑ i ∈ range m, (callIn d m Gb π j Z mem).CP i := rfl
    _ ≤ ∑ _i ∈ range m, Z := sum_le_sum h
    _ = m * Z := by rw [sum_const, card_range, smul_eq_mul]

/-- The capacities of a frame are nonnegative. -/
lemma lay_u_nonneg (hl : Lay M gid u S T Z x m en d mem) :
    ∀ e : SDart (pdarts M x.1.piece x.2.1), 0 ≤ u e.1 := fun e => by
  obtain ⟨i, hi, he⟩ := hl.en_surj e.1 e.2
  rw [← he, ← (hl.cp i hi).1]; positivity

set_option maxHeartbeats 4000000 in
/-- **The lengths of `fixPath` after `n ≤ k` stages are bounded by `16 fpB AS m k`.** -/
theorem fx7f_lenK (hP : PieceInv M x.1.piece x.2.1 x.2.2)
    (hpl : (pmap hP).IsPlane) (hrot : (pmap hP).RotTrans) (hface : (pmap hP).FaceTrans)
    (hl : Lay M gid u S T Z x m en d mem) {πj : SPath (pmap hP)}
    {f₀ : SDart (pdarts M x.1.piece x.2.1) → ℤ}
    (hf₀ : IsPseudo (pmap hP) (fun y => u y.1) f₀) {AS k K : ℕ}
    (hAS : ((AS : ℕ) : ℤ) = SPath.absSum (fun y : SDart (pdarts M x.1.piece x.2.1) => u y.1))
    (hkk : πj.k ≤ k) (hK : 16 * fpB AS m k ≤ K) {n : ℕ} (hn : n ≤ πj.k) (e) :
    |u e.1 - (fpState (pmap hP) (fun y => u y.1) f₀ πj (Klein.msspPlaneK (pmap hP)) (frRef _)
      n).1 e| ≤ (K : ℤ) := by
  have hmssp : MSSPSpecAt (pmap hP) (Klein.msspPlaneK (pmap hP)) πj :=
    fun ℓ' hnn' y hy => Klein.msspPlaneK_spec hpl hrot hface πj ℓ' hnn' y hy
  have hc0 := lay_u_nonneg hl
  have hinv := fixPath_invB hpl hc0 hf₀ hmssp (frRef_spec _) n hn
  have h1 := hinv.len_bound hc0 hf₀ e
  have hcard : Fintype.card (SDart (pdarts M x.1.piece x.2.1)) = m := hl.card_sdart
  have eB : Bst (SDart (pdarts M x.1.piece x.2.1)) (fun y => u y.1) =
      2 * ((AS : ℤ) + (m : ℤ) * (4 * AS + 1)) := by
    unfold Bst; rw [hcard, ← hAS]
  rw [eB, ← hAS] at h1
  simp only [Pi.sub_apply] at h1
  have hAS0 : (0 : ℤ) ≤ AS := by positivity
  have hX : (0 : ℤ) ≤ 2 * ((AS : ℤ) + (m : ℤ) * (4 * AS + 1)) := by positivity
  have hnk : (n : ℤ) ≤ k := by exact_mod_cast hn.trans hkk
  have h2 : (n : ℤ) * (2 * ((AS : ℤ) + (m : ℤ) * (4 * AS + 1))) ≤
      (k : ℤ) * (2 * ((AS : ℤ) + (m : ℤ) * (4 * AS + 1))) := mul_le_mul_of_nonneg_right hnk hX
  have hKe : ((16 * fpB AS m k : ℕ) : ℤ) =
      16 * (((k : ℤ) + 2) * (2 * ((AS : ℤ) + (m : ℤ) * (4 * AS + 1))) + 12 * AS + 4) := by
    unfold fpB; push_cast; ring
  have hK' : ((16 * fpB AS m k : ℕ) : ℤ) ≤ K := by exact_mod_cast hK
  rw [hKe] at hK'
  linarith

/-- **`rtL` of the lengths of `fixPath` after `n ≤ k` stages is at most `m · K`.** -/
theorem fx7f_rtL (hP : PieceInv M x.1.piece x.2.1 x.2.2)
    (hpl : (pmap hP).IsPlane) (hrot : (pmap hP).RotTrans) (hface : (pmap hP).FaceTrans)
    (hl : Lay M gid u S T Z x m en d mem) {πj : SPath (pmap hP)}
    {f₀ : SDart (pdarts M x.1.piece x.2.1) → ℤ}
    (hf₀ : IsPseudo (pmap hP) (fun y => u y.1) f₀) {AS k K : ℕ}
    (hAS : ((AS : ℕ) : ℤ) = SPath.absSum (fun y : SDart (pdarts M x.1.piece x.2.1) => u y.1))
    (hkk : πj.k ≤ k) (hK : 16 * fpB AS m k ≤ K) {n : ℕ} (hn : n ≤ πj.k) :
    rtL (pmap hP) (fun y => u y.1 - (fpState (pmap hP) (fun y => u y.1) f₀ πj
      (Klein.msspPlaneK (pmap hP)) (frRef _) n).1 y) ≤ m * K := by
  have := rtL_le_mul (pmap hP) _ (B := K)
    (fun e => fx7f_lenK hP hpl hrot hface hl hf₀ hAS hkk hK hn e)
  rwa [hl.card_sdart] at this

/-- **The node-call glue**: at a node call meeting `CallOk`, with a part `πj` of the separator in
the piece map. -/
theorem fx7f_call {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D}
    (h : SCond M l r π Hs σ) (hok : CallOk M S T (.node l r π, Hs, σ)) {j : ℕ}
    {πj : SPath (pmap h.1)} (hj : (segsP h.1 π.segs h.2)[j]? = some πj) :
    (pmap h.1).IsPlane ∧ (pmap h.1).RotTrans ∧ (pmap h.1).FaceTrans ∧
      (pdarts M (l.piece ∪ r.piece) Hs).Nonempty ∧
      ∃ hj' : j < π.segs.length, πj.k = (π.segs[j]).k ∧
        ∀ l < πj.k, (πj.d l).1 = (π.segs[j]).d l := by
  obtain ⟨y, -⟩ := Quotient.exists_rep (πj.p 0)
  have hcon : HConn M (l.piece ∪ r.piece) Hs := ADec.PGood.hConn hok.2.2.1
  obtain ⟨hpl, hrot, hface⟩ := h.1.isPlane hcon y.2
  obtain ⟨hj', h1, h2⟩ := segsP_get h.1 π.segs h.2 j πj hj
  exact ⟨hpl, hrot, hface, ⟨y.1, y.2⟩, hj', h1, h2⟩

end Call

end BKMNW

end PlanarFlow
