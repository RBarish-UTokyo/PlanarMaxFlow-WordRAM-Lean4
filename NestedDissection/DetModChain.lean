module

public import NestedDissection.DetModSigns

/-!
# Chaining the programs: listed entries to the determinant modulo a prime

The output of `DetMod.build` is a valid input of `DetMod.detMod` (`DetMod.bout_denc`), and the
matrix it encodes is the matrix of the listed entries (`DetMod.inMat_bout`). When the listed
pairs `{u_k, v_k}` are proper and pairwise distinct, that matrix has `sgn s_k` at `(u_k, v_k)`,
`-sgn s_k` at `(v_k, u_k)` and `0` elsewhere (`DetMod.listed_bout`), with `sgn 0 = 1` and
`sgn s = -1` otherwise. Running `build` and then `detMod` on its output prints the determinant of
that matrix (`DetMod.build_detMod`). The output of `DetMod.signs` is a valid input of `build`
(`DetMod.sout_benc`), so `signs`, `build` and `detMod` in turn print the determinant of the
matrix of the listed entries with signs from a bit and two parities, within
`O(m + n³ + n log p)` steps in all (`DetMod.signs_build_detMod`).

A run of one program and then of the next on its output is stated as the conjunction of the two
`RunsWithin` statements, the first printing exactly the input of the second.
-/

@[expose] public section

namespace NestedDissection

namespace DetMod

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### Signs and matrices of listed entries -/

/-- The sign `1` for `0` and `-1` otherwise, in `ZMod p`. -/
def sgn (p s : ℕ) : ZMod p := if s = 0 then 1 else -1

@[simp] theorem sgn_zero (p : ℕ) : sgn p 0 = 1 := rfl
@[simp] theorem sgn_one (p : ℕ) : sgn p 1 = -1 := rfl

/-- The listed pairs `(u k, v k)`, `k < m`, are proper and pairwise distinct as unordered
pairs. -/
def Simple (m : ℕ) (u v : ℕ → ℕ) : Prop :=
  (∀ k < m, u k ≠ v k) ∧
    ∀ k < m, ∀ k' < m, k ≠ k' → ¬ (u k = u k' ∧ v k = v k') ∧ ¬ (u k = v k' ∧ v k = u k')

/-- `M` is the skew matrix of the listed entries: `sgn (s k)` at `(u k, v k)`, `-sgn (s k)` at
`(v k, u k)`, and `0` at every position that is not listed. -/
structure Listed {n p : ℕ} (m : ℕ) (u v s : ℕ → ℕ) (M : Matrix (Fin n) (Fin n) (ZMod p)) :
    Prop where
  fwd : ∀ k < m, ∀ i j : Fin n, (i : ℕ) = u k → (j : ℕ) = v k → M i j = sgn p (s k)
  bwd : ∀ k < m, ∀ i j : Fin n, (i : ℕ) = v k → (j : ℕ) = u k → M i j = - sgn p (s k)
  zero : ∀ i j : Fin n, (∀ k < m, ¬ ((i : ℕ) = u k ∧ (j : ℕ) = v k) ∧
    ¬ ((i : ℕ) = v k ∧ (j : ℕ) = u k)) → M i j = 0

/-- The matrix of the listed entries is unique. -/
theorem Listed.eq {n p m : ℕ} {u v s : ℕ → ℕ} {M M' : Matrix (Fin n) (Fin n) (ZMod p)}
    (h : Listed m u v s M) (h' : Listed m u v s M') : M = M' := by
  ext i j
  by_cases hf : ∃ k < m, (i : ℕ) = u k ∧ (j : ℕ) = v k
  · obtain ⟨k, hk, hi, hj⟩ := hf
    rw [h.fwd k hk i j hi hj, h'.fwd k hk i j hi hj]
  by_cases hb : ∃ k < m, (i : ℕ) = v k ∧ (j : ℕ) = u k
  · obtain ⟨k, hk, hi, hj⟩ := hb
    rw [h.bwd k hk i j hi hj, h'.bwd k hk i j hi hj]
  have hz : ∀ k < m, ¬ ((i : ℕ) = u k ∧ (j : ℕ) = v k) ∧ ¬ ((i : ℕ) = v k ∧ (j : ℕ) = u k) :=
    fun k hk => ⟨fun e => hf ⟨k, hk, e⟩, fun e => hb ⟨k, hk, e⟩⟩
  rw [h.zero i j hz, h'.zero i j hz]

/-- `Listed` only reads the listed entries. -/
theorem Listed.congr {n p m : ℕ} {u v s u' v' s' : ℕ → ℕ} {M : Matrix (Fin n) (Fin n) (ZMod p)}
    (h : Listed m u v s M) (hu : ∀ k < m, u' k = u k) (hv : ∀ k < m, v' k = v k)
    (hs : ∀ k < m, s' k = s k) : Listed m u' v' s' M := by
  refine ⟨fun k hk i j hi hj => ?_, fun k hk i j hi hj => ?_, fun i j hz => h.zero i j ?_⟩
  · rw [hs k hk]; exact h.fwd k hk i j (by rw [hi, hu k hk]) (by rw [hj, hv k hk])
  · rw [hs k hk]; exact h.bwd k hk i j (by rw [hi, hv k hk]) (by rw [hj, hu k hk])
  · intro k hk; rw [← hu k hk, ← hv k hk]; exact hz k hk

theorem Simple.congr {m : ℕ} {u v u' v' : ℕ → ℕ} (h : Simple m u v) (hu : ∀ k < m, u' k = u k)
    (hv : ∀ k < m, v' k = v k) : Simple m u' v' := by
  refine ⟨fun k hk => ?_, fun k hk k' hk' hne => ?_⟩
  · rw [hu k hk, hv k hk]; exact h.1 k hk
  · rw [hu k hk, hv k hk, hu k' hk', hv k' hk']; exact h.2 k hk k' hk' hne

/-! ### The output of `build` as an input of `detMod` -/

section build
variable {d : List ℕ} {W : ℕ}

theorem dim_bout (d : List ℕ) : dim (bout d) = dim d := rfl
theorem prm_bout (d : List ℕ) : prm (bout d) = prm d := rfl
theorem detCost_bout (d : List ℕ) : detCost (bout d) = detCost d := rfl

theorem ent_bout {t : ℕ} (ht : t < dim d * dim d) : ent (bout d) t = bmat d t := by
  simp [ent, bout, ht]

theorem getD_bout (i : ℕ) : (bout d).getD (i + 2) 0 =
    if i < dim d * dim d then bmat d i else 0 := by
  split_ifs with h
  · exact ent_bout h
  · simp [bout, h]

/-- **The output of `build` is a valid input of `detMod`.** -/
theorem bout_denc (he : BEnc d W) : DEnc (bout d) W := by
  have hp := he.prime.two_le
  refine ⟨he.prime, fun i => ?_, he.sq, he.dim_sq⟩
  rcases i with _ | _ | i
  · exact he.word_le 0
  · exact he.word_le 1
  · rw [getD_bout]
    split_ifs
    · have := bmem_lt he (bm d) i; unfold bmat; nlinarith [he.sq]
    · exact Nat.zero_le _

/-- **The matrix of the output of `build`** is the matrix of the listed entries, read in
`ZMod p`. -/
theorem inMat_bout (d : List ℕ) :
    inMat (bout d) = fun i j : Fin (dim d) => (bmat d (i * dim d + j) : ZMod (prm d)) := by
  ext i j
  exact congrArg (fun x : ℕ => (x : ZMod (prm d))) (ent_bout (d := d) (idx_lt i.2 j.2))

theorem sres_cast {p s : ℕ} (hp : 1 ≤ p) : (sres p s : ZMod p) = sgn p s := by
  unfold sres sgn
  split_ifs
  · simp
  · rw [Nat.cast_sub hp, ZMod.natCast_self]; simp

theorem sres_neg_cast {p s : ℕ} (hp : 1 ≤ p) :
    (((p - sres p s) % p : ℕ) : ZMod p) = - sgn p s := by
  have : sres p s ≤ p := by unfold sres; split_ifs <;> omega
  rw [ZMod.natCast_mod, Nat.cast_sub this, ZMod.natCast_self, sres_cast hp, zero_sub]

theorem bmem_fwd (he : BEnc d W) (hs : Simple (bm d) (bu d) (bv d)) {K k : ℕ} (hK : K ≤ bm d)
    (hk : k < K) : bmem d K (bu d k * dim d + bv d k) = sres (prm d) (bs d k) := by
  induction K with
  | zero => omega
  | succ K ih =>
    have hkm : k < bm d := by omega
    obtain ⟨huk, hvk⟩ := he.ent_lt k hkm
    obtain ⟨huK, hvK⟩ := he.ent_lt K (by omega)
    unfold bmem
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · have hd := hs.2 k hkm K (by omega) (by omega)
      rw [iteN fun e => hd.2 (idx_inj hvk huK e), iteN fun e => hd.1 (idx_inj hvk hvK e),
        ih (by omega) hk]
    · rw [iteN fun e => hs.1 k hkm (idx_inj hvk huk e).1, iteP rfl]

theorem bmem_bwd (he : BEnc d W) (hs : Simple (bm d) (bu d) (bv d)) {K k : ℕ} (hK : K ≤ bm d)
    (hk : k < K) :
    bmem d K (bv d k * dim d + bu d k) = (prm d - sres (prm d) (bs d k)) % prm d := by
  induction K with
  | zero => omega
  | succ K ih =>
    have hkm : k < bm d := by omega
    obtain ⟨huk, hvk⟩ := he.ent_lt k hkm
    obtain ⟨huK, hvK⟩ := he.ent_lt K (by omega)
    unfold bmem
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · have hd := hs.2 k hkm K (by omega) (by omega)
      have e1 := fun e => hd.1 (And.symm (idx_inj (n := dim d) huk huK e))
      have e2 := fun e => hd.2 (And.symm (idx_inj (n := dim d) huk hvK e))
      rw [iteN e1, iteN e2, ih (by omega) hk]
    · rw [iteP rfl]

theorem bmem_zero (he : BEnc d W) {K i j : ℕ} (hK : K ≤ bm d) (hj : j < dim d)
    (hz : ∀ k < K, ¬ (i = bu d k ∧ j = bv d k) ∧ ¬ (i = bv d k ∧ j = bu d k)) :
    bmem d K (i * dim d + j) = 0 := by
  induction K with
  | zero => rfl
  | succ K ih =>
    obtain ⟨huK, hvK⟩ := he.ent_lt K (by omega)
    unfold bmem
    rw [iteN fun e => (hz K (by omega)).2 (idx_inj hj huK e),
      iteN fun e => (hz K (by omega)).1 (idx_inj hj hvK e),
      ih (by omega) fun k hk => hz k (by omega)]

/-- **The matrix of the output of `build`, entry by entry**: for proper, pairwise distinct
listed pairs, it is the skew matrix of the listed entries. -/
theorem listed_bout (he : BEnc d W) (hs : Simple (bm d) (bu d) (bv d)) :
    Listed (n := dim d) (p := prm d) (bm d) (bu d) (bv d) (bs d) (inMat (bout d)) := by
  have hp : 1 ≤ prm d := he.prime.one_lt.le
  rw [inMat_bout]
  refine ⟨fun k hk i j hi hj => ?_, fun k hk i j hi hj => ?_, fun i j hz => ?_⟩
  · show (bmat d (i * dim d + j) : ZMod (prm d)) = _
    rw [hi, hj, bmat, bmem_fwd he hs le_rfl hk, sres_cast hp]
  · show (bmat d (i * dim d + j) : ZMod (prm d)) = _
    rw [hi, hj, bmat, bmem_bwd he hs le_rfl hk, sres_neg_cast hp]
  · show (bmat d (i * dim d + j) : ZMod (prm d)) = _
    rw [bmat, bmem_zero he le_rfl j.2 hz, Nat.cast_zero]

/-- **`build`, then `detMod`.** The first program prints the input of the second, which prints
the determinant of the matrix of the listed entries modulo `p`; the two runs take at most
`9 n² + 22 m + 21` and `detCost + 1` steps. -/
theorem build_detMod (he : BEnc d W) :
    RunsWithin (compile build 0 ++ [Instr.halt]) (inp d) W (9 * (dim d * dim d) + 22 * bm d + 21)
      (bout d) ∧
    RunsWithin (compile detMod 0 ++ [Instr.halt]) (inp (bout d)) W (detCost d + 1)
      [(Matrix.of fun i j : Fin (dim d) => (bmat d (i * dim d + j) : ZMod (prm d))).det.val] := by
  refine ⟨build_runsWithin he, ?_⟩
  have h := detMod_runsWithin (bout_denc he)
  rw [inMat_bout] at h
  exact h

/-- **`build`, then `detMod`, for proper and pairwise distinct listed pairs**: the output is the
determinant modulo `p` of the skew matrix with entries `±1` of the listed entries. -/
theorem build_detMod_listed (he : BEnc d W) (hs : Simple (bm d) (bu d) (bv d))
    {M : Matrix (Fin (dim d)) (Fin (dim d)) (ZMod (prm d))}
    (hM : Listed (bm d) (bu d) (bv d) (bs d) M) :
    RunsWithin (compile build 0 ++ [Instr.halt]) (inp d) W (9 * (dim d * dim d) + 22 * bm d + 21)
      (bout d) ∧
    RunsWithin (compile detMod 0 ++ [Instr.halt]) (inp (bout d)) W (detCost d + 1)
      [M.det.val] := by
  refine ⟨build_runsWithin he, ?_⟩
  have h := detMod_runsWithin (bout_denc he)
  rwa [(listed_bout he hs).eq hM] at h

end build

/-! ### The output of `signs` as an input of `build` -/

/-- Inputs of `signs` whose output is a valid input of `build`. -/
structure SFull (d : List ℕ) (W : ℕ) : Prop extends SEnc d W where
  prime : (prm d).Prime
  ent_lt : ∀ k < bm d, su d k < dim d ∧ sv d k < dim d
  dim_sq : dim d * dim d + 2 ≤ W
  sq : prm d * prm d + prm d ≤ W

section signs
variable {d : List ℕ} {W : ℕ}

theorem dim_sout (d : List ℕ) : dim (sout d) = dim d := rfl
theorem prm_sout (d : List ℕ) : prm (sout d) = prm d := rfl
theorem bm_sout (d : List ℕ) : bm (sout d) = bm d := rfl

theorem getD_sout (t : ℕ) : (sout d).getD (t + 3) 0 =
    if t < 3 * bm d then sword d t else 0 := by
  split_ifs with h <;> simp [sout, h]

theorem bu_sout {k : ℕ} (hk : k < bm d) : bu (sout d) k = su d k := by
  have h := getD_sout (d := d) (3 * k)
  rw [iteP (by omega)] at h
  unfold bu; rw [show 3 + 3 * k = 3 * k + 3 by ring, h, sword, iteP (by omega)]
  congr 1; omega

theorem bv_sout {k : ℕ} (hk : k < bm d) : bv (sout d) k = sv d k := by
  have h := getD_sout (d := d) (3 * k + 1)
  rw [iteP (by omega)] at h
  unfold bv; rw [show 4 + 3 * k = 3 * k + 1 + 3 by ring, h, sword, iteN (by omega), iteP (by omega)]
  congr 1; omega

theorem bs_sout {k : ℕ} (hk : k < bm d) : bs (sout d) k = ss d k := by
  have h := getD_sout (d := d) (3 * k + 2)
  rw [iteP (by omega)] at h
  unfold bs; rw [show 5 + 3 * k = 3 * k + 2 + 3 by ring, h, sword, iteN (by omega), iteN (by omega)]
  congr 1; omega

/-- **The output of `signs` is a valid input of `build`.** -/
theorem sout_benc (hf : SFull d W) : BEnc (sout d) W := by
  have hW := hf.size
  refine ⟨hf.prime, fun i => ?_, hf.dim_sq, fun k hk => ?_, by rw [bm_sout]; omega, hf.sq⟩
  · rcases i with _ | _ | _ | t
    · exact hf.word_le 0
    · exact hf.word_le 1
    · exact hf.word_le 2
    · rw [getD_sout]
      split_ifs
      · unfold sword
        split_ifs
        · exact hf.word_le _
        · exact hf.word_le _
        · have : ss d (t / 3) < 2 := Nat.mod_lt _ (by omega)
          omega
      · exact Nat.zero_le _
  · rw [bm_sout] at hk
    rw [bu_sout hk, bv_sout hk]; exact hf.ent_lt k hk

/-- **`signs`, then `build`, then `detMod`.** On an input `[n, p, m, S, (u_k, v_k, i_k, j_k)*,
a_0, …, b_0, …]` with proper, pairwise distinct pairs `{u_k, v_k}`, each program prints the input
of the next, and the last prints `det M mod p` for the skew matrix `M` with `sgn s_k` at
`(u_k, v_k)`, `-sgn s_k` at `(v_k, u_k)` and `0` elsewhere, where
`s_k = (a_{i_k} + 1 + b_{i_k} + b_{j_k}) mod 2`. The runs take at most `28 m + 18`,
`9 n² + 22 m + 21` and `detCost + 1` steps (`O(m + n³ + n log p)` in all,
`DetMod.signs_build_detMod_cost`). -/
theorem signs_build_detMod (hf : SFull d W) (hs : Simple (bm d) (su d) (sv d))
    {M : Matrix (Fin (dim d)) (Fin (dim d)) (ZMod (prm d))}
    (hM : Listed (bm d) (su d) (sv d) (ss d) M) :
    RunsWithin (compile signs 0 ++ [Instr.halt]) (inp d) W (28 * bm d + 18) (sout d) ∧
    RunsWithin (compile build 0 ++ [Instr.halt]) (inp (sout d)) W
      (9 * (dim d * dim d) + 22 * bm d + 21) (bout (sout d)) ∧
    RunsWithin (compile detMod 0 ++ [Instr.halt]) (inp (bout (sout d))) W (detCost d + 1)
      [M.det.val] := by
  have hb := sout_benc hf
  have hs' : Simple (bm (sout d)) (bu (sout d)) (bv (sout d)) :=
    hs.congr (fun k hk => bu_sout hk) (fun k hk => bv_sout hk)
  have hM' : Listed (bm (sout d)) (bu (sout d)) (bv (sout d)) (bs (sout d)) M :=
    hM.congr (fun k hk => bu_sout hk) (fun k hk => bv_sout hk) (fun k hk => bs_sout hk)
  exact ⟨signs_runsWithin hf.toSEnc, build_detMod_listed hb hs' hM'⟩

/-- The matrix of `signs_build_detMod` exists: it is the matrix encoded by `build`'s output. -/
theorem listed_sout (hf : SFull d W) (hs : Simple (bm d) (su d) (sv d)) :
    Listed (n := dim d) (p := prm d) (bm d) (su d) (sv d) (ss d) (inMat (bout (sout d))) :=
  (listed_bout (sout_benc hf) (hs.congr (fun _ hk => bu_sout hk) (fun _ hk => bv_sout hk))).congr
    (fun _ hk => (bu_sout (d := d) hk).symm) (fun _ hk => (bv_sout (d := d) hk).symm)
    (fun _ hk => (bs_sout (d := d) hk).symm)

/-- The total step bound of `signs`, `build` and `detMod`: `O(m + n³ + n log p)`. -/
theorem signs_build_detMod_cost (d : List ℕ) :
    (28 * bm d + 18) + (9 * (dim d * dim d) + 22 * bm d + 21) + (detCost d + 1) ≤
      50 * bm d + 11 * dim d ^ 3 + 46 * dim d ^ 2 + 12 * dim d * Nat.log 2 (prm d) +
        62 * dim d + 56 := by
  have h := Nat.mul_le_mul_left (dim d) (colCost_le d)
  unfold detCost
  have e : dim d * (11 * dim d * dim d + 30 * dim d + 12 * Nat.log 2 (prm d) + 62) =
      11 * dim d ^ 3 + 30 * dim d ^ 2 + 12 * dim d * Nat.log 2 (prm d) + 62 * dim d := by ring
  have e2 : 7 * dim d * dim d = 7 * dim d ^ 2 := by ring
  have e3 : dim d * dim d = dim d ^ 2 := by ring
  omega

end signs

end DetMod

end NestedDissection
