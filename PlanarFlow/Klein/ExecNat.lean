module

public import PlanarFlow.Klein.ProgKleinMC
public import PlanarFlow.Klein.ModNat
public import PlanarFlow.Klein.ProgExistsMask

/-!
# Klein's masked program on natural words only

The machine of `WordRAM/Spec.lean` has exact real registers. Klein's masked program
`kleinProgM` uses no `divR` and names registers `< 201` (`kleinProgM_noDivR`,
`kleinProgM_regsOK`), and every real comparison of every run is within `Hc ≥ kleinHI`
(`kleinProgM_cmpOK`); its starting configuration holds integers only (`klein_exec_pre`). So the
simulation of `WordRAM/Machine/RealsModNat.lean` runs it **on natural words**: each real is kept
modulo `Mo = 2 Hc + 1` in a natural register or a natural memory cell, a comparison is decided
on the residue of the difference.

* `natOnly s`: `s` has no real instruction and no real test; `compile_natOnly`: then its
  compiled flat program has no real instruction (`Instr.isReal`).
* `resW`, `natCfg R W M β c`: the natural-word configuration holding the natural part of `c`
  and the residues modulo `M` of its (integer) reals, with real registers and memory `0`;
  `sim_natCfg`, `wb_natCfg`: it simulates `c` and is bounded.
* `kleinProgMN B nD n k t Hc`: the constants `Mo`, `Hc`, `β` into their registers, then the
  translation `ModNat.toNat 201 Mo kleinProgM`; `kleinProgMN_natOnly`: **it is a natural-word
  program** (checked by the kernel). `kleinWN B n Hc`: its word bound
  `2 W + 1 + Mo² + Mo`, `W = B + 16 (n + 1)` the word bound of the real program.
* `kOutN`: an answer read from the natural words (the reach bit and the natural word holding the
  residue of the distance); `kOutN_of_sim`: it is the real answer when that is an integer in
  `[0, Mo)`.
* `dist_le_sum_len`: a distance with nonnegative lengths is at most the sum of all lengths.
* `kleinM_exec_exists_nat`: **Klein's masked program end to end on natural words**: the
  statement of `kleinM_exec_exists` for `kleinProgMN` run from `natCfg`, within
  `4 · 36500000 (N lg N + f t lg N) + 3` steps, with words at most `kleinWN`, and
  `kleinHI ≤ Hc < kleinHI + 1` (`kleinHI_le`: polynomial in the size of the map and the
  largest length); the answers of the flagged moves are read **exactly** from the natural words
  (`kOutN`), for all lengths: no hypothesis on their size.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt

/-! ### Programs without reals -/

/-- No real instruction and no real test. -/
def natOnly : Stmt → Bool
  | .skip => true
  | .instr i => !i.isReal
  | .seq s t => natOnly s && natOnly t
  | .ifLtN _ _ t e => natOnly t && natOnly e
  | .ifLtR _ _ _ _ => false
  | .whileLtN _ _ b => natOnly b
  | .whileLtR _ _ _ => false

/-- **The compiled program of a statement without reals has no real instruction.** -/
theorem compile_natOnly : ∀ (s : Stmt), natOnly s = true →
    ∀ base, ∀ j ∈ compile s base, j.isReal = false
  | .skip, _, _, j, hj => by simp [compile] at hj
  | .instr i, h, _, j, hj => by
    simp only [compile, List.mem_singleton] at hj
    subst hj
    simpa [natOnly] using h
  | .seq s t, h, base, j, hj => by
    simp only [natOnly, Bool.and_eq_true] at h
    simp only [compile, List.mem_append] at hj
    rcases hj with hj | hj
    · exact compile_natOnly s h.1 _ j hj
    · exact compile_natOnly t h.2 _ j hj
  | .ifLtN a b t e, h, base, j, hj => by
    simp only [natOnly, Bool.and_eq_true] at h
    simp only [compile, List.mem_append, List.mem_cons] at hj
    rcases hj with (rfl | hj) | (rfl | hj)
    · rfl
    · exact compile_natOnly e h.2 _ j hj
    · rfl
    · exact compile_natOnly t h.1 _ j hj
  | .ifLtR _ _ _ _, h, _, _, _ => by simp [natOnly] at h
  | .whileLtN a b body, h, base, j, hj => by
    simp only [natOnly] at h
    simp only [compile, List.mem_append, List.mem_cons] at hj
    rcases hj with (rfl | rfl | hj) | hj
    · rfl
    · rfl
    · exact compile_natOnly body h _ j hj
    · simp at hj; subst hj; rfl
  | .whileLtR _ _ _, h, _, _, _ => by simp [natOnly] at h

/-! ### The natural-word configuration -/

/-- The residue modulo `M` of (the integer part of) a real, as a natural word. -/
def resW (M : ℕ) (x : ℝ) : ℕ := (⌊x⌋ % (M : ℤ)).toNat

lemma res_resW {M : ℕ} (hM : 0 < M) (z : ℤ) : ModNat.Res M (z : ℝ) (resW M z) := by
  refine ⟨z, rfl, ?_⟩
  unfold resW
  rw [Int.floor_intCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]

lemma resW_lt {M : ℕ} (hM : 0 < M) (x : ℝ) : resW M x < M := by
  unfold resW
  have h1 := Int.emod_lt_of_pos ⌊x⌋ (by exact_mod_cast hM : (0 : ℤ) < M)
  have h2 := Int.emod_nonneg ⌊x⌋ (by omega : (M : ℤ) ≠ 0)
  omega

/-- **The natural-word configuration simulating `c`**: the natural registers `< R` and the
natural memory at addresses `≤ W` of `c`, the residues modulo `M` of the real registers `< R`
at `R + r` and of the real memory cells `≤ W` at `β + a`, nothing else; no real. -/
def natCfg (R W M β : ℕ) (c : Config) : Config where
  pc := c.pc
  nreg r := if r < R then c.nreg r else if r < 2 * R then resW M (c.rreg (r - R)) else 0
  rreg _ := 0
  nmem a := if a ≤ W then c.nmem a else if β ≤ a ∧ a ≤ β + W then resW M (c.rmem (a - β))
    else 0
  rmem _ := 0
  output := c.output

theorem sim_natCfg {R W M β : ℕ} {c : Config} (hM : 0 < M) (hβ : W < β)
    (hr : ∀ r, ∃ z : ℤ, c.rreg r = z) (hm : ∀ a, ∃ z : ℤ, c.rmem a = z) :
    ModNat.Sim R W M β c (natCfg R W M β c) where
  nreg r hr' := by simp [natCfg, hr']
  rreg r hr' := by
    obtain ⟨z, hz⟩ := hr r
    have h1 : ¬ R + r < R := by omega
    have h2 : R + r < 2 * R := by omega
    simp only [natCfg, h1, h2, ↓reduceIte, Nat.add_sub_cancel_left, hz]
    exact res_resW hM z
  nmem a ha := by simp [natCfg, ha]
  rmem a ha := by
    obtain ⟨z, hz⟩ := hm a
    have h1 : ¬ β + a ≤ W := by omega
    have h2 : β ≤ β + a ∧ β + a ≤ β + W := ⟨by omega, by omega⟩
    simp only [natCfg, h1, h2, and_self, ↓reduceIte, Nat.add_sub_cancel_left, hz]
    exact res_resW hM z
  output := rfl

theorem wb_natCfg {R W M β W' : ℕ} {c : Config} (hc : WordsBounded W c) (hM : 0 < M)
    (hW : W ≤ W') (hMW : M ≤ W') : WordsBounded W' (natCfg R W M β c) := by
  refine ⟨fun r => ?_, fun a => ?_⟩
  · simp only [natCfg]
    split_ifs
    · exact (hc.1 r).trans hW
    · exact (resW_lt hM _).le.trans hMW
    · exact Nat.zero_le _
  · simp only [natCfg]
    split_ifs
    · exact (hc.2 a).trans hW
    · exact (resW_lt hM _).le.trans hMW
    · exact Nat.zero_le _

/-! ### Klein's masked program on natural words -/

/-- **Klein's masked program on natural words**: the constants `Mo = 2 Hc + 1`, `Hc` and
`β = W + 1` (`W = B + 16 (n + 1)`) into their registers, then `kleinProgM` with its reals kept
modulo `Mo` (`ModNat.toNat`). -/
def kleinProgMN (B nD n k t Hc : ℕ) : Stmt :=
  .seq (ModNat.constsS 201 (2 * Hc + 1) Hc (B + 16 * (n + 1) + 1))
    (ModNat.toNat 201 (2 * Hc + 1) (kleinProgM B nD n k t))

/-- The word bound of `kleinProgMN`: `2 W + 1 + Mo² + Mo`. -/
def kleinWN (B n Hc : ℕ) : ℕ :=
  2 * (B + 16 * (n + 1)) + 1 + (2 * Hc + 1) * (2 * Hc + 1) + (2 * Hc + 1)

/-- **`kleinProgMN` has no real instruction and no real test** (checked by the kernel). -/
theorem kleinProgMN_natOnly (B nD n k t Hc : ℕ) : natOnly (kleinProgMN B nD n k t Hc) = true := by
  kernel_rfl

/-- The compiled `kleinProgMN` has no real instruction. -/
theorem kleinProgMN_compile_noReal (B nD n k t Hc base : ℕ) :
    ∀ j ∈ compile (kleinProgMN B nD n k t Hc) base, j.isReal = false :=
  compile_natOnly _ (kleinProgMN_natOnly B nD n k t Hc) base

/-- An answer read from the natural words: the reach bit, and the natural word at `β + a`
holding the residue of the real word `a` of the answer. -/
def kOutN (nD n k t β : ℕ) (d : Config) (q i : ℕ) : Option ℤ :=
  if d.nmem (aRBM n k + q * t + i) = 1 then some (d.nmem (β + (aOUT nD + q * t + i)) : ℤ)
  else none

/-- **The answer read from the natural words is the real answer** when it is an integer in
`[0, Mo)`. -/
lemma kOutN_of_sim {R W Mo β nD n k t q i : ℕ} {c d : Config}
    (hS : ModNat.Sim R W Mo β c d) (h1 : aRBM n k + q * t + i ≤ W)
    (h2 : aOUT nD + q * t + i ≤ W) {o : Option ℤ}
    (ho : kOutM nD n k t c q i = o.map ((↑) : ℤ → ℝ))
    (hb : ∀ z, o = some z → 0 ≤ z ∧ z < Mo) :
    kOutN nD n k t β d q i = o := by
  unfold kOutM at ho
  unfold kOutN
  rw [hS.nmem _ h1]
  split_ifs at ho ⊢ with hc
  · cases o with
    | none => simp at ho
    | some z =>
      simp only [Option.map_some, Option.some.injEq] at ho
      obtain ⟨hz0, hzM⟩ := hb z rfl
      have hres := hS.rmem _ h2
      have e : d.nmem (β + (aOUT nD + q * t + i)) = z.toNat :=
        hres.eq_of_lt (by rw [ho]; exact_mod_cast (Int.toNat_of_nonneg hz0).symm) (by omega)
      rw [e, Int.toNat_of_nonneg hz0]
  · cases o with
    | none => rfl
    | some z => simp at ho

/-- A distance with nonnegative lengths is at most the sum of all the lengths. -/
lemma dist_le_sum_len {X A : Type*} [Fintype A] [DecidableEq X] {G : Digraph X A}
    (hnn : ∀ a, 0 ≤ G.len a) {x y : X} (h : Reach G x y) : dist G x y ≤ ∑ a, G.len a := by
  classical
  obtain ⟨L, hL, -⟩ := exists_walk_dist hnn h
  obtain ⟨L', hL', -, hnd⟩ := exists_nodup_walk hL
  have h2 := dist_le hnn hL'
  have hnd' : L'.Nodup := hnd.of_map _
  have h3 : wlen G L' ≤ ∑ a, G.len a := by
    unfold wlen
    rw [← List.sum_toFinset _ hnd']
    exact Finset.sum_le_univ_sum_of_nonneg fun a => hnn a
  linarith

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

local notation "𝒢" => pieceGraph M S ℓ

/-- The answers of the trip are integers in `[0, tripW]`. -/
lemma odist_le_tripW (H : Hyp M k g S ℓ) {x y : V} {z : ℤ} (h : odist 𝒢 x y = some z) :
    0 ≤ z ∧ z ≤ tripW S ℓ := by
  unfold odist at h
  split_ifs at h with hr
  obtain rfl := Option.some.inj h
  have hnn : ∀ a, 0 ≤ (pieceGraph M S ℓ).len a := fun a => (H.pos a.1 a.2).le
  refine ⟨dist_nonneg hnn hr, (dist_le_sum_len hnn hr).trans ?_⟩
  show ∑ a : {d // d ∈ S}, ℓ a.1 ≤ ∑ d ∈ S, |ℓ d|
  rw [Finset.sum_coe_sort S ℓ]
  exact Finset.sum_le_sum fun d _ => le_abs_self _

lemma tripW_le_kleinHI : (tripW S ℓ : ℝ) ≤ kleinHI V F S ℓ k := by
  have hW : (0 : ℝ) ≤ tripW S ℓ := by exact_mod_cast tripW_nonneg
  have hL : (0 : ℝ) ≤ tripL V S ℓ := by exact_mod_cast tripL_nonneg
  have hK : (0 : ℝ) ≤ tripK V S ℓ := by exact_mod_cast tripK_nonneg
  have h1 := kleinZ_nonneg (V := V) (F := F) (S := S) (ℓ := ℓ) (k := k)
  have h2 := kleinA_sub_tripTh_nonneg (V := V) (S := S) (ℓ := ℓ) (k := k)
  unfold kleinHI kleinAI
  linarith

/-- **Klein's masked program end to end, on natural words only** (`kleinM_exec_exists` for
`kleinProgMN`): for every map, boundary, piece and lengths meeting the hypotheses of the trip,
`t` targets `X i` (none of them a root) and flags `fl` of the moves, with
`N = #V + #F + #D`, there are an input `P`, a starting configuration `c₀` of the real program
(its reals are integers) and a bound `Hc` of the compared differences,
`kleinHI ≤ Hc < kleinHI + 1`, such that the natural-word program `kleinProgMN` (no real
instruction: `kleinProgMN_natOnly`) runs from `natCfg c₀` (the natural words of `c₀` and the
residues modulo `Mo = 2 Hc + 1` of its reals, no real) with words at most
`kleinWN B n Hc` within `4 · 36500000 (N lg N + f t lg N) + 3` steps, prints nothing, and ends
with the answers of the flagged moves **read exactly from its natural words** (`kOutN`): in the
slot `kRank fl j` of a flagged move `j`, the distance in the piece from `tail (g j)` to `X i`,
none when `X i` is not reached. There is no hypothesis on the size of the lengths. -/
theorem kleinM_exec_exists_nat' (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (t : ℕ)
    (X : ℕ → V) (hX : ∀ i < t, ¬ IsRoot M k g (X i)) (fl : ℕ → Bool) :
    ∃ (n B Hc : ℕ) (P : Input) (c₀ d' : Config) (steps : ℕ),
      n = 2 * (Fintype.card V + Fintype.card F + Fintype.card D) ∧
      kleinHI V F S ℓ k ≤ Hc ∧ (Hc : ℝ) < kleinHI V F S ℓ k + 1 ∧
      Exec P (kleinWN B n Hc) (kleinProgMN B (Fintype.card D) n k t Hc)
        (natCfg 201 (B + 16 * (n + 1)) (2 * Hc + 1) (B + 16 * (n + 1) + 1) c₀) d' steps ∧
      steps ≤ 4 * (36500000 * ((Fintype.card V + Fintype.card F + Fintype.card D) *
          BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D) +
        kRank fl k * t * BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D))) + 3 ∧
      (∀ j < k, fl j = true → ∀ i < t,
        kOutN (Fintype.card D) n k t (B + 16 * (n + 1) + 1) d' (kRank fl j) i =
          odist 𝒢 (tripSrc M k g j) (X i)) ∧
      d'.output = c₀.output ∧
      aOUT (Fintype.card D) + k * t ≤ B ∧ aRBM n k + k * t ≤ B := by
  obtain ⟨n, ιv, ιg, ιf, ιe, σ, P, B, T, C, vs, ts, fs, cs, c₀, hn, hWa, hB, hOUT, hRB, hP, hL,
    hK, hG, hO, hXT, hI, hoff, hCr, hT, hc₀, hwt, hph, htl, hth, hh0, hr0, hm0⟩ :=
    klein_exec_pre H hR t X hX
  have hf : kRank fl k * t ≤ k * t := Nat.mul_le_mul_right _ (kRank_le fl k)
  have hc₀' : WordsBounded (B + k + 16 * (n + 1)) (withFlags n k fl c₀) :=
    withFlags_wb ⟨fun r => (hc₀.1 r).trans (by omega), fun a => (hc₀.2 a).trans (by omega)⟩
      (by omega)
  have hRB' : aRBM n k + kRank fl k * t ≤ B + k := by unfold aRBM; unfold aRB at hRB; omega
  obtain ⟨c', steps, e, hsteps, -, hd, hout⟩ := kleinM_exec (B := B + k) (fl := fl)
    (by omega) (by omega) (by omega) hRB'
    (fun i => (hP i).trans (by omega)) H hR hL hK hG hO hXT hI hoff hCr hT hc₀' hwt hph htl hth
    hh0 (fun j hj => withFlags_mk hj)
  set Hc := ⌈kleinHI V F S ℓ k⌉₊ with hHcdef
  have hHI0 : 0 ≤ kleinHI V F S ℓ k :=
    (by exact_mod_cast tripW_nonneg : (0 : ℝ) ≤ tripW S ℓ).trans tripW_le_kleinHI
  have hHc : kleinHI V F S ℓ k ≤ Hc := Nat.le_ceil _
  have hHc' : (Hc : ℝ) < kleinHI V F S ℓ k + 1 := Nat.ceil_lt_add_one hHI0
  have hcmp := kleinProgM_cmpOK (B := B + k) (fl := fl) (by omega) (by omega) (by omega) hRB'
    (fun i => (hP i).trans (by omega)) H hR hL hK hG hO hXT hI hoff hCr hT hc₀' hwt hph htl hth
    hh0 (fun j hj => withFlags_mk hj) hHc
  set W := B + k + 16 * (n + 1) with hWdef
  set Mo := 2 * Hc + 1 with hMo
  have hW' : kleinWN (B + k) n Hc = 2 * W + 1 + Mo * Mo + Mo := by unfold kleinWN; rfl
  have hr0' : ∀ r, ∃ z : ℤ, (withFlags n k fl c₀).rreg r = z := fun r =>
    ⟨0, by simp [withFlags, hr0 r]⟩
  obtain ⟨d', k', ex, hk', hS', -, -, -, -, -⟩ := ModNat.ExecCmp.toNat_consts (hcmp.exec e)
    (kleinProgM_regsOK _ _ _ _ _) (kleinProgM_noDivR _ _ _ _ _) (M := Mo) (by omega)
    (β := W + 1) (W' := kleinWN (B + k) n Hc) (by omega) (by omega) (by omega) (by omega)
    (d := natCfg 201 W Mo (W + 1) (withFlags n k fl c₀))
    (sim_natCfg (by omega) (by omega) hr0' (fun a => hm0 a))
    (wb_natCfg hc₀' (by omega) (by omega) (by omega))
  refine ⟨n, B + k, Hc, P, withFlags n k fl c₀, d', k', hn, hHc, hHc', ex, ?_, fun j hj hfj i hi =>
    ?_, ?_, by omega, by unfold aRBM; unfold aRB at hRB; omega⟩
  · have hs2 : steps ≤ 36500000 * ((Fintype.card V + Fintype.card F + Fintype.card D) *
          BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D) +
        kRank fl k * t * BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D)) :=
      hsteps.trans (by
      rw [hn]
      exact kleinM_steps_le (nV := Fintype.card V) (nF := Fintype.card F)
        (nD := Fintype.card D) (nS := S.card) (k := k) (f := kRank fl k) (t := t)
        (by have := H.face.two_le; have := H.k_le_card; omega) (card_le_univ S) H.k_le_card)
    omega
  · have hq : kRank fl j * t + t ≤ kRank fl k * t := by
      have := Nat.mul_le_mul_right t (kRank_succ_le fl hj hfj)
      rw [Nat.add_mul, one_mul] at this
      exact this
    refine kOutN_of_sim hS' (by unfold aRBM at hRB' ⊢; omega)
      (by unfold aOUT at hOUT ⊢; omega) (hd j hj hfj i hi) fun z hz => ?_
    obtain ⟨hz0, hz1⟩ := odist_le_tripW H hz
    have h1 : ((z : ℤ) : ℝ) ≤ Hc := by
      have : ((z : ℤ) : ℝ) ≤ tripW S ℓ := by exact_mod_cast hz1
      linarith [tripW_le_kleinHI (V := V) (F := F) (S := S) (ℓ := ℓ) (k := k)]
    refine ⟨hz0, ?_⟩
    have h2 : z ≤ (Hc : ℤ) := by exact_mod_cast h1
    omega
  · rw [hS'.output, hout]

/-- **Klein's masked program end to end, on natural words only** (see
`kleinM_exec_exists_nat'`, which also bounds the answer arrays by `B`). -/
theorem kleinM_exec_exists_nat (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (t : ℕ)
    (X : ℕ → V) (hX : ∀ i < t, ¬ IsRoot M k g (X i)) (fl : ℕ → Bool) :
    ∃ (n B Hc : ℕ) (P : Input) (c₀ d' : Config) (steps : ℕ),
      n = 2 * (Fintype.card V + Fintype.card F + Fintype.card D) ∧
      kleinHI V F S ℓ k ≤ Hc ∧ (Hc : ℝ) < kleinHI V F S ℓ k + 1 ∧
      Exec P (kleinWN B n Hc) (kleinProgMN B (Fintype.card D) n k t Hc)
        (natCfg 201 (B + 16 * (n + 1)) (2 * Hc + 1) (B + 16 * (n + 1) + 1) c₀) d' steps ∧
      steps ≤ 4 * (36500000 * ((Fintype.card V + Fintype.card F + Fintype.card D) *
          BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D) +
        kRank fl k * t * BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D))) + 3 ∧
      (∀ j < k, fl j = true → ∀ i < t,
        kOutN (Fintype.card D) n k t (B + 16 * (n + 1) + 1) d' (kRank fl j) i =
          odist 𝒢 (tripSrc M k g j) (X i)) ∧
      d'.output = c₀.output := by
  obtain ⟨n, B, Hc, P, c₀, d', steps, h1, h2, h3, h4, h5, h6, h7, -⟩ :=
    kleinM_exec_exists_nat' H hR t X hX fl
  exact ⟨n, B, Hc, P, c₀, d', steps, h1, h2, h3, h4, h5, h6, h7⟩

end Klein

end PlanarFlow
