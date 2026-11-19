module

public import PlanarFlow.Klein.ExecNat
public import PlanarFlow.Klein.ProgTripC

/-!
# Klein's (unmasked) program on natural words only

The analogue of `PlanarFlow/Klein/ExecNat.lean` for the program `kleinProg`, which answers the
`t` queries at every move: its runs are compare-bounded (`kleinProg_cmpOK`), it names only the
registers `< 201` and uses no `divR` (`kleinProg_regsOK`, `kleinProg_noDivR`), so it runs on
natural words modulo `Mo = 2 Hc + 1`.

* `kleinProgN`: the constants, then `ModNat.toNat 201 Mo kleinProg`; `kleinProgN_natOnly`: no
  real instruction (checked by the kernel).
* `kOutNK`, `kOutNK_of_sim`: the answers read from the natural words.
* `klein_exec_exists_nat`: **`klein_exec_exists` on natural words only**: the answers of every
  move at every target are read exactly from the natural words, for all lengths.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt

/-- **Klein's program on natural words**: the constants `Mo = 2 Hc + 1`, `Hc`, `β = W + 1`, then
`kleinProg` with its reals kept modulo `Mo`. -/
def kleinProgN (B nD n k t Hc : ℕ) : Stmt :=
  .seq (ModNat.constsS 201 (2 * Hc + 1) Hc (B + 16 * (n + 1) + 1))
    (ModNat.toNat 201 (2 * Hc + 1) (kleinProg B nD n k t))

/-- **`kleinProgN` has no real instruction and no real test** (checked by the kernel). -/
theorem kleinProgN_natOnly (B nD n k t Hc : ℕ) : natOnly (kleinProgN B nD n k t Hc) = true := by
  kernel_rfl

/-- An answer of `kleinProg` read from the natural words. -/
def kOutNK (nD n t β : ℕ) (d : Config) (j i : ℕ) : Option ℤ :=
  if d.nmem (aRB n + j * t + i) = 1 then some (d.nmem (β + (aOUT nD + j * t + i)) : ℤ)
  else none

lemma kOutNK_of_sim {R W Mo β nD n t j i : ℕ} {c d : Config}
    (hS : ModNat.Sim R W Mo β c d) (h1 : aRB n + j * t + i ≤ W)
    (h2 : aOUT nD + j * t + i ≤ W) {o : Option ℤ}
    (ho : kOut nD n t c j i = o.map ((↑) : ℤ → ℝ))
    (hb : ∀ z, o = some z → 0 ≤ z ∧ z < Mo) :
    kOutNK nD n t β d j i = o := by
  unfold kOut at ho
  unfold kOutNK
  rw [hS.nmem _ h1]
  split_ifs at ho ⊢ with hc
  · cases o with
    | none => simp at ho
    | some z =>
      simp only [Option.map_some, Option.some.injEq] at ho
      obtain ⟨hz0, hzM⟩ := hb z rfl
      have hres := hS.rmem _ h2
      have e : d.nmem (β + (aOUT nD + j * t + i)) = z.toNat :=
        hres.eq_of_lt (by rw [ho]; exact_mod_cast (Int.toNat_of_nonneg hz0).symm) (by omega)
      rw [e, Int.toNat_of_nonneg hz0]
  · cases o with
    | none => rfl
    | some z => simp at ho

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

local notation "𝒢" => pieceGraph M S ℓ

/-- **Klein's program end to end, on natural words only** (`klein_exec_exists` for
`kleinProgN`): there are an input `P`, a starting configuration `c₀` of the real program and a
bound `kleinHI ≤ Hc < kleinHI + 1` such that the natural-word program `kleinProgN` runs from
`natCfg c₀` with words at most `kleinWN B n Hc` within `4 · 36500000 (N lg N + k t lg N) + 3`
steps, prints nothing, and ends with the answers of every move `j < k` at every target `X i`
read exactly from its natural words (`kOutNK`): the distance in the piece from `tail (g j)` to
`X i`, none when it is not reached. No hypothesis bounds the lengths. -/
theorem klein_exec_exists_nat' (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (t : ℕ)
    (X : ℕ → V) (hX : ∀ i < t, ¬ IsRoot M k g (X i)) :
    ∃ (n B Hc : ℕ) (P : Input) (c₀ d' : Config) (steps : ℕ),
      n = 2 * (Fintype.card V + Fintype.card F + Fintype.card D) ∧
      kleinHI V F S ℓ k ≤ Hc ∧ (Hc : ℝ) < kleinHI V F S ℓ k + 1 ∧
      Exec P (kleinWN B n Hc) (kleinProgN B (Fintype.card D) n k t Hc)
        (natCfg 201 (B + 16 * (n + 1)) (2 * Hc + 1) (B + 16 * (n + 1) + 1) c₀) d' steps ∧
      steps ≤ 4 * (36500000 * ((Fintype.card V + Fintype.card F + Fintype.card D) *
          BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D) +
        k * t * BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D))) + 3 ∧
      (∀ j < k, ∀ i < t,
        kOutNK (Fintype.card D) n t (B + 16 * (n + 1) + 1) d' j i =
          odist 𝒢 (tripSrc M k g j) (X i)) ∧
      d'.output = c₀.output ∧
      aOUT (Fintype.card D) + k * t ≤ B ∧ aRB n + k * t ≤ B := by
  obtain ⟨n, ιv, ιg, ιf, ιe, σ, P, B, T, C, vs, ts, fs, cs, c₀, hn, hWa, hB, hOUT, hRB, hP, hL,
    hK, hG, hO, hXT, hI, hoff, hCr, hT, hc₀, hwt, hph, htl, hth, hh0, hr0, hm0⟩ :=
    klein_exec_pre H hR t X hX
  obtain ⟨c', steps, e, hsteps, -, hd, hout⟩ := klein_exec hWa hB hOUT hRB hP H hR hL hK hG
    hO hXT hI hoff hCr hT hc₀ hwt hph htl hth hh0
  set Hc := ⌈kleinHI V F S ℓ k⌉₊ with hHcdef
  have hHI0 : 0 ≤ kleinHI V F S ℓ k :=
    (by exact_mod_cast tripW_nonneg : (0 : ℝ) ≤ tripW S ℓ).trans tripW_le_kleinHI
  have hHc : kleinHI V F S ℓ k ≤ Hc := Nat.le_ceil _
  have hHc' : (Hc : ℝ) < kleinHI V F S ℓ k + 1 := Nat.ceil_lt_add_one hHI0
  have hcmp := kleinProg_cmpOK hWa hB hOUT hRB hP H hR hL hK hG hO hXT hI hoff hCr hT hc₀ hwt
    hph htl hth hh0 hHc
  set W := B + 16 * (n + 1) with hWdef
  set Mo := 2 * Hc + 1 with hMo
  have hW' : kleinWN B n Hc = 2 * W + 1 + Mo * Mo + Mo := by unfold kleinWN; rfl
  have hr0' : ∀ r, ∃ z : ℤ, c₀.rreg r = z := fun r => ⟨0, by simp [hr0 r]⟩
  obtain ⟨d', k', ex, hk', hS', -, -, -, -, -⟩ := ModNat.ExecCmp.toNat_consts (hcmp.exec e)
    (kleinProg_regsOK _ _ _ _ _) (kleinProg_noDivR _ _ _ _ _) (M := Mo) (by omega)
    (β := W + 1) (W' := kleinWN B n Hc) (by omega) (by omega) (by omega) (by omega)
    (d := natCfg 201 W Mo (W + 1) c₀)
    (sim_natCfg (by omega) (by omega) hr0' (fun a => hm0 a))
    (wb_natCfg hc₀ (by omega) (by omega) (by omega))
  refine ⟨n, B, Hc, P, c₀, d', k', hn, hHc, hHc', ex, ?_, fun j hj i hi => ?_, ?_, hOUT, hRB⟩
  · have hs2 : steps ≤ 36500000 * ((Fintype.card V + Fintype.card F + Fintype.card D) *
          BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D) +
        k * t * BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D)) :=
      hsteps.trans (by
        rw [hn]
        exact klein_steps_le (nV := Fintype.card V) (nF := Fintype.card F)
          (nD := Fintype.card D) (nS := S.card) (k := k) (t := t)
          (by have := H.face.two_le; have := H.k_le_card; omega) (card_le_univ S) H.k_le_card)
    omega
  · have hq : j * t + t ≤ k * t := by
      have := Nat.mul_le_mul_right t (show j + 1 ≤ k by omega)
      rw [Nat.add_mul, one_mul] at this
      exact this
    refine kOutNK_of_sim hS' (by unfold aRB at hRB ⊢; omega)
      (by unfold aOUT at hOUT ⊢; omega) (hd j hj i hi) fun z hz => ?_
    obtain ⟨hz0, hz1⟩ := odist_le_tripW H hz
    have h1 : ((z : ℤ) : ℝ) ≤ Hc := by
      have : ((z : ℤ) : ℝ) ≤ tripW S ℓ := by exact_mod_cast hz1
      linarith [tripW_le_kleinHI (V := V) (F := F) (S := S) (ℓ := ℓ) (k := k)]
    refine ⟨hz0, ?_⟩
    have h2 : z ≤ (Hc : ℤ) := by exact_mod_cast h1
    omega
  · rw [hS'.output, hout]

/-- **Klein's program end to end, on natural words only** (see `klein_exec_exists_nat'`, which
also bounds the answer arrays by `B`). -/
theorem klein_exec_exists_nat (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (t : ℕ)
    (X : ℕ → V) (hX : ∀ i < t, ¬ IsRoot M k g (X i)) :
    ∃ (n B Hc : ℕ) (P : Input) (c₀ d' : Config) (steps : ℕ),
      n = 2 * (Fintype.card V + Fintype.card F + Fintype.card D) ∧
      kleinHI V F S ℓ k ≤ Hc ∧ (Hc : ℝ) < kleinHI V F S ℓ k + 1 ∧
      Exec P (kleinWN B n Hc) (kleinProgN B (Fintype.card D) n k t Hc)
        (natCfg 201 (B + 16 * (n + 1)) (2 * Hc + 1) (B + 16 * (n + 1) + 1) c₀) d' steps ∧
      steps ≤ 4 * (36500000 * ((Fintype.card V + Fintype.card F + Fintype.card D) *
          BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D) +
        k * t * BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D))) + 3 ∧
      (∀ j < k, ∀ i < t,
        kOutNK (Fintype.card D) n t (B + 16 * (n + 1) + 1) d' j i =
          odist 𝒢 (tripSrc M k g j) (X i)) ∧
      d'.output = c₀.output := by
  obtain ⟨n, B, Hc, P, c₀, d', steps, h1, h2, h3, h4, h5, h6, h7, -⟩ :=
    klein_exec_exists_nat' H hR t X hX
  exact ⟨n, B, Hc, P, c₀, d', steps, h1, h2, h3, h4, h5, h6, h7⟩

end Klein

end PlanarFlow
