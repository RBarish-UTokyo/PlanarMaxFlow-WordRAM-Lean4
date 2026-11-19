module

public import PlanarFlow.NegSSSP.Enc.PrmWc

/-!
# Reduced lengths as natural words, from residues

The node keeps the lengths `ℓ` and the potentials `δᵢ` of its children as reals, simulated modulo
`M` (`Sim`, residues `Res M x v`: `v = z mod M` for the integer `z = x`). The side arrays need the
reduced lengths `ℓ d + δ (tail d) − δ (head d)` as natural words. When the true value lies in
`[0, M)` it is recovered from the residues: `(Rℓ + Rδt + M − Rδh) mod M`.

`rlProg`: for `i < n`, `OUT[i] := (L[i] + D[T[i]] + M − D[H[i]]) mod M` (registers `2750 … 2763`,
free in the node's and the split's programs). **`rlProg_exec`**: within `19 n + 4` steps, for
residues `L[i] ≡ ℓᵢ`, `D[T[i]] ≡ δtᵢ`, `D[H[i]] ≡ δhᵢ (mod M)` and `0 ≤ ℓᵢ + δtᵢ − δhᵢ < M`,
`OUT[i] = (ℓᵢ + δtᵢ − δhᵢ).toNat`; memory outside `[Ob, Ob + n)`, registers outside
`[2750, 2763]`, reals and output kept. Words: `3 M ≤ W`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- One reduced length (`i = r2757`). -/
def rlBody : Stmt :=
  block [.addN 2758 2751 2757, .loadN 2759 2758,
    .addN 2758 2752 2757, .loadN 2758 2758, .addN 2758 2754 2758, .loadN 2760 2758,
    .addN 2758 2753 2757, .loadN 2758 2758, .addN 2758 2754 2758, .loadN 2761 2758,
    .addN 2759 2759 2760, .addN 2759 2759 2755, .subN 2759 2759 2761, .modN 2759 2759 2755,
    .addN 2758 2756 2757, .storeN 2758 2759, .addN 2757 2757 2762]

/-- **The reduced lengths from residues** (`r2750 = n`, `r2751 = Lb`, `r2752 = Tb`, `r2753 = Hb`,
`r2754 = Db`, `r2755 = M`, `r2756 = Ob`). -/
def rlProg : Stmt :=
  .seq (block [.constN 2757 0, .constN 2762 1]) (.whileLtN 2757 2750 rlBody)

theorem rlProg_natOnly : Klein.natOnly rlProg = true := by kernel_rfl

/-- The arithmetic: residues give the value in `[0, M)`. -/
theorem rl_val {M a b c : ℕ} {l t h : ℤ} (hM : 0 < M) (ha : (a : ℤ) = l % M)
    (hb : (b : ℤ) = t % M) (hc : (c : ℤ) = h % M) (h0 : 0 ≤ l + t - h) (h1 : l + t - h < M) :
    (a + b + M - c) % M = (l + t - h).toNat := by
  have hcM : c < M := by
    have := Int.emod_lt_of_pos h (by exact_mod_cast hM : (0 : ℤ) < M); omega
  have e : (l % M + t % M + M - h % M) % (M : ℤ) = (l + t - h) % M := by
    have : l % (M : ℤ) + t % M + M - h % M = (l + t - h) + M * (1 - l / M - t / M + h / M) := by
      have := Int.emod_add_mul_ediv l M; have := Int.emod_add_mul_ediv t M
      have := Int.emod_add_mul_ediv h M; linarith
    rw [this, Int.add_mul_emod_self_left]
  have key : (((a + b + M - c) % M : ℕ) : ℤ) = l + t - h := by
    rw [Int.natCast_mod, Nat.cast_sub (by omega)]
    push_cast
    rw [ha, hb, hc, e, Int.emod_eq_of_lt h0 h1]
  rw [← key, Int.toNat_natCast]

theorem rl_mle {a M W : ℕ} (h : a ≤ W) : a % M ≤ W := Nat.le_trans (Nat.mod_le _ _) h

theorem rlBody_exec (c : Config) (hc : WordsBounded W c) {Lb Tb Hb Db M Ob i : ℕ}
    (r51 : c.nreg 2751 = Lb) (r52 : c.nreg 2752 = Tb) (r53 : c.nreg 2753 = Hb)
    (r54 : c.nreg 2754 = Db) (r55 : c.nreg 2755 = M) (r56 : c.nreg 2756 = Ob)
    (r57 : c.nreg 2757 = i) (r62 : c.nreg 2762 = 1) (hM : 0 < M)
    (w1 : Lb + i ≤ W) (w2 : Tb + i ≤ W) (w3 : Hb + i ≤ W) (w4 : Ob + i ≤ W) (w5 : i + 1 ≤ W)
    (w6 : Db + c.nmem (Tb + i) ≤ W) (w7 : Db + c.nmem (Hb + i) ≤ W)
    (w8 : c.nmem (Lb + i) + c.nmem (Db + c.nmem (Tb + i)) + M ≤ W) :
    ∃ c' k, Exec P W rlBody c c' k ∧ k = 17 ∧
      c'.nmem = upd c.nmem (Ob + i) ((c.nmem (Lb + i) + c.nmem (Db + c.nmem (Tb + i)) + M -
        c.nmem (Db + c.nmem (Hb + i))) % M) ∧ c'.nreg 2757 = i + 1 ∧
      (∀ r, (r < 2757 ∨ 2761 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rlBody
  exec_block
  all_goals try ((try config_simp); (try simp only [r51, r52, r53, r54, r55, r56, r57]); omega)
  refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r51, r52, r53, r54, r55, r56, r57]
  · config_simp; simp only [r57, r62]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **The reduced lengths on the machine** (see the module docstring). -/
theorem rlProg_exec {n Lb Tb Hb Db M Ob : ℕ} (c : Config) (hc : WordsBounded W c)
    (r50 : c.nreg 2750 = n) (r51 : c.nreg 2751 = Lb) (r52 : c.nreg 2752 = Tb)
    (r53 : c.nreg 2753 = Hb) (r54 : c.nreg 2754 = Db) (r55 : c.nreg 2755 = M)
    (r56 : c.nreg 2756 = Ob) (hM : 0 < M) (hW : 3 * M ≤ W) (h1 : 1 ≤ W)
    (wL : Lb + n ≤ W) (wT : Tb + n ≤ W) (wH : Hb + n ≤ W) (wO : Ob + n ≤ W)
    (dL : Ob + n ≤ Lb ∨ Lb + n ≤ Ob) (dT : Ob + n ≤ Tb ∨ Tb + n ≤ Ob)
    (dH : Ob + n ≤ Hb ∨ Hb + n ≤ Ob)
    (hT : ∀ i < n, Db + c.nmem (Tb + i) ≤ W ∧ (Db + c.nmem (Tb + i) < Ob ∨ Ob + n ≤ Db + c.nmem (Tb + i)))
    (hH : ∀ i < n, Db + c.nmem (Hb + i) ≤ W ∧ (Db + c.nmem (Hb + i) < Ob ∨ Ob + n ≤ Db + c.nmem (Hb + i)))
    (ℓ δt δh : ℕ → ℤ)
    (hl : ∀ i < n, (c.nmem (Lb + i) : ℤ) = ℓ i % M)
    (ht : ∀ i < n, (c.nmem (Db + c.nmem (Tb + i)) : ℤ) = δt i % M)
    (hh : ∀ i < n, (c.nmem (Db + c.nmem (Hb + i)) : ℤ) = δh i % M)
    (hv : ∀ i < n, 0 ≤ ℓ i + δt i - δh i ∧ ℓ i + δt i - δh i < M) :
    ∃ c' k, Exec P W rlProg c c' k ∧ k ≤ 19 * n + 4 ∧
      (∀ i < n, c'.nmem (Ob + i) = (ℓ i + δt i - δh i).toNat) ∧
      (∀ a, (a < Ob ∨ Ob + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2750 ∨ 2763 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hres : ∀ i < n, c.nmem (Lb + i) < M ∧ c.nmem (Db + c.nmem (Tb + i)) < M ∧
      c.nmem (Db + c.nmem (Hb + i)) < M := fun i hi => by
    have a := Int.emod_lt_of_pos (ℓ i) (by exact_mod_cast hM : (0 : ℤ) < M)
    have b := Int.emod_lt_of_pos (δt i) (by exact_mod_cast hM : (0 : ℤ) < M)
    have d := Int.emod_lt_of_pos (δh i) (by exact_mod_cast hM : (0 : ℤ) < M)
    have := hl i hi; have := ht i hi; have := hh i hi
    omega
  unfold rlProg
  obtain ⟨c₁, k₁, e₁, hk₁, g57, g62, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 2757 0, .constN 2762 1]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 2757 = 0 ∧ c₁.nreg 2762 = 1 ∧
      (∀ r, r ≠ 2757 → r ≠ 2762 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ e < i, c'.nmem (Ob + e) = (ℓ e + δt e - δh e).toNat) ∧
      (∀ a, (a < Ob ∨ Ob + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2750 ∨ 2763 < r) → c'.nreg r = c.nreg r) ∧
      c'.nreg 2751 = Lb ∧ c'.nreg 2752 = Tb ∧ c'.nreg 2753 = Hb ∧ c'.nreg 2754 = Db ∧
      c'.nreg 2755 = M ∧ c'.nreg 2756 = Ob ∧ c'.nreg 2762 = 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  have k1 : ∀ r, (r < 2757 ∨ 2762 < r) → c₁.nreg r = c.nreg r := fun r h =>
    gn₁ r (by omega) (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2757) (bR := 2750)
    (body := rlBody) J (K := 17) (n := n) c₁ e₁.wb_right g57
    (by rw [k1 2750 (by omega)]; exact r50)
    ⟨fun e he => absurd he (by omega), fun a _ => by rw [gm₁], fun r hr => k1 r (by omega),
      by rw [k1 _ (by omega)]; exact r51, by rw [k1 _ (by omega)]; exact r52,
      by rw [k1 _ (by omega)]; exact r53, by rw [k1 _ (by omega)]; exact r54,
      by rw [k1 _ (by omega)]; exact r55, by rw [k1 _ (by omega)]; exact r56, g62,
      gr₁, grm₁, go₁⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j3, j51, j52, j53, j54, j55, j56, j62, jr, jrm, jo⟩ := hJ
      obtain ⟨t1, t2⟩ := hT i hi
      obtain ⟨u1, u2⟩ := hH i hi
      have eL : c'.nmem (Lb + i) = c.nmem (Lb + i) := j2 _ (by omega)
      have eT : c'.nmem (Tb + i) = c.nmem (Tb + i) := j2 _ (by omega)
      have eH : c'.nmem (Hb + i) = c.nmem (Hb + i) := j2 _ (by omega)
      have eDT : c'.nmem (Db + c.nmem (Tb + i)) = c.nmem (Db + c.nmem (Tb + i)) :=
        j2 _ (by omega)
      have eDH : c'.nmem (Db + c.nmem (Hb + i)) = c.nmem (Db + c.nmem (Hb + i)) :=
        j2 _ (by omega)
      obtain ⟨q1, q2, q3⟩ := hres i hi
      obtain ⟨c'', k, ex, hk, hm, h57, hn, hr, hrm, ho⟩ := rlBody_exec (P := P) c' hw j51 j52 j53
        j54 j55 j56 ha j62 hM (by omega) (by omega) (by omega) (by omega) (by omega)
        (by rw [eT]; omega) (by rw [eH]; omega) (by rw [eL, eT, eDT]; omega)
      refine ⟨c'', k, ex, by omega, h57,
        by rw [hn 2750 (by omega)]; exact hb, fun e he => ?_, fun a h => ?_, fun r hr' => ?_,
        by rw [hn 2751 (by omega)]; exact j51, by rw [hn 2752 (by omega)]; exact j52,
        by rw [hn 2753 (by omega)]; exact j53, by rw [hn 2754 (by omega)]; exact j54,
        by rw [hn 2755 (by omega)]; exact j55, by rw [hn 2756 (by omega)]; exact j56,
        by rw [hn 2762 (by omega)]; exact j62,
        by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩
      · rw [hm, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact j1 e he
        · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), eL, eT, eH, eDT, eDH]
          exact rl_val hM (hl e hi) (ht e hi) (hh e hi) (hv e hi).1 (hv e hi).2
      · rw [hm, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact j2 a (by omega)
      · by_cases h' : r < 2750
        · rw [hn r (by omega)]; exact j3 r hr'
        · rw [hn r (by omega)]; exact j3 r hr')
  obtain ⟨j1, j2, j3, -, -, -, -, -, -, -, jr, jrm, jo⟩ := hJ
  exact ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by omega, j1, j2, j3, jr, jrm, jo⟩

end NegSSSP

end PlanarFlow
