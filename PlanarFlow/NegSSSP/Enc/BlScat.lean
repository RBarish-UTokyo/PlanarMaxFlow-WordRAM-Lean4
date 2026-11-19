module

public import PlanarFlow.NegSSSP.Enc.FlagK
public import PlanarFlow.NegSSSP.FaceKlein

/-!
# The lengths `bL` of a side in the numbering of the piece map (the scatter)

`sdWalk_exec` reads the lengths `bL[cn x] = (ℓ x.1).toNat` of the darts `x.1 ∈ K` of the piece
map `kmap N K` (`hLP`). The node has its lengths and the potentials of its children as residues
(`Sim`); `rlProg` turns them into reduced lengths `RL[h]` in the order of the piece (`h < m`),
and the scatter below places them by the index array `X[h] = cn (δ h)` of `bigProg_spec'`.

* `rlRaw`, **`rlProg_exec'`**: `rlProg` with no hypothesis on the true values: `OUT[i]` is the
  machine value `(L[i] + D[T[i]] + M − D[H[i]]) mod M` (`rlRaw`); `rl_val` gives its meaning
  when the true reduced length lies in `[0, M)`.
* `blProg` (registers `2776 … 2788`): `OUT[j] := 0` for `j < m'`, then `OUT[X[h]] := R[h]` for
  every `h < m` with `F[h] ≠ 0`. **`blProg_exec`**: within `5 m' + 14 m + 10` steps,
  `OUT[j] = blV … m j`; memory outside `[Kb, Kb + m')`, registers outside `[2776, 2788]`,
  reals, output kept.
* `blLen` (the lengths read back from `R` along `δ`), **`bl_hLP`**: with the facts of
  `bigProg_spec'`, `OUT[cn x] = (blLen … x.1).toNat` for `x.1 ∈ K`: the hypothesis `hLP` of
  `sdWalk_exec` for the lengths `blLen`; **`blLen_eq`**: `blLen d = f d` for the darts
  `d = δ h` (`h < m`) when `R[h] = f (δ h)`; **`faceLen_congr`**: the lengths of an instance
  depend only on the lengths on its darts, so `blLen` may replace the reduced lengths of the side
  (on which they agree, `rl_val`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

universe u

variable {P : Input} {W : ℕ}

/-! ### The reduced lengths without hypotheses on the true values -/

/-- The machine value of a reduced length from residues. -/
def rlRaw (mem : ℕ → ℕ) (Lb Tb Hb Db M i : ℕ) : ℕ :=
  (mem (Lb + i) + mem (Db + mem (Tb + i)) + M - mem (Db + mem (Hb + i))) % M

/-- **`rlProg` with the raw values** (see the module docstring). -/
theorem rlProg_exec' {n Lb Tb Hb Db M Ob : ℕ} (c : Config) (hc : WordsBounded W c)
    (r50 : c.nreg 2750 = n) (r51 : c.nreg 2751 = Lb) (r52 : c.nreg 2752 = Tb)
    (r53 : c.nreg 2753 = Hb) (r54 : c.nreg 2754 = Db) (r55 : c.nreg 2755 = M)
    (r56 : c.nreg 2756 = Ob) (hM : 0 < M) (hW : 3 * M ≤ W) (h1 : 1 ≤ W)
    (wL : Lb + n ≤ W) (wT : Tb + n ≤ W) (wH : Hb + n ≤ W) (wO : Ob + n ≤ W)
    (dL : Ob + n ≤ Lb ∨ Lb + n ≤ Ob) (dT : Ob + n ≤ Tb ∨ Tb + n ≤ Ob)
    (dH : Ob + n ≤ Hb ∨ Hb + n ≤ Ob)
    (hT : ∀ i < n, Db + c.nmem (Tb + i) ≤ W ∧
      (Db + c.nmem (Tb + i) < Ob ∨ Ob + n ≤ Db + c.nmem (Tb + i)))
    (hH : ∀ i < n, Db + c.nmem (Hb + i) ≤ W ∧
      (Db + c.nmem (Hb + i) < Ob ∨ Ob + n ≤ Db + c.nmem (Hb + i)))
    (hres : ∀ i < n, c.nmem (Lb + i) < M ∧ c.nmem (Db + c.nmem (Tb + i)) < M) :
    ∃ c' k, Exec P W rlProg c c' k ∧ k ≤ 19 * n + 4 ∧
      (∀ i < n, c'.nmem (Ob + i) = rlRaw c.nmem Lb Tb Hb Db M i) ∧
      (∀ a, (a < Ob ∨ Ob + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2750 ∨ 2763 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
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
    (∀ e < i, c'.nmem (Ob + e) = rlRaw c.nmem Lb Tb Hb Db M e) ∧
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
      obtain ⟨q1, q2⟩ := hres i hi
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
          rfl
      · rw [hm, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact j2 a (by omega)
      · rw [hn r (by omega)]; exact j3 r hr')
  obtain ⟨j1, j2, j3, -, -, -, -, -, -, -, jr, jrm, jo⟩ := hJ
  exact ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by omega, j1, j2, j3, jr, jrm, jo⟩

/-- **The meaning of the raw value**: the reduced length when the residues are those of `ℓ`,
`δt`, `δh` and the true value lies in `[0, M)`. -/
theorem rlRaw_val {mem : ℕ → ℕ} {Lb Tb Hb Db M i : ℕ} {l t h : ℤ} (hM : 0 < M)
    (ha : (mem (Lb + i) : ℤ) = l % M) (hb : (mem (Db + mem (Tb + i)) : ℤ) = t % M)
    (hc : (mem (Db + mem (Hb + i)) : ℤ) = h % M) (h0 : 0 ≤ l + t - h) (h1 : l + t - h < M) :
    rlRaw mem Lb Tb Hb Db M i = (l + t - h).toNat :=
  rl_val hM ha hb hc h0 h1

/-! ### The scatter of values -/

/-- `OUT[i] := 0` (`i = r2782`). -/
def blZ : Stmt := block [.addN 2785 2777 2782, .storeN 2785 2783, .addN 2782 2782 2784]

/-- The load of `F[h]` (`h = r2782`) into `r2786`. -/
def blL : Stmt := block [.addN 2786 2779 2782, .loadN 2786 2786]

/-- `OUT[X[h]] := R[h]`. -/
def blS : Stmt := block [.addN 2787 2780 2782, .loadN 2787 2787, .addN 2787 2777 2787,
  .addN 2788 2781 2782, .loadN 2788 2788, .storeN 2787 2788]

/-- One step of the scatter. -/
def blB : Stmt := .seq blL (.seq (.ifLtN 2783 2786 blS .skip) (block [.addN 2782 2782 2784]))

/-- **The scatter of values** (`r2776 = m'`, `r2777 = Kb`, `r2778 = m`, `r2779 = Fb`,
`r2780 = Xb`, `r2781 = Rb`). -/
def blProg : Stmt :=
  .seq (block [.constN 2782 0, .constN 2783 0, .constN 2784 1]) <|
  .seq (.whileLtN 2782 2776 blZ) <|
  .seq (block [.constN 2782 0]) (.whileLtN 2782 2778 blB)

theorem blProg_natOnly : Klein.natOnly blProg = true := by kernel_rfl

/-- The value of the scatter after `i` steps. -/
def blV (mem : ℕ → ℕ) (Fb Xb Rb : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | i + 1, j => if mem (Fb + i) ≠ 0 ∧ mem (Xb + i) = j then mem (Rb + i) else
      blV mem Fb Xb Rb i j

theorem blZ_exec (c : Config) (hc : WordsBounded W c) {Kb i : ℕ} (r77 : c.nreg 2777 = Kb)
    (r82 : c.nreg 2782 = i) (r83 : c.nreg 2783 = 0) (r84 : c.nreg 2784 = 1) (w1 : Kb + i ≤ W)
    (w2 : i + 1 ≤ W) :
    ∃ c' k, Exec P W blZ c c' k ∧ k = 3 ∧ c'.nmem = upd c.nmem (Kb + i) 0 ∧
      c'.nreg 2782 = i + 1 ∧ (∀ r, r ≠ 2782 → r ≠ 2785 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold blZ
  exec_block
  all_goals try ((try config_simp); (try simp only [r77, r82, r83, r84]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r77, r82, r83]
  · config_simp; simp only [r82, r84]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem blB_exec (c : Config) (hc : WordsBounded W c) {Kb Fb Xb Rb m' h : ℕ}
    (r77 : c.nreg 2777 = Kb) (r82 : c.nreg 2782 = h) (r83 : c.nreg 2783 = 0)
    (r84 : c.nreg 2784 = 1) (r79 : c.nreg 2779 = Fb) (r80 : c.nreg 2780 = Xb)
    (r81 : c.nreg 2781 = Rb)
    (w1 : Fb + h ≤ W) (w2 : Xb + h ≤ W) (w3 : h + 1 ≤ W) (w4 : Kb + m' ≤ W) (w5 : Rb + h ≤ W)
    (hX : c.nmem (Fb + h) ≠ 0 → c.nmem (Xb + h) < m') :
    ∃ c' k, Exec P W blB c c' k ∧ k ≤ 12 ∧
      c'.nmem = (if c.nmem (Fb + h) ≠ 0 then upd c.nmem (Kb + c.nmem (Xb + h))
        (c.nmem (Rb + h)) else c.nmem) ∧
      c'.nreg 2782 = h + 1 ∧
      (∀ r, r ≠ 2782 → r ≠ 2786 → r ≠ 2787 → r ≠ 2788 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold blB
  obtain ⟨c₁, k₁, e₁, hk₁, g86, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁, Exec P W blL c c₁ k₁ ∧
      k₁ = 2 ∧ c₁.nreg 2786 = c.nmem (Fb + h) ∧ (∀ r, r ≠ 2786 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold blL
    exec_block
    all_goals try ((try config_simp); (try simp only [r82, r79]); omega)
    refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [r82, r79]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  obtain ⟨c₂, k₂, e₂, hk₂, gm₂, gn₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
      Exec P W (.ifLtN 2783 2786 blS .skip) c₁ c₂ k₂ ∧ k₂ ≤ 7 ∧
      c₂.nmem = (if c.nmem (Fb + h) ≠ 0 then upd c.nmem (Kb + c.nmem (Xb + h))
        (c.nmem (Rb + h)) else c.nmem) ∧ (∀ r, r ≠ 2787 → r ≠ 2788 → c₂.nreg r = c₁.nreg r) ∧
      c₂.rreg = c.rreg ∧ c₂.rmem = c.rmem ∧ c₂.output = c.output := by
    by_cases hf : c.nmem (Fb + h) ≠ 0
    · have hlt : c₁.nreg 2783 < c₁.nreg 2786 := by
        rw [gn₁ 2783 (by omega), r83, g86]; omega
      obtain ⟨c₃, k₃, e₃, hk₃, h3m, h3n, h3r, h3rm, h3o⟩ : ∃ c₃ k₃, Exec P W blS c₁ c₃ k₃ ∧
          k₃ = 6 ∧ c₃.nmem = upd c.nmem (Kb + c.nmem (Xb + h)) (c.nmem (Rb + h)) ∧
          (∀ r, r ≠ 2787 → r ≠ 2788 → c₃.nreg r = c₁.nreg r) ∧ c₃.rreg = c.rreg ∧
          c₃.rmem = c.rmem ∧ c₃.output = c.output := by
        have := hX hf
        have q77 : c₁.nreg 2777 = Kb := by rw [gn₁ _ (by omega), r77]
        have q82 : c₁.nreg 2782 = h := by rw [gn₁ _ (by omega), r82]
        have q80 : c₁.nreg 2780 = Xb := by rw [gn₁ _ (by omega), r80]
        have q81 : c₁.nreg 2781 = Rb := by rw [gn₁ _ (by omega), r81]
        have hw₁ := e₁.wb_right
        unfold blS
        exec_block
        all_goals try ((try config_simp); (try simp only [q77, q82, q80, q81, gm₁]); omega)
        refine ⟨rfl, ?_, fun r h1 h2 => ?_, by rw [gr₁], by rw [grm₁], by rw [go₁]⟩
        · config_simp; simp only [q77, q82, q80, q81, gm₁]
        · config_simp; simp only [upd_apply]; split_ifs <;> omega
      exact ⟨c₃, k₃ + 1, .ifLtN_true hlt e₃, by omega,
        by rw [h3m, ite_eq_left_of_eq_true _ _ (eq_true hf)], h3n, h3r, h3rm, h3o⟩
    · have hlt : ¬ c₁.nreg 2783 < c₁.nreg 2786 := by
        rw [gn₁ 2783 (by omega), r83, g86]; try omega
      exact ⟨c₁, 0 + 2, .ifLtN_false hlt (.skip e₁.wb_right), by omega,
        by rw [gm₁, ite_eq_right_of_eq_false _ _ (eq_false hf)], fun _ _ _ => rfl, gr₁, grm₁,
        go₁⟩
  have hw₂ := e₂.wb_right
  have q82 : c₂.nreg 2782 = h := by rw [gn₂ _ (by omega) (by omega), gn₁ _ (by omega), r82]
  have q84 : c₂.nreg 2784 = 1 := by rw [gn₂ _ (by omega) (by omega), gn₁ _ (by omega), r84]
  obtain ⟨c₃, k₃, e₃, hk₃, h82, hn₃, hm₃, hr₃, hrm₃, ho₃⟩ : ∃ c₃ k₃,
      Exec P W (block [.addN 2782 2782 2784]) c₂ c₃ k₃ ∧ k₃ = 1 ∧ c₃.nreg 2782 = h + 1 ∧
      (∀ r, r ≠ 2782 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [q82, q84]); omega)
    refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [q82, q84]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, by rw [hm₃, gm₂], h82,
    fun r h1 h2 h3 h4 => ?_, by rw [hr₃, gr₂], by rw [hrm₃, grm₂], by rw [ho₃, go₂]⟩
  rw [hn₃ r h1, gn₂ r h3 h4, gn₁ r h2]

/-- **The scatter of values on the machine** (see the module docstring). -/
theorem blProg_exec {m' m Kb Fb Xb Rb : ℕ} (c : Config) (hc : WordsBounded W c)
    (r76 : c.nreg 2776 = m') (r77 : c.nreg 2777 = Kb) (r78 : c.nreg 2778 = m)
    (r79 : c.nreg 2779 = Fb) (r80 : c.nreg 2780 = Xb) (r81 : c.nreg 2781 = Rb) (h1 : 1 ≤ W)
    (wK : Kb + m' ≤ W) (wF : Fb + m ≤ W) (wX : Xb + m ≤ W) (wR : Rb + m ≤ W)
    (dF : Kb + m' ≤ Fb ∨ Fb + m ≤ Kb) (dX : Kb + m' ≤ Xb ∨ Xb + m ≤ Kb)
    (dR : Kb + m' ≤ Rb ∨ Rb + m ≤ Kb)
    (hX : ∀ h < m, c.nmem (Fb + h) ≠ 0 → c.nmem (Xb + h) < m') :
    ∃ c' k, Exec P W blProg c c' k ∧ k ≤ 5 * m' + 14 * m + 10 ∧
      (∀ j < m', c'.nmem (Kb + j) = blV c.nmem Fb Xb Rb m j) ∧
      (∀ a, (a < Kb ∨ Kb + m' ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2776 ∨ 2788 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold blProg
  obtain ⟨c₁, k₁, e₁, hk₁, g82, g83, g84, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 2782 0, .constN 2783 0, .constN 2784 1]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 2782 = 0 ∧ c₁.nreg 2783 = 0 ∧ c₁.nreg 2784 = 1 ∧
      (∀ r, r ≠ 2782 → r ≠ 2783 → r ≠ 2784 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, fun r a b d => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  -- the zeros
  let J₁ : ℕ → Config → Prop := fun i c' =>
    (∀ j < i, c'.nmem (Kb + j) = 0) ∧ (∀ a, (a < Kb ∨ Kb + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 2782 → r ≠ 2783 → r ≠ 2784 → r ≠ 2785 → c'.nreg r = c.nreg r) ∧
      c'.nreg 2783 = 0 ∧ c'.nreg 2784 = 1 ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, hJ₁⟩ := forLoop_exec (P := P) (a := 2782) (bR := 2776)
    (body := blZ) J₁ (K := 3) (n := m') c₁ e₁.wb_right g82
    (by rw [gn₁ _ (by omega) (by omega) (by omega)]; exact r76)
    ⟨fun j hj => absurd hj (by omega), fun a _ => by rw [gm₁], fun r a b d _ => gn₁ r a b d,
      g83, g84, gr₁, grm₁, go₁⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j3, j83, j84, jr, jrm, jo⟩ := hJ
      obtain ⟨c'', k, ex, hk, hm, h82, hn, hr, hrm, ho⟩ := blZ_exec (P := P) (Kb := Kb) (i := i)
        c' hw (by rw [j3 2777 (by omega) (by omega) (by omega) (by omega)]; exact r77) ha j83
        j84 (by omega) (by omega)
      refine ⟨c'', k, ex, by omega, h82, by rw [hn 2776 (by omega) (by omega)]; exact hb,
        fun j hj => ?_, fun a h => ?_, fun r a b d e => by rw [hn r a e]; exact j3 r a b d e,
        by rw [hn _ (by omega) (by omega)]; exact j83,
        by rw [hn _ (by omega) (by omega)]; exact j84, by rw [hr, jr], by rw [hrm, jrm],
        by rw [ho, jo]⟩
      · rw [hm, upd_apply]
        split_ifs with he
        · rfl
        · exact j1 j (by omega)
      · rw [hm, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact j2 a (by omega))
  obtain ⟨z1, z2, z3, z83, z84, zr, zrm, zo⟩ := hJ₁
  -- the scatter
  obtain ⟨c₃, k₃, e₃, hk₃, h82, hn₃, hm₃, hr₃, hrm₃, ho₃⟩ : ∃ c₃ k₃,
      Exec P W (block [.constN 2782 0]) c₂ c₃ k₃ ∧ k₃ = 1 ∧ c₃.nreg 2782 = 0 ∧
      (∀ r, r ≠ 2782 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  let J₂ : ℕ → Config → Prop := fun h c' =>
    (∀ j < m', c'.nmem (Kb + j) = blV c.nmem Fb Xb Rb h j) ∧
      (∀ a, (a < Kb ∨ Kb + m' ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2776 ∨ 2788 < r ∨ r = 2777 ∨ r = 2778 ∨ r = 2779 ∨ r = 2780 ∨ r = 2781) →
        c'.nreg r = c.nreg r) ∧
      c'.nreg 2783 = 0 ∧ c'.nreg 2784 = 1 ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output
  obtain ⟨c₄, k₄, e₄, hk₄, -, hJ₂⟩ := forLoop_exec (P := P) (a := 2782) (bR := 2778)
    (body := blB) J₂ (K := 12) (n := m) c₃ e₃.wb_right h82
    (by rw [hn₃ _ (by omega), z3 _ (by omega) (by omega) (by omega) (by omega)]; exact r78)
    ⟨fun j hj => by rw [hm₃, z1 j hj]; rfl,
      fun a h => by rw [hm₃]; exact z2 a (by omega),
      fun r h => by rw [hn₃ r (by omega)]; exact z3 r (by omega) (by omega) (by omega) (by omega),
      by rw [hn₃ _ (by omega)]; exact z83, by rw [hn₃ _ (by omega)]; exact z84,
      by rw [hr₃, zr], by rw [hrm₃, zrm], by rw [ho₃, zo]⟩
    (fun h c' hh hw ha hb hJ => by
      obtain ⟨j1, j2, j3, j83, j84, jr, jrm, jo⟩ := hJ
      have eF : c'.nmem (Fb + h) = c.nmem (Fb + h) := j2 _ (by omega)
      have eX : c'.nmem (Xb + h) = c.nmem (Xb + h) := j2 _ (by omega)
      have eR : c'.nmem (Rb + h) = c.nmem (Rb + h) := j2 _ (by omega)
      obtain ⟨c'', k, ex, hk, hm, h82', hn, hr, hrm, ho⟩ := blB_exec (P := P) (m' := m')
        (Kb := Kb) (Fb := Fb) (Xb := Xb) (Rb := Rb) (h := h) c' hw
        (by rw [j3 2777 (by omega)]; exact r77) ha j83 j84
        (by rw [j3 2779 (by omega)]; exact r79) (by rw [j3 2780 (by omega)]; exact r80)
        (by rw [j3 2781 (by omega)]; exact r81) (by omega) (by omega) (by omega) wK (by omega)
        (fun hf => by rw [eX]; rw [eF] at hf; exact hX h hh hf)
      refine ⟨c'', k, ex, hk, h82',
        by rw [hn 2778 (by omega) (by omega) (by omega) (by omega)]; exact hb,
        fun j hj => ?_, fun a ha' => ?_, fun r hr' => by
          rw [hn r (by omega) (by omega) (by omega) (by omega)]; exact j3 r hr',
        by rw [hn _ (by omega) (by omega) (by omega) (by omega)]; exact j83,
        by rw [hn _ (by omega) (by omega) (by omega) (by omega)]; exact j84,
        by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩
      · rw [hm, eF, eX, eR]
        show _ = if c.nmem (Fb + h) ≠ 0 ∧ c.nmem (Xb + h) = j then c.nmem (Rb + h) else
          blV c.nmem Fb Xb Rb h j
        by_cases hf : c.nmem (Fb + h) ≠ 0
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hf), upd_apply]
          by_cases hj' : c.nmem (Xb + h) = j
          · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
              ite_eq_left_of_eq_true _ _ (eq_true ⟨hf, hj'⟩)]
          · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
              ite_eq_right_of_eq_false _ _ (eq_false (fun h' => hj' h'.2)), j1 j hj]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hf),
            ite_eq_right_of_eq_false _ _ (eq_false (fun h' => hf h'.1)), j1 j hj]
      · rw [hm, eF]
        by_cases hf : c.nmem (Fb + h) ≠ 0
        · have := hX h hh hf
          rw [ite_eq_left_of_eq_true _ _ (eq_true hf), upd_apply, eX,
            ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
          exact j2 a ha'
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hf)]; exact j2 a ha')
  obtain ⟨j1, j2, j3, -, -, jr, jrm, jo⟩ := hJ₂
  exact ⟨c₄, k₁ + (k₂ + (k₃ + k₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, j1, j2,
    fun r h => j3 r (by omega), jr, jrm, jo⟩

/-- The scatter at a target hit by exactly one flagged index. -/
theorem blV_unique {mem : ℕ → ℕ} {Fb Xb Rb j h : ℕ} :
    ∀ i, h < i → (mem (Fb + h) ≠ 0 ∧ mem (Xb + h) = j) →
      (∀ h' < i, mem (Fb + h') ≠ 0 ∧ mem (Xb + h') = j → h' = h) →
      blV mem Fb Xb Rb i j = mem (Rb + h)
  | 0, hi, _, _ => absurd hi (by omega)
  | i + 1, hi, hh, hu => by
    simp only [blV]
    by_cases hc : mem (Fb + i) ≠ 0 ∧ mem (Xb + i) = j
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), hu i (by omega) hc]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact blV_unique i hi hh (fun h' hh' hc' => hu h' (by omega) hc')
      · exact absurd hh hc

/-! ### The meaning: the lengths `hLP` of `sdWalk_exec` -/

section Sem

open Orbit CombMap BKMNW PlanarSeparator

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {N : CombMap D V F}

open Classical in
/-- **The lengths read back along the numbering `δ`**: `R[h]` at the dart `δ h` (`h < m`), `0`
elsewhere. -/
noncomputable def blLen (mem : ℕ → ℕ) (Rb m : ℕ) (δ : ℕ → D) (d : D) : ℤ :=
  if h : ∃ i < m, δ i = d then (mem (Rb + h.choose) : ℤ) else 0

/-- `blLen` at a dart reached by `δ`. -/
theorem blLen_of {mem : ℕ → ℕ} {Rb m : ℕ} {δ : ℕ → D} {d : D} (ex : ∃ i < m, δ i = d) :
    blLen mem Rb m δ d = (mem (Rb + ex.choose) : ℤ) := by
  unfold blLen
  simp only [ex, ↓reduceDIte]

/-- `blLen` at a dart `δ h` with `R[h] = f (δ h)`. -/
theorem blLen_eq {mem : ℕ → ℕ} {Rb m : ℕ} {δ : ℕ → D}
    {f : D → ℤ} (hR : ∀ h < m, (mem (Rb + h) : ℤ) = f (δ h)) {h : ℕ} (hh : h < m) :
    blLen mem Rb m δ (δ h) = f (δ h) := by
  have ex : ∃ i < m, δ i = δ h := ⟨h, hh, rfl⟩
  rw [blLen_of ex]
  obtain ⟨h1, h2⟩ := ex.choose_spec
  rw [hR _ h1, h2]

/-- **The scattered lengths are those of `hLP`** (`sdWalk_exec`) for the lengths `blLen`. -/
theorem bl_hLP {Pc K : Finset D} {m k m' : ℕ} {δ : ℕ → D} {α σ : ℕ → ℕ}
    (he : PEnc N Pc m k δ α σ) (hKP : K ⊆ Pc) (cn : SDart (rcl N K) ≃ Fin m')
    {mem : ℕ → ℕ} {Fb Xb Rb : ℕ}
    (hXm : ∀ h < k, ∀ hm : δ h ∈ rcl N K, mem (Xb + h) = cn ⟨δ h, hm⟩)
    (hFm : ∀ x < m, (mem (Fb + x) ≠ 0 ↔ δ x ∈ K)) (x : SDart (rcl N K)) (hx : x.1 ∈ K) :
    blV mem Fb Xb Rb m (cn x) = (blLen mem Rb m δ x.1).toNat := by
  obtain ⟨h, hh, hδ⟩ := he.enumP.surj _ (hKP hx)
  have hk : h < k := by have := he.mle; omega
  have hc : mem (Fb + h) ≠ 0 ∧ mem (Xb + h) = cn x := by
    refine ⟨(hFm h hh).2 (by rw [hδ]; exact hx), ?_⟩
    rw [hXm h hk (by rw [hδ]; exact x.2)]
    congr 2
    exact Subtype.ext hδ
  rw [blV_unique m hh hc (fun h' hh' hc' => ?_)]
  · have ex : ∃ i < m, δ i = x.1 := ⟨h, hh, hδ⟩
    rw [blLen_of ex, Int.toNat_natCast]
    have e2 := ex.choose_spec
    rw [he.enumP.inj _ e2.1 h hh (e2.2.trans hδ.symm)]
  · have hK' := (hFm h' hh').1 hc'.1
    have hk' : h' < k := by have := he.mle; omega
    rw [hXm h' hk' (subset_rcl K hK')] at hc'
    have e1 := cn.injective (Fin.ext hc'.2)
    have e2 : δ h' = δ h := by rw [hδ]; exact congrArg Subtype.val e1
    exact he.enumP.inj h' hh' h hh e2

end Sem

/-- **The lengths of an instance depend only on the lengths on its darts.** -/
theorem faceLen_congr {D DQ : Type u} [DecidableEq DQ] {P' : Finset D} {e : D → DQ}
    {ℓ ℓ' : D → ℤ} (h : ∀ d ∈ P', ℓ' d = ℓ d) : faceLen P' e ℓ' = faceLen P' e ℓ := by
  funext x
  unfold faceLen
  split_ifs with hx
  · rw [h _ hx.choose_spec.1]
  · rfl

end NegSSSP

end PlanarFlow
