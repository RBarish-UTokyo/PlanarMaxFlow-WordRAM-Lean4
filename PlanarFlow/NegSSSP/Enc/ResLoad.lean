module

public import PlanarFlow.NegSSSP.Enc.BlScat
public import PlanarFlow.NegSSSP.NodeNatN

/-!
# Integers of a frame as residues, and back (the node's input and output)

The frames of the driver hold integers (lengths, potentials) as natural words in the **offset
encoding** `z ↦ (z + L).toNat` (`|z| ≤ L`, one global `L`). The node reads residues modulo its
modulus `M` (`Sim`), and its outcome is read back by `sgnD H M v` (`v` the residue).

* `ldProg` (registers `2840 … 2850`): `OUT[i] := (IN[J[i]] + (M − L mod M)) mod M` for `i < n`,
  a gather through an index array `J`. **`ldProg_exec`**: within `11 n + 6` steps; **`ld_val`**:
  if `IN[J[i]] = (z + L).toNat` with `0 ≤ z + L` then `OUT[i] ≡ z (mod M)`, i.e.
  `(OUT[i] : ℤ) = z % M` (the form of the residue hypotheses of `node_exec_fixedD`).
* `wbProg` (registers `2860 … 2870`): `OUT[i] := v + L` if `v ≤ H`, `v + L − M` otherwise
  (`v = IN[i]`), for `i < n`. **`wbProg_exec`**: within `12 n + 5` steps; **`wb_val`**: if the
  integer `f` is read back from `v` (`(f : ℝ) = sgnD H M v`) and `0 ≤ f + L`, then
  `OUT[i] = (f + L).toNat`: the offset encoding of the node's outcome.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-! ### Offsets to residues -/

/-- One residue (`i = r2847`). -/
def ldBody : Stmt :=
  block [.addN 2849 2842 2847, .loadN 2849 2849, .addN 2849 2841 2849, .loadN 2849 2849,
    .addN 2849 2849 2846, .modN 2849 2849 2844, .addN 2850 2843 2847, .storeN 2850 2849,
    .addN 2847 2847 2848]

/-- **Offsets to residues** (`r2840 = n`, `r2841 = INb`, `r2842 = Jb`, `r2843 = OUTb`,
`r2844 = M`, `r2845 = L`). -/
def ldProg : Stmt :=
  .seq (block [.constN 2847 0, .constN 2848 1, .modN 2846 2845 2844, .subN 2846 2844 2846])
    (.whileLtN 2847 2840 ldBody)

theorem ldProg_natOnly : Klein.natOnly ldProg = true := by kernel_rfl

/-- The value written by `ldProg`. -/
def ldV (mem : ℕ → ℕ) (INb Jb M L i : ℕ) : ℕ := (mem (INb + mem (Jb + i)) + (M - L % M)) % M

/-- **The meaning of a loaded residue.** -/
theorem ld_val {M L u : ℕ} {z : ℤ} (hM : 0 < M) (hu : (u : ℤ) = z + L) :
    (((u + (M - L % M)) % M : ℕ) : ℤ) = z % M := by
  have hLM : L % M < M := Nat.mod_lt _ hM
  rw [Int.natCast_mod, Nat.cast_add, Nat.cast_sub hLM.le, hu]
  have e : z + (L : ℤ) + ((M : ℤ) - ((L % M : ℕ) : ℤ)) = z + (M : ℤ) * (L / M + 1 : ℕ) := by
    have := Nat.mod_add_div L M
    push_cast
    have h2 : ((L % M : ℕ) : ℤ) + (M : ℤ) * ((L / M : ℕ) : ℤ) = L := by exact_mod_cast this
    push_cast at h2
    linarith
  rw [e, Int.add_mul_emod_self_left]

theorem ldBody_exec (c : Config) (hc : WordsBounded W c) {INb Jb Ob M c0 i : ℕ}
    (r41 : c.nreg 2841 = INb) (r42 : c.nreg 2842 = Jb) (r43 : c.nreg 2843 = Ob)
    (r44 : c.nreg 2844 = M) (r46 : c.nreg 2846 = c0) (r47 : c.nreg 2847 = i)
    (r48 : c.nreg 2848 = 1) (hM : 0 < M)
    (w1 : Jb + i ≤ W) (w2 : INb + c.nmem (Jb + i) ≤ W)
    (w3 : c.nmem (INb + c.nmem (Jb + i)) + c0 ≤ W) (w4 : Ob + i ≤ W) (w5 : i + 1 ≤ W) :
    ∃ c' k, Exec P W ldBody c c' k ∧ k = 9 ∧
      c'.nmem = upd c.nmem (Ob + i) ((c.nmem (INb + c.nmem (Jb + i)) + c0) % M) ∧
      c'.nreg 2847 = i + 1 ∧
      (∀ r, r ≠ 2847 → r ≠ 2849 → r ≠ 2850 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ldBody
  exec_block
  all_goals try ((try config_simp); (try simp only [r41, r42, r43, r44, r46, r47, r48]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r41, r42, r43, r44, r46, r47]
  · config_simp; simp only [r47, r48]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **Offsets to residues on the machine** (see the module docstring). -/
theorem ldProg_exec {n INb Jb Ob M L : ℕ} (c : Config) (hc : WordsBounded W c)
    (r40 : c.nreg 2840 = n) (r41 : c.nreg 2841 = INb) (r42 : c.nreg 2842 = Jb)
    (r43 : c.nreg 2843 = Ob) (r44 : c.nreg 2844 = M) (r45 : c.nreg 2845 = L) (hM : 0 < M)
    (h1 : 1 ≤ W) (wJ : Jb + n ≤ W) (wO : Ob + n ≤ W)
    (dJ : Ob + n ≤ Jb ∨ Jb + n ≤ Ob)
    (hI : ∀ i < n, INb + c.nmem (Jb + i) ≤ W ∧
      (INb + c.nmem (Jb + i) < Ob ∨ Ob + n ≤ INb + c.nmem (Jb + i)) ∧
      c.nmem (INb + c.nmem (Jb + i)) + M ≤ W) :
    ∃ c' k, Exec P W ldProg c c' k ∧ k ≤ 11 * n + 6 ∧
      (∀ i < n, c'.nmem (Ob + i) = ldV c.nmem INb Jb M L i) ∧
      (∀ a, (a < Ob ∨ Ob + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2840 ∨ 2850 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hMW : M ≤ W := by
    rcases Nat.eq_zero_or_pos n with h | h
    · have := hc.2 0; have := hc.1 2844; omega
    · have := (hI 0 h).2.2; omega
  unfold ldProg
  obtain ⟨c₁, k₁, e₁, hk₁, g46, g47, g48, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 2847 0, .constN 2848 1, .modN 2846 2845 2844,
        .subN 2846 2844 2846]) c c₁ k₁ ∧ k₁ = 4 ∧
      c₁.nreg 2846 = M - L % M ∧ c₁.nreg 2847 = 0 ∧ c₁.nreg 2848 = 1 ∧
      (∀ r, r ≠ 2846 → r ≠ 2847 → r ≠ 2848 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    have := hc.1 2845
    have hLM := Nat.mod_le L M
    exec_block
    all_goals try ((try config_simp); (try simp only [r44, r45]); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r44, r45])
    simp only [upd_apply]; split_ifs <;> omega
  have hc0 : M - L % M ≤ M := Nat.sub_le _ _
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ e < i, c'.nmem (Ob + e) = ldV c.nmem INb Jb M L e) ∧
      (∀ a, (a < Ob ∨ Ob + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2840 ∨ 2850 < r) → c'.nreg r = c.nreg r) ∧
      c'.nreg 2841 = INb ∧ c'.nreg 2842 = Jb ∧ c'.nreg 2843 = Ob ∧ c'.nreg 2844 = M ∧
      c'.nreg 2846 = M - L % M ∧ c'.nreg 2848 = 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  have k1 : ∀ r, (r < 2846 ∨ 2848 < r) → c₁.nreg r = c.nreg r := fun r h =>
    gn₁ r (by omega) (by omega) (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2847) (bR := 2840)
    (body := ldBody) J (K := 9) (n := n) c₁ e₁.wb_right g47
    (by rw [k1 2840 (by omega)]; exact r40)
    ⟨fun e he => absurd he (by omega), fun a _ => by rw [gm₁], fun r hr => k1 r (by omega),
      by rw [k1 _ (by omega)]; exact r41, by rw [k1 _ (by omega)]; exact r42,
      by rw [k1 _ (by omega)]; exact r43, by rw [k1 _ (by omega)]; exact r44, g46, g48,
      gr₁, grm₁, go₁⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j3, j41, j42, j43, j44, j46, j48, jr, jrm, jo⟩ := hJ
      obtain ⟨t1, t2, t3⟩ := hI i hi
      have eJ : c'.nmem (Jb + i) = c.nmem (Jb + i) := j2 _ (by omega)
      have eI : c'.nmem (INb + c.nmem (Jb + i)) = c.nmem (INb + c.nmem (Jb + i)) :=
        j2 _ (by omega)
      obtain ⟨c'', k, ex, hk, hm, h47, hn, hr, hrm, ho⟩ := ldBody_exec (P := P) c' hw j41 j42 j43
        j44 j46 ha j48 hM (by omega) (by rw [eJ]; omega) (by rw [eJ, eI]; omega) (by omega)
        (by omega)
      refine ⟨c'', k, ex, by omega, h47,
        by rw [hn 2840 (by omega) (by omega) (by omega)]; exact hb, fun e he => ?_,
        fun a h => ?_, fun r hr' => ?_,
        by rw [hn 2841 (by omega) (by omega) (by omega)]; exact j41,
        by rw [hn 2842 (by omega) (by omega) (by omega)]; exact j42,
        by rw [hn 2843 (by omega) (by omega) (by omega)]; exact j43,
        by rw [hn 2844 (by omega) (by omega) (by omega)]; exact j44,
        by rw [hn 2846 (by omega) (by omega) (by omega)]; exact j46,
        by rw [hn 2848 (by omega) (by omega) (by omega)]; exact j48,
        by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩
      · rw [hm, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact j1 e he
        · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), eJ, eI]; rfl
      · rw [hm, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact j2 a (by omega)
      · rw [hn r (by omega) (by omega) (by omega)]; exact j3 r hr')
  obtain ⟨j1, j2, j3, -, -, -, -, -, -, jr, jrm, jo⟩ := hJ
  exact ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by omega, j1, j2, j3, jr, jrm, jo⟩

/-! ### Residues to offsets (the write-back) -/

/-- `v + L`, minus `M` if `H < v` (`i = r2866`, `H + L` in `r2870`). -/
def wbBody : Stmt :=
  .seq (block [.addN 2868 2861 2866, .loadN 2868 2868, .addN 2868 2868 2865]) <|
  .seq (.ifLtN 2870 2868 (block [.subN 2868 2868 2863]) .skip) <|
  block [.addN 2869 2862 2866, .storeN 2869 2868, .addN 2866 2866 2867]

/-- **Residues to offsets** (`r2860 = n`, `r2861 = INb`, `r2862 = OUTb`, `r2863 = M`,
`r2864 = H`, `r2865 = L`). -/
def wbProg : Stmt :=
  .seq (block [.constN 2866 0, .constN 2867 1, .addN 2870 2864 2865])
    (.whileLtN 2866 2860 wbBody)

theorem wbProg_natOnly : Klein.natOnly wbProg = true := by kernel_rfl

/-- The value written by `wbProg`. -/
def wbV (H M L v : ℕ) : ℕ := if H < v then v + L - M else v + L

/-- **The meaning of a written-back value**: the offset encoding of the integer read back. -/
theorem wb_val {H M L v : ℕ} {f : ℤ} (hf : (f : ℝ) = sgnD H M v) (hfL : 0 ≤ f + L) :
    wbV H M L v = (f + L).toNat := by
  unfold sgnD at hf
  unfold wbV
  by_cases h : v ≤ H
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at hf
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    have e : f = v := by exact_mod_cast hf
    omega
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h)] at hf
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    have e : f = (v : ℤ) - M := by
      exact_mod_cast (show (f : ℝ) = (((v : ℤ) - M : ℤ) : ℝ) by push_cast; linarith)
    omega

theorem wbBody_exec (c : Config) (hc : WordsBounded W c) {INb Ob M H L i : ℕ}
    (r61 : c.nreg 2861 = INb) (r62 : c.nreg 2862 = Ob) (r63 : c.nreg 2863 = M)
    (r65 : c.nreg 2865 = L) (r66 : c.nreg 2866 = i) (r67 : c.nreg 2867 = 1)
    (r70 : c.nreg 2870 = H + L)
    (w1 : INb + i ≤ W) (w2 : c.nmem (INb + i) + L ≤ W) (w4 : Ob + i ≤ W) (w5 : i + 1 ≤ W) :
    ∃ c' k, Exec P W wbBody c c' k ∧ k ≤ 8 ∧
      c'.nmem = upd c.nmem (Ob + i) (wbV H M L (c.nmem (INb + i))) ∧
      c'.nreg 2866 = i + 1 ∧
      (∀ r, r ≠ 2866 → r ≠ 2868 → r ≠ 2869 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold wbBody
  obtain ⟨c₁, k₁, e₁, hk₁, g68, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.addN 2868 2861 2866, .loadN 2868 2868, .addN 2868 2868 2865]) c c₁ k₁ ∧
      k₁ = 3 ∧ c₁.nreg 2868 = c.nmem (INb + i) + L ∧ (∀ r, r ≠ 2868 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [r61, r65, r66]); omega)
    refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [r61, r65, r66]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  obtain ⟨c₂, k₂, e₂, hk₂, g68', gn₂, gm₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
      Exec P W (.ifLtN 2870 2868 (block [.subN 2868 2868 2863]) .skip) c₁ c₂ k₂ ∧ k₂ ≤ 2 ∧
      c₂.nreg 2868 = wbV H M L (c.nmem (INb + i)) ∧ (∀ r, r ≠ 2868 → c₂.nreg r = c₁.nreg r) ∧
      c₂.nmem = c.nmem ∧ c₂.rreg = c.rreg ∧ c₂.rmem = c.rmem ∧ c₂.output = c.output := by
    have q70 : c₁.nreg 2870 = H + L := by rw [gn₁ _ (by omega), r70]
    have q63 : c₁.nreg 2863 = M := by rw [gn₁ _ (by omega), r63]
    by_cases hv : H < c.nmem (INb + i)
    · have hlt : c₁.nreg 2870 < c₁.nreg 2868 := by rw [q70, g68]; omega
      have hw₁ := e₁.wb_right
      obtain ⟨c₃, k₃, e₃, hk₃, h68, hn₃, hm₃, hr₃, hrm₃, ho₃⟩ : ∃ c₃ k₃,
          Exec P W (block [.subN 2868 2868 2863]) c₁ c₃ k₃ ∧ k₃ = 1 ∧
          c₃.nreg 2868 = c.nmem (INb + i) + L - M ∧ (∀ r, r ≠ 2868 → c₃.nreg r = c₁.nreg r) ∧
          c₃.nmem = c₁.nmem ∧ c₃.rreg = c₁.rreg ∧ c₃.rmem = c₁.rmem ∧ c₃.output = c₁.output := by
        exec_block
        all_goals try ((try config_simp); (try simp only [g68, q63]); omega)
        refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp; simp only [g68, q63]
        · config_simp; simp only [upd_apply]; split_ifs <;> omega
      refine ⟨c₃, k₃ + 1, .ifLtN_true hlt e₃, by omega, ?_, hn₃, by rw [hm₃, gm₁],
        by rw [hr₃, gr₁], by rw [hrm₃, grm₁], by rw [ho₃, go₁]⟩
      rw [h68]; unfold wbV; rw [ite_eq_left_of_eq_true _ _ (eq_true hv)]
    · have hlt : ¬ c₁.nreg 2870 < c₁.nreg 2868 := by rw [q70, g68]; omega
      refine ⟨c₁, 0 + 2, .ifLtN_false hlt (.skip e₁.wb_right), by omega, ?_, fun _ _ => rfl,
        gm₁, gr₁, grm₁, go₁⟩
      rw [g68]; unfold wbV; rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
  have hw₂ := e₂.wb_right
  have q62 : c₂.nreg 2862 = Ob := by rw [gn₂ _ (by omega), gn₁ _ (by omega), r62]
  have q66 : c₂.nreg 2866 = i := by rw [gn₂ _ (by omega), gn₁ _ (by omega), r66]
  have q67 : c₂.nreg 2867 = 1 := by rw [gn₂ _ (by omega), gn₁ _ (by omega), r67]
  obtain ⟨c₃, k₃, e₃, hk₃, h66, hn₃, hm₃, hr₃, hrm₃, ho₃⟩ : ∃ c₃ k₃,
      Exec P W (block [.addN 2869 2862 2866, .storeN 2869 2868, .addN 2866 2866 2867]) c₂ c₃
        k₃ ∧ k₃ = 3 ∧ c₃.nreg 2866 = i + 1 ∧
      (∀ r, r ≠ 2866 → r ≠ 2869 → c₃.nreg r = c₂.nreg r) ∧
      c₃.nmem = upd c₂.nmem (Ob + i) (wbV H M L (c.nmem (INb + i))) ∧ c₃.rreg = c₂.rreg ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [q62, q66, q67, g68']); omega)
    refine ⟨rfl, ?_, fun r h1 h2 => ?_, ?_, rfl, rfl, rfl⟩
    · config_simp; simp only [q66, q67]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
    · config_simp; simp only [q62, q66, g68']
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, by rw [hm₃, gm₂], h66,
    fun r h1 h2 h3 => ?_, by rw [hr₃, gr₂], by rw [hrm₃, grm₂], by rw [ho₃, go₂]⟩
  rw [hn₃ r h1 h3, gn₂ r h2, gn₁ r h2]

/-- **Residues to offsets on the machine** (see the module docstring). -/
theorem wbProg_exec {n INb Ob M H L : ℕ} (c : Config) (hc : WordsBounded W c)
    (r60 : c.nreg 2860 = n) (r61 : c.nreg 2861 = INb) (r62 : c.nreg 2862 = Ob)
    (r63 : c.nreg 2863 = M) (r64 : c.nreg 2864 = H) (r65 : c.nreg 2865 = L)
    (h1 : 1 ≤ W) (hHL : H + L ≤ W) (wI : INb + n ≤ W) (wO : Ob + n ≤ W)
    (dI : Ob + n ≤ INb ∨ INb + n ≤ Ob) (hv : ∀ i < n, c.nmem (INb + i) + L ≤ W) :
    ∃ c' k, Exec P W wbProg c c' k ∧ k ≤ 10 * n + 5 ∧
      (∀ i < n, c'.nmem (Ob + i) = wbV H M L (c.nmem (INb + i))) ∧
      (∀ a, (a < Ob ∨ Ob + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2860 ∨ 2870 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold wbProg
  obtain ⟨c₁, k₁, e₁, hk₁, g66, g67, g70, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 2866 0, .constN 2867 1, .addN 2870 2864 2865]) c c₁ k₁ ∧
      k₁ = 3 ∧ c₁.nreg 2866 = 0 ∧ c₁.nreg 2867 = 1 ∧ c₁.nreg 2870 = H + L ∧
      (∀ r, r ≠ 2866 → r ≠ 2867 → r ≠ 2870 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [r64, r65]); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r64, r65])
    simp only [upd_apply]; split_ifs <;> omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ e < i, c'.nmem (Ob + e) = wbV H M L (c.nmem (INb + e))) ∧
      (∀ a, (a < Ob ∨ Ob + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2860 ∨ 2870 < r) → c'.nreg r = c.nreg r) ∧
      c'.nreg 2861 = INb ∧ c'.nreg 2862 = Ob ∧ c'.nreg 2863 = M ∧ c'.nreg 2865 = L ∧
      c'.nreg 2867 = 1 ∧ c'.nreg 2870 = H + L ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  have k1 : ∀ r, (r < 2866 ∨ 2870 < r ∨ r = 2868 ∨ r = 2869) → c₁.nreg r = c.nreg r :=
    fun r h => gn₁ r (by omega) (by omega) (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2866) (bR := 2860)
    (body := wbBody) J (K := 8) (n := n) c₁ e₁.wb_right g66
    (by rw [k1 2860 (by omega)]; exact r60)
    ⟨fun e he => absurd he (by omega), fun a _ => by rw [gm₁], fun r hr => k1 r (by omega),
      by rw [k1 _ (by omega)]; exact r61, by rw [k1 _ (by omega)]; exact r62,
      by rw [k1 _ (by omega)]; exact r63, by rw [k1 _ (by omega)]; exact r65, g67, g70,
      gr₁, grm₁, go₁⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j3, j61, j62, j63, j65, j67, j70, jr, jrm, jo⟩ := hJ
      have eI : c'.nmem (INb + i) = c.nmem (INb + i) := j2 _ (by omega)
      obtain ⟨c'', k, ex, hk, hm, h66, hn, hr, hrm, ho⟩ := wbBody_exec (P := P) (H := H) c' hw
        j61 j62 j63 j65 ha j67 j70 (by omega) (by rw [eI]; exact hv i hi) (by omega) (by omega)
      refine ⟨c'', k, ex, hk, h66,
        by rw [hn 2860 (by omega) (by omega) (by omega)]; exact hb, fun e he => ?_,
        fun a h => ?_, fun r hr' => ?_,
        by rw [hn 2861 (by omega) (by omega) (by omega)]; exact j61,
        by rw [hn 2862 (by omega) (by omega) (by omega)]; exact j62,
        by rw [hn 2863 (by omega) (by omega) (by omega)]; exact j63,
        by rw [hn 2865 (by omega) (by omega) (by omega)]; exact j65,
        by rw [hn 2867 (by omega) (by omega) (by omega)]; exact j67,
        by rw [hn 2870 (by omega) (by omega) (by omega)]; exact j70,
        by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩
      · rw [hm, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact j1 e he
        · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), eI]
      · rw [hm, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact j2 a (by omega)
      · rw [hn r (by omega) (by omega) (by omega)]; exact j3 r hr')
  obtain ⟨j1, j2, j3, -, -, -, -, -, -, jr, jrm, jo⟩ := hJ
  exact ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by omega, j1, j2, j3, jr, jrm, jo⟩

end NegSSSP

end PlanarFlow
