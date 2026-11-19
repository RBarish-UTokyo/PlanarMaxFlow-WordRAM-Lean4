module

public import PlanarFlow.NegSSSP.NdRun

/-!
# Small generic programs for the full branch

* **`cpRegs l`**: the register copies `r p.1 := r p.2` for the pairs of `l`; **`cpRegs_exec`**:
  when the targets are distinct and no source is a target (`cpOK`, `cpSrc`, Boolean, for the
  kernel), within `l.length` steps every target holds its source's value; other registers,
  memory, reals, output kept.
* **`idProg`**: `OUT[i] := i` for `i < n` (`r2100 = n`, `r2101 = OUTb`; scratch
  `2102 … 2104`); **`idProg_exec`** (`4 n + 4` steps): the identity array, the gather index of
  `ldProg` for a plain array.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-! ### Register copies -/

/-- The register copies `r p.1 := r p.2`. -/
def cpRegs : List (ℕ × ℕ) → Stmt
  | [] => .skip
  | p :: l => .seq (.instr (.copyN p.1 p.2)) (cpRegs l)

/-- The targets are distinct. -/
def cpOK : List (ℕ × ℕ) → Bool
  | [] => true
  | p :: l => !((l.map (·.1)).contains p.1) && cpOK l

/-- No source is a target. -/
def cpSrc (l : List (ℕ × ℕ)) : Bool := l.all fun p => !((l.map (·.1)).contains p.2)

theorem cpRegs_natOnly (l : List (ℕ × ℕ)) : Klein.natOnly (cpRegs l) = true := by
  induction l with
  | nil => rfl
  | cons p l ih => simp [cpRegs, Klein.natOnly, Instr.isReal, ih]

theorem cpRegs_exec (l : List (ℕ × ℕ)) (hok : cpOK l = true) (hs : cpSrc l = true)
    (c : Config) (hc : WordsBounded W c) :
    ∃ c', Exec P W (cpRegs l) c c' l.length ∧ (∀ p ∈ l, c'.nreg p.1 = c.nreg p.2) ∧
      (∀ r, r ∉ l.map (·.1) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  induction l generalizing c with
  | nil => exact ⟨c, .skip hc, by simp, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | cons p l ih =>
    simp only [cpOK, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hok
    have hs0 : ∀ q ∈ p :: l, q.2 ∉ (p :: l).map (·.1) := by
      simpa [cpSrc] using hs
    have hp2 : p.2 ≠ p.1 := fun h => hs0 p (List.mem_cons_self) (by simp [h])
    have hl : ∀ q ∈ l, q.2 ≠ p.1 ∧ q.2 ∉ l.map (·.1) := fun q hq => by
      have := hs0 q (List.mem_cons_of_mem _ hq)
      simp only [List.map_cons, List.mem_cons, not_or] at this
      exact ⟨this.1, this.2⟩
    have hs' : cpSrc l = true := by
      simp only [cpSrc, List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not]
      intro q hq; exact (hl q hq).2
    have e₁ := Exec.copyN (P := P) hc p.1 p.2
    obtain ⟨c', e₂, h1, h2, h3, h4, h5, h6⟩ := ih hok.2 hs' _ e₁.wb_right
    refine ⟨c', ?_, fun q hq => ?_, fun r hr => ?_, h3, h4, h5, h6⟩
    · have := Exec.seq e₁ e₂
      rw [List.length_cons, Nat.add_comm]; exact this
    · rcases List.mem_cons.1 hq with rfl | hq
      · rw [h2 _ hok.1]; simp [upd_apply]
      · rw [h1 q hq]
        have : q.2 ≠ p.1 := (hl q hq).1
        simp [upd_apply, this]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [h2 r hr.2]; simp [upd_apply, hr.1]

/-! ### The identity array -/

/-- One step: `OUT[i] := i`. -/
def idBody : Stmt := block [.addN 2104 2101 2102, .storeN 2104 2102, .addN 2102 2102 2103]

/-- **The identity array** (`r2100 = n`, `r2101 = OUTb`). -/
def idProg : Stmt :=
  .seq (block [.constN 2102 0, .constN 2103 1]) (.whileLtN 2102 2100 idBody)

theorem idProg_natOnly : Klein.natOnly idProg = true := by kernel_rfl

theorem idProg_exec {n Ob : ℕ} (c : Config) (hc : WordsBounded W c) (r00 : c.nreg 2100 = n)
    (r01 : c.nreg 2101 = Ob) (hW : Ob + n ≤ W) (h1 : 1 ≤ W) :
    ∃ c' k, Exec P W idProg c c' k ∧ k ≤ 5 * n + 4 ∧ (∀ i < n, c'.nmem (Ob + i) = i) ∧
      (∀ a, (a < Ob ∨ Ob + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2102 ∨ 2104 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold idProg
  obtain ⟨c₁, k₁, e₁, hk₁, g02, g03, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 2102 0, .constN 2103 1]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 2102 = 0 ∧ c₁.nreg 2103 = 1 ∧
      (∀ r, r ≠ 2102 → r ≠ 2103 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp (disch := omega) only [upd_other]
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ e < i, c'.nmem (Ob + e) = e) ∧
      (∀ a, (a < Ob ∨ Ob + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2102 ∨ 2104 < r) → c'.nreg r = c.nreg r) ∧ c'.nreg 2103 = 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  have k1 : ∀ r, (r < 2102 ∨ 2104 < r) → c₁.nreg r = c.nreg r := fun r h =>
    gn₁ r (by omega) (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2102) (bR := 2100)
    (body := idBody) J (K := 3) (n := n) c₁ e₁.wb_right g02
    (by rw [k1 2100 (by omega)]; exact r00)
    ⟨fun e he => absurd he (by omega), fun a _ => by rw [gm₁], fun r hr => k1 r hr, g03,
      gr₁, grm₁, go₁⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j3, j03, jr, jrm, jo⟩ := hJ
      have j01 : c'.nreg 2101 = Ob := by rw [j3 _ (by omega)]; exact r01
      obtain ⟨c'', k, ex, hk, h02, h03, hn, hm, hr, hrm, ho⟩ : ∃ c'' k,
          Exec P W idBody c' c'' k ∧ k = 3 ∧ c''.nreg 2102 = i + 1 ∧ c''.nreg 2103 = 1 ∧
          (∀ r, r ≠ 2102 → r ≠ 2104 → c''.nreg r = c'.nreg r) ∧
          c''.nmem = upd c'.nmem (Ob + i) i ∧ c''.rreg = c'.rreg ∧ c''.rmem = c'.rmem ∧
          c''.output = c'.output := by
        unfold idBody
        exec_block
        all_goals try ((try config_simp); (try simp only [ha, j01, j03]); omega)
        refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, ?_, rfl, rfl, rfl⟩
        all_goals config_simp
        all_goals try simp only [ha, j01, j03]
        · simp (disch := omega) only [upd_other]
      refine ⟨c'', k, ex, by omega, h02, by rw [hn 2100 (by omega) (by omega)]; exact hb,
        fun e he => ?_, fun a h => ?_, fun r hr' => ?_, h03, by rw [hr, jr], by rw [hrm, jrm],
        by rw [ho, jo]⟩
      · rw [hm, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact j1 e he
        · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      · rw [hm, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact j2 a (by omega)
      · rw [hn r (by omega) (by omega)]; exact j3 r hr')
  obtain ⟨j1, j2, j3, -, jr, jrm, jo⟩ := hJ
  exact ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by omega, j1, j2, j3, jr, jrm, jo⟩

/-! ### A plain gather and a zero loop -/

/-- One step of the gather: `OUT[i] := IN[J[i]]` (`i = r2109`). -/
def gaBody : Stmt :=
  block [.addN 2112 2107 2109, .loadN 2112 2112, .addN 2112 2106 2112, .loadN 2112 2112,
    .addN 2113 2108 2109, .storeN 2113 2112, .addN 2109 2109 2110]

/-- **The gather** `OUT[i] := IN[J[i]]` for `i < n` (`r2105 = n`, `r2106 = INb`, `r2107 = Jb`,
`r2108 = OUTb`; scratch `2109 … 2113`). -/
def gaProg : Stmt :=
  .seq (block [.constN 2109 0, .constN 2110 1]) (.whileLtN 2109 2105 gaBody)

theorem gaProg_natOnly : Klein.natOnly gaProg = true := by kernel_rfl

theorem gaProg_exec {n INb Jb Ob : ℕ} (c : Config) (hc : WordsBounded W c)
    (r05 : c.nreg 2105 = n) (r06 : c.nreg 2106 = INb) (r07 : c.nreg 2107 = Jb)
    (r08 : c.nreg 2108 = Ob) (h1 : 1 ≤ W) (wO : Ob + n ≤ W) (wJ : Jb + n ≤ W)
    (dJ : Ob + n ≤ Jb ∨ Jb + n ≤ Ob)
    (hI : ∀ i < n, INb + c.nmem (Jb + i) ≤ W ∧
      (INb + c.nmem (Jb + i) < Ob ∨ Ob + n ≤ INb + c.nmem (Jb + i))) :
    ∃ c' k, Exec P W gaProg c c' k ∧ k ≤ 9 * n + 4 ∧
      (∀ i < n, c'.nmem (Ob + i) = c.nmem (INb + c.nmem (Jb + i))) ∧
      (∀ a, (a < Ob ∨ Ob + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2109 ∨ 2113 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold gaProg
  obtain ⟨c₁, k₁, e₁, hk₁, g09, g10, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 2109 0, .constN 2110 1]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 2109 = 0 ∧ c₁.nreg 2110 = 1 ∧
      (∀ r, r ≠ 2109 → r ≠ 2110 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp (disch := omega) only [upd_other]
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ e < i, c'.nmem (Ob + e) = c.nmem (INb + c.nmem (Jb + e))) ∧
      (∀ a, (a < Ob ∨ Ob + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2109 ∨ 2113 < r) → c'.nreg r = c.nreg r) ∧ c'.nreg 2110 = 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  have k1 : ∀ r, (r < 2109 ∨ 2113 < r) → c₁.nreg r = c.nreg r := fun r h =>
    gn₁ r (by omega) (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2109) (bR := 2105)
    (body := gaBody) J (K := 7) (n := n) c₁ e₁.wb_right g09
    (by rw [k1 2105 (by omega)]; exact r05)
    ⟨fun e he => absurd he (by omega), fun a _ => by rw [gm₁], fun r hr => k1 r hr, g10,
      gr₁, grm₁, go₁⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j3, j10, jr, jrm, jo⟩ := hJ
      have j06 : c'.nreg 2106 = INb := by rw [j3 _ (by omega)]; exact r06
      have j07 : c'.nreg 2107 = Jb := by rw [j3 _ (by omega)]; exact r07
      have j08 : c'.nreg 2108 = Ob := by rw [j3 _ (by omega)]; exact r08
      have eJ : c'.nmem (Jb + i) = c.nmem (Jb + i) := j2 _ (by omega)
      obtain ⟨t1, t2⟩ := hI i hi
      have eI : c'.nmem (INb + c.nmem (Jb + i)) = c.nmem (INb + c.nmem (Jb + i)) :=
        j2 _ (by omega)
      obtain ⟨c'', k, ex, hk, h09, h10, hn, hm, hr, hrm, ho⟩ : ∃ c'' k,
          Exec P W gaBody c' c'' k ∧ k = 7 ∧ c''.nreg 2109 = i + 1 ∧ c''.nreg 2110 = 1 ∧
          (∀ r, r ≠ 2109 → r ≠ 2112 → r ≠ 2113 → c''.nreg r = c'.nreg r) ∧
          c''.nmem = upd c'.nmem (Ob + i) (c.nmem (INb + c.nmem (Jb + i))) ∧
          c''.rreg = c'.rreg ∧ c''.rmem = c'.rmem ∧ c''.output = c'.output := by
        have hw' := hw
        unfold gaBody
        exec_block
        all_goals try ((try config_simp); (try simp only [ha, j06, j07, j08, j10, eJ, eI]); omega)
        refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, rfl, rfl, rfl⟩
        all_goals config_simp
        all_goals try simp only [ha, j06, j07, j08, j10, eJ, eI]
        · simp (disch := omega) only [upd_other]
      refine ⟨c'', k, ex, by omega, h09, by rw [hn 2105 (by omega) (by omega) (by omega)]; exact hb,
        fun e he => ?_, fun a h => ?_, fun r hr' => ?_, h10, by rw [hr, jr], by rw [hrm, jrm],
        by rw [ho, jo]⟩
      · rw [hm, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact j1 e he
        · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      · rw [hm, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact j2 a (by omega)
      · rw [hn r (by omega) (by omega) (by omega)]; exact j3 r hr')
  obtain ⟨j1, j2, j3, -, jr, jrm, jo⟩ := hJ
  exact ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by omega, j1, j2, j3, jr, jrm, jo⟩

/-- One step of the zero loop: `OUT[i] := 0` (`i = r2116`). -/
def zrBody : Stmt := block [.addN 2118 2115 2116, .storeN 2118 2119, .addN 2116 2116 2117]

/-- **The zero loop** `OUT[i] := 0` for `i < n` (`r2114 = n`, `r2115 = OUTb`; scratch
`2116 … 2119`). -/
def zrProg : Stmt :=
  .seq (block [.constN 2116 0, .constN 2117 1, .constN 2119 0]) (.whileLtN 2116 2114 zrBody)

theorem zrProg_natOnly : Klein.natOnly zrProg = true := by kernel_rfl

theorem zrProg_exec {n Ob : ℕ} (c : Config) (hc : WordsBounded W c) (r14 : c.nreg 2114 = n)
    (r15 : c.nreg 2115 = Ob) (hW : Ob + n ≤ W) (h1 : 1 ≤ W) :
    ∃ c' k, Exec P W zrProg c c' k ∧ k ≤ 5 * n + 5 ∧ (∀ i < n, c'.nmem (Ob + i) = 0) ∧
      (∀ a, (a < Ob ∨ Ob + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2116 ∨ 2119 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold zrProg
  obtain ⟨c₁, k₁, e₁, hk₁, g16, g17, g19, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 2116 0, .constN 2117 1, .constN 2119 0]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 2116 = 0 ∧ c₁.nreg 2117 = 1 ∧ c₁.nreg 2119 = 0 ∧
      (∀ r, r ≠ 2116 → r ≠ 2117 → r ≠ 2119 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp (disch := omega) only [upd_other]
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ e < i, c'.nmem (Ob + e) = 0) ∧
      (∀ a, (a < Ob ∨ Ob + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2116 ∨ 2119 < r) → c'.nreg r = c.nreg r) ∧ c'.nreg 2117 = 1 ∧
      c'.nreg 2119 = 0 ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  have k1 : ∀ r, (r < 2116 ∨ 2119 < r) → c₁.nreg r = c.nreg r := fun r h =>
    gn₁ r (by omega) (by omega) (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2116) (bR := 2114)
    (body := zrBody) J (K := 3) (n := n) c₁ e₁.wb_right g16
    (by rw [k1 2114 (by omega)]; exact r14)
    ⟨fun e he => absurd he (by omega), fun a _ => by rw [gm₁], fun r hr => k1 r hr, g17, g19,
      gr₁, grm₁, go₁⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j3, j17, j19, jr, jrm, jo⟩ := hJ
      have j15 : c'.nreg 2115 = Ob := by rw [j3 _ (by omega)]; exact r15
      obtain ⟨c'', k, ex, hk, h16, h17, h19, hn, hm, hr, hrm, ho⟩ : ∃ c'' k,
          Exec P W zrBody c' c'' k ∧ k = 3 ∧ c''.nreg 2116 = i + 1 ∧ c''.nreg 2117 = 1 ∧
          c''.nreg 2119 = 0 ∧
          (∀ r, r ≠ 2116 → r ≠ 2118 → c''.nreg r = c'.nreg r) ∧
          c''.nmem = upd c'.nmem (Ob + i) 0 ∧ c''.rreg = c'.rreg ∧ c''.rmem = c'.rmem ∧
          c''.output = c'.output := by
        unfold zrBody
        exec_block
        all_goals try ((try config_simp); (try simp only [ha, j15, j17, j19]); omega)
        refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 => ?_, ?_, rfl, rfl, rfl⟩
        all_goals config_simp
        all_goals try simp only [ha, j15, j17, j19]
        · simp (disch := omega) only [upd_other]
      refine ⟨c'', k, ex, by omega, h16, by rw [hn 2114 (by omega) (by omega)]; exact hb,
        fun e he => ?_, fun a h => ?_, fun r hr' => ?_, h17, h19, by rw [hr, jr],
        by rw [hrm, jrm], by rw [ho, jo]⟩
      · rw [hm, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact j1 e he
        · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      · rw [hm, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact j2 a (by omega)
      · rw [hn r (by omega) (by omega)]; exact j3 r hr')
  obtain ⟨j1, j2, j3, -, -, jr, jrm, jo⟩ := hJ
  exact ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by omega, j1, j2, j3, jr, jrm, jo⟩

end NegSSSP

end PlanarFlow
