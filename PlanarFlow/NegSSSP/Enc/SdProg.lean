module

public import PlanarFlow.NegSSSP.Enc.SdArr
public import PlanarFlow.NegSSSP.Enc.DkProg
public import PlanarFlow.NegSSSP.LinGlue

/-!
# The program writing the plain arrays of a side (`sdProg`): the program, pass 1

`sdProg` writes, from the plain arrays of the stellar subdivision of the piece map (reverses at
`bA`, vertex numbers at `bV`, `3 m` codes), the marks of a side `Z` (`sv` at `bz`, one per
triangle), the flags of `K` (`bK`), the lengths (`bL`) and the codes of the walk along the
boundary of the side (`bW`, `k` words), the six plain arrays of the one-face instance of the side
(`sd_arrays`), in passes over the codes:

1. `sdL1`: the flags `inf y` of the darts of the disc and their prefix counts (`INF`, `NUM`);
2. `sdL2a`, `sdL2b`, `sdL2c`: the flags of the used vertex numbers and their prefix counts
   (`U`, `VN`);
3. `sdL3`: the prefix counts of the triangles in `Z` (`TN`) and their number `nZ`;
4. `sdL4`: for every dart of the disc, its five words at `I0 + j nD + NUM[y]`;
5. `sdL5`: the words of the walk at `I0 + 5 nD + t`.

Registers: inputs `2550 … 2561` (`m`, `bz`, `sv`, `bA`, `bV`, `nV + nF`, `bK`, `bL`, `bW`, `k`,
`S` the scratch, `I0` the output); the program writes only `2562 … 2593` (the loop bodies only `2562`, `2564`, `2568 … 2579`)
(`sdProg_ok`, by `decide`), with natural instructions only, so it keeps every other register,
the reals and the output (`sd_keep`).

Here: the programs, `sd_keep`, and pass 1 (`sdL1_exec`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge.CmpAbs

variable {P : Input} {W : ℕ}

/-! ### The programs -/

/-- Constants and the scratch layout: `r2589 = 1`, `r2590 = 3`, `r2591 = 0`, `r2564 = 0`,
`r2587 = 3 m`, `INF = r2582 = S`, `NUM = r2583 = S + 3 m`, `U = r2584 = S + 6 m`,
`VN = r2585 = U + (nV + nF)`, `TN = r2586 = VN + (nV + nF)`. -/
def sdSetup : Stmt := block [.constN 2589 1, .constN 2590 3, .constN 2591 0, .constN 2564 0,
  .mulN 2587 2590 2550, .copyN 2582 2560, .addN 2583 2560 2587, .addN 2584 2583 2587,
  .addN 2585 2584 2555, .addN 2586 2585 2555]

/-- Pass 1, one code `y = r2562`: `INF[y] := inf y`, `NUM[y] := cnt`, `cnt += inf y`. -/
def sdB1 : Stmt := block [.divN 2568 2562 2590, .addN 2568 2551 2568, .loadN 2568 2568,
  .subN 2569 2568 2552, .subN 2570 2552 2568, .addN 2569 2569 2570, .subN 2569 2589 2569,
  .addN 2568 2553 2562, .loadN 2568 2568, .divN 2568 2568 2590, .addN 2568 2551 2568,
  .loadN 2568 2568, .subN 2570 2568 2552, .subN 2571 2552 2568, .addN 2570 2570 2571,
  .subN 2570 2589 2570, .addN 2571 2569 2570, .mulN 2572 2569 2570, .subN 2571 2571 2572,
  .addN 2568 2582 2562, .storeN 2568 2571, .addN 2568 2583 2562, .storeN 2568 2564,
  .addN 2564 2564 2571, .addN 2562 2562 2589]

/-- Pass 1. -/
def sdL1 : Stmt :=
  .seq (block [.constN 2562 0, .copyN 2592 2587]) (.whileLtN 2562 2592 sdB1)

/-- Pass 2a, one vertex number `v`: `U[v] := 0`. -/
def sdB2a : Stmt := block [.addN 2568 2584 2562, .storeN 2568 2591, .addN 2562 2562 2589]

/-- Pass 2a: `nD := cnt`, the flags `U` cleared. -/
def sdL2a : Stmt :=
  .seq (block [.copyN 2580 2564, .constN 2562 0, .copyN 2592 2555]) (.whileLtN 2562 2592 sdB2a)

/-- Pass 2b, one code `y`: `U[V[y]] := U[V[y]] ∨ INF[y]`. -/
def sdB2b : Stmt := block [.addN 2568 2554 2562, .loadN 2568 2568, .addN 2568 2584 2568,
  .loadN 2569 2568, .addN 2570 2582 2562, .loadN 2570 2570, .addN 2571 2569 2570,
  .mulN 2572 2569 2570, .subN 2571 2571 2572, .storeN 2568 2571, .addN 2562 2562 2589]

/-- Pass 2b. -/
def sdL2b : Stmt :=
  .seq (block [.constN 2562 0, .copyN 2592 2587]) (.whileLtN 2562 2592 sdB2b)

/-- Pass 2c, one vertex number `v`: `VN[v] := cnt`, `cnt += U[v]`. -/
def sdB2c : Stmt := block [.addN 2568 2585 2562, .storeN 2568 2564, .addN 2568 2584 2562,
  .loadN 2568 2568, .addN 2564 2564 2568, .addN 2562 2562 2589]

/-- Pass 2c. -/
def sdL2c : Stmt :=
  .seq (block [.constN 2562 0, .copyN 2592 2555, .constN 2564 0]) (.whileLtN 2562 2592 sdB2c)

/-- Pass 3, one triangle `x`: `TN[x] := cnt`, `cnt += [mark x = sv]`. -/
def sdB3 : Stmt := block [.addN 2568 2586 2562, .storeN 2568 2564, .addN 2568 2551 2562,
  .loadN 2568 2568, .subN 2569 2568 2552, .subN 2570 2552 2568, .addN 2569 2569 2570,
  .subN 2569 2589 2569, .addN 2564 2564 2569, .addN 2562 2562 2589]

/-- Pass 3 (`r2593 :=` the count of the used vertex numbers, left by pass 2c). -/
def sdL3 : Stmt :=
  .seq (block [.copyN 2593 2564, .constN 2562 0, .copyN 2592 2550, .constN 2564 0])
    (.whileLtN 2562 2592 sdB3)

/-- Pass 4, the words of one dart of the disc (`y = r2562`, `INF[y] = 1`): the five values read
first (`NUM[A[y]]`, `VN[V[y]]`, `e₁ TN[z] + (1 − e₁) nZ`, `e₀ e₁ KB[z]`, `e₀ e₁ KB[z] LP[z]`,
`z = y / 3`, `e₁ = [mark z = sv]`, `e₀ = [y mod 3 = 0]`), then stored at `o, o + nD, …,
o + 4 nD`, `o = I0 + NUM[y]`. -/
def sdB4w : Stmt := block [.addN 2568 2553 2562, .loadN 2568 2568, .addN 2568 2583 2568,
  .loadN 2576 2568, .addN 2568 2554 2562, .loadN 2568 2568, .addN 2568 2585 2568,
  .loadN 2577 2568, .divN 2574 2562 2590, .addN 2568 2551 2574, .loadN 2568 2568,
  .subN 2569 2568 2552, .subN 2570 2552 2568, .addN 2569 2569 2570, .subN 2569 2589 2569,
  .addN 2568 2586 2574, .loadN 2568 2568, .mulN 2578 2569 2568, .subN 2572 2589 2569,
  .mulN 2572 2572 2581, .addN 2578 2578 2572, .modN 2572 2562 2590, .subN 2575 2572 2591,
  .subN 2570 2591 2572, .addN 2575 2575 2570, .subN 2575 2589 2575, .mulN 2575 2575 2569,
  .addN 2568 2556 2574, .loadN 2568 2568, .mulN 2575 2575 2568, .addN 2568 2557 2574,
  .loadN 2568 2568, .mulN 2579 2575 2568, .addN 2568 2583 2562, .loadN 2568 2568,
  .addN 2573 2561 2568, .storeN 2573 2576, .addN 2573 2573 2580, .storeN 2573 2577,
  .addN 2573 2573 2580, .storeN 2573 2578, .addN 2573 2573 2580, .storeN 2573 2575,
  .addN 2573 2573 2580, .storeN 2573 2579]

/-- Pass 4, one code. -/
def sdB4 : Stmt :=
  .seq (block [.addN 2568 2582 2562, .loadN 2571 2568])
    (.seq (.ifLtN 2591 2571 sdB4w .skip) (.instr (.addN 2562 2562 2589)))

/-- Pass 4: `nZ := cnt`. -/
def sdL4 : Stmt :=
  .seq (block [.copyN 2581 2564, .constN 2562 0, .copyN 2592 2587]) (.whileLtN 2562 2592 sdB4)

/-- Pass 5, one position `t` of the walk: `G[t] := NUM[Wk[t]]`. -/
def sdB5 : Stmt := block [.addN 2568 2558 2562, .loadN 2568 2568, .addN 2568 2583 2568,
  .loadN 2568 2568, .addN 2569 2588 2562, .storeN 2569 2568, .addN 2562 2562 2589]

/-- Pass 5: `r2588 = I0 + 5 nD`. -/
def sdL5 : Stmt :=
  .seq (block [.constN 2568 5, .mulN 2588 2568 2580, .addN 2588 2588 2561, .constN 2562 0,
    .copyN 2592 2559]) (.whileLtN 2562 2592 sdB5)

/-- **The plain arrays of a side.** -/
def sdProg : Stmt :=
  .seq sdSetup (.seq sdL1 (.seq sdL2a (.seq sdL2b (.seq sdL2c (.seq sdL3 (.seq sdL4 sdL5))))))

/-! ### Syntactic frames -/

/-- A pure natural instruction writing a register in `[lo, hi]` (if any). -/
def sdOk (lo hi : ℕ) (i : Instr) : Bool :=
  dkPure i && match i.wN with
    | some r => decide (lo ≤ r ∧ r ≤ hi)
    | none => true

/-- **A statement of pure natural instructions writing registers in `[lo, hi]` only** keeps
every other register, the reals and the output. -/
theorem sd_keep {lo hi : ℕ} {s : Stmt} {c d : Config} {k : ℕ} (e : Exec P W s c d k)
    (h : s.allI (sdOk lo hi) = true) :
    (∀ r, r < lo ∨ hi < r → d.nreg r = c.nreg r) ∧ d.rreg = c.rreg ∧ d.rmem = c.rmem ∧
      d.output = c.output := by
  have hp : s.allI dkPure = true := nb_allI_mono (fun i hi => by
    simp only [sdOk, Bool.and_eq_true] at hi; exact hi.1) s h
  refine ⟨fun r hr => e.nreg_keep (nb_allI_mono (fun i hi => ?_) s h), dk_exec_pure e hp⟩
  simp only [sdOk, Bool.and_eq_true] at hi
  simp only [decide_eq_true_eq]
  intro he
  rw [he] at hi
  simp only [decide_eq_true_eq] at hi
  omega

theorem sdProg_ok : sdProg.allI (sdOk 2562 2593) = true := by decide

theorem sdProg_natOnly : Klein.natOnly sdProg = true := by kernel_rfl

/-! ### Pass 1 -/

lemma sd_absd_le {a b W : ℕ} (ha : a ≤ W) (hb : b ≤ W) : a - b + (b - a) ≤ W := by omega

lemma sd_or_le {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) : a + b - a * b ≤ 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with rfl | rfl <;> simp

theorem sdB1_exec (c : Config) (hc : WordsBounded W c) {m bz sv bA INF NUM y cnt : ℕ}
    (r51 : c.nreg 2551 = bz) (r52 : c.nreg 2552 = sv) (r53 : c.nreg 2553 = bA)
    (r89 : c.nreg 2589 = 1) (r90 : c.nreg 2590 = 3) (r82 : c.nreg 2582 = INF)
    (r83 : c.nreg 2583 = NUM) (r62 : c.nreg 2562 = y) (r64 : c.nreg 2564 = cnt)
    (hy : y < 3 * m) (hay : c.nmem (bA + y) < 3 * m) (w1 : bz + m ≤ W) (w2 : bA + y ≤ W)
    (w3 : INF + y ≤ W) (w4 : NUM + y ≤ W) (w5 : cnt + 1 ≤ W) (w6 : y + 1 ≤ W) (w7 : 2 ≤ W) :
    ∃ c' k, Exec P W sdB1 c c' k ∧ k = 25 ∧
      c'.nmem = upd (upd c.nmem (INF + y) (sdInf c.nmem bz bA sv y)) (NUM + y) cnt ∧
      c'.nreg 2564 = cnt + sdInf c.nmem bz bA sv y ∧ c'.nreg 2562 = y + 1 := by
  have hsv : sv ≤ W := r52 ▸ hc.1 2552
  have hle := sdInf_le c.nmem bz bA sv y
  unfold sdB1
  exec_block
  all_goals try (config_simp; simp only [r51, r52, r53, r62, r89, r64, r90, r82, r83]; first | omega | exact sd_absd_le (hc.2 _) hsv | exact le_trans (Nat.mul_le_mul (Nat.sub_le 1 _) (Nat.sub_le 1 _)) (by omega) | exact le_trans (Nat.add_le_add_left (sd_or_le (Nat.sub_le 1 _) (Nat.sub_le 1 _)) _) (by omega))
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · config_simp; simp only [r51, r52, r53, r62, r89, r64, r90, r82, r83]; rfl
    · config_simp; simp only [r51, r52, r53, r62, r89, r64, r90, r82, r83]; rfl
    · config_simp; simp only [r62, r89]

theorem sdB1_ok : sdB1.allI (sdOk 2562 2579) = true := by decide

lemma sdInf_congr {mem mem' : ℕ → ℕ} {bz bA sv y : ℕ} (h1 : mem' (bz + y / 3) = mem (bz + y / 3))
    (h2 : mem' (bA + y) = mem (bA + y)) (h3 : mem' (bz + mem (bA + y) / 3) = mem (bz + mem (bA + y) / 3)) :
    sdInf mem' bz bA sv y = sdInf mem bz bA sv y := by
  unfold sdInf; rw [h1, h2, h3]

/-- **Pass 1**: the flags of the darts of the disc at `INF`, their prefix counts at
`NUM = INF + 3 m`, the count `nD` in `r2564`, within `27 (3 m) + 4` steps. -/
theorem sdL1_exec (c : Config) (hc : WordsBounded W c) {m bz sv bA INF : ℕ}
    (r87 : c.nreg 2587 = 3 * m) (r51 : c.nreg 2551 = bz) (r52 : c.nreg 2552 = sv)
    (r53 : c.nreg 2553 = bA) (r89 : c.nreg 2589 = 1) (r90 : c.nreg 2590 = 3)
    (r82 : c.nreg 2582 = INF) (r83 : c.nreg 2583 = INF + 3 * m) (r64 : c.nreg 2564 = 0)
    (hA : ∀ y < 3 * m, c.nmem (bA + y) < 3 * m) (l1 : bz + m ≤ INF) (l2 : bA + 3 * m ≤ INF)
    (w : INF + 6 * m + 2 ≤ W) :
    ∃ c' k, Exec P W sdL1 c c' k ∧ k ≤ 27 * (3 * m) + 4 ∧
      (∀ y < 3 * m, c'.nmem (INF + y) = sdInf c.nmem bz bA sv y ∧
        c'.nmem (INF + 3 * m + y) = sdCnt (sdInf c.nmem bz bA sv) y) ∧
      c'.nreg 2564 = sdCnt (sdInf c.nmem bz bA sv) (3 * m) ∧
      (∀ a, a < INF ∨ INF + 6 * m ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2562 ∨ 2592 < r → c'.nreg r = c.nreg r) := by
  have hsv : sv ≤ W := r52 ▸ hc.1 2552
  unfold sdL1
  obtain ⟨c₁, k₁, e₁, hk₁, g62, g92, gn₁, gm₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 2562 0, .copyN 2592 2587]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 2562 = 0 ∧ c₁.nreg 2592 = 3 * m ∧
      (∀ r, r ≠ 2562 → r ≠ 2592 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl⟩
    all_goals config_simp
    · exact r87
    · simp only [upd_apply]; split_ifs <;> omega
  set inf := sdInf c.nmem bz bA sv with hinf
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ y < i, c'.nmem (INF + y) = inf y ∧ c'.nmem (INF + 3 * m + y) = sdCnt inf y) ∧
      (∀ a, a < INF ∨ INF + 6 * m ≤ a → c'.nmem a = c.nmem a) ∧
      c'.nreg 2564 = sdCnt inf i ∧ (∀ r, r < 2562 ∨ 2579 < r → c'.nreg r = c₁.nreg r)
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2562) (bR := 2592)
    (body := sdB1) J (K := 25) (n := 3 * m) c₁ e₁.wb_right g62 g92
    ⟨fun y hy => absurd hy (by omega), fun a _ => by rw [gm₁],
      by rw [gn₁ _ (by omega) (by omega), r64, sdCnt_zero], fun r _ => rfl⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j3, j4⟩ := hJ
      have R : ∀ r, r < 2562 ∨ 2579 < r → r ≠ 2592 → c'.nreg r = c.nreg r := fun r hr h' =>
        (j4 r hr).trans (gn₁ r (by omega) h')
      have hai : c'.nmem (bA + i) = c.nmem (bA + i) := j2 _ (by omega)
      have hlt := hA i hi
      have hcnt : sdCnt inf i ≤ i := sdCnt_le (fun y _ => sdInf_le _ _ _ _ _)
      obtain ⟨c'', k, ex, hk, hm, h64, h62⟩ := sdB1_exec (P := P) (m := m) c' hw
        ((R 2551 (by omega) (by omega)).trans r51) ((R 2552 (by omega) (by omega)).trans r52)
        ((R 2553 (by omega) (by omega)).trans r53) ((R 2589 (by omega) (by omega)).trans r89)
        ((R 2590 (by omega) (by omega)).trans r90) ((R 2582 (by omega) (by omega)).trans r82)
        ((R 2583 (by omega) (by omega)).trans r83) ha j3 hi (by rw [hai]; exact hlt) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hinf' : sdInf c'.nmem bz bA sv i = inf i :=
        sdInf_congr (j2 _ (by omega)) hai (j2 _ (by have := hA i hi; omega))
      have keep := (sd_keep ex sdB1_ok).1
      refine ⟨c'', k, ex, by omega, h62, by rw [keep 2592 (by omega)]; exact hb,
        fun y hy => ?_, fun a h => ?_, ?_, fun r hr => (keep r hr).trans (j4 r hr)⟩
      · rw [hm, upd_apply, upd_apply, upd_apply, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hy with hy | rfl
        · have := j1 y hy
          refine ⟨?_, ?_⟩
          · rw [sd_ifN (by omega), sd_ifN (by omega)]; exact this.1
          · rw [sd_ifN (by omega), sd_ifN (by omega)]; exact this.2
        · refine ⟨?_, ?_⟩
          · rw [sd_ifN (by omega), sd_ifP rfl, hinf']
          · rw [sd_ifP (by omega)]
      · rw [hm, upd_apply, upd_apply, sd_ifN (by omega), sd_ifN (by omega)]
        exact j2 a h
      · rw [h64, hinf', sdCnt_succ])
  obtain ⟨j1, j2, j3, j4⟩ := hJ
  refine ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by omega, j1, j3, fun a h => by rw [j2 a h], fun r hr => ?_⟩
  rcases hr with hr | hr
  · rw [j4 r (Or.inl hr), gn₁ r (by omega) (by omega)]
  · by_cases h : r ≤ 2579
    · omega
    · rw [j4 r (Or.inr (by omega))]
      by_cases h' : r = 2592
      · omega
      · rw [gn₁ r (by omega) h']

end NegSSSP

end PlanarFlow
