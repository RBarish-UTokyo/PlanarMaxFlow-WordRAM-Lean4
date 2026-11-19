module

public import PlanarFlow.BKMNW.BfsProg
public import PlanarFlow.BKMNW.CompGraph

/-!
# The components off a hole on the machine

The graph `cgAdj` of `PlanarFlow/BKMNW/CompGraph.lean` written in CSR form by one scan
(`cgBuild`), then labelled by breadth-first search (`bfProg`): **`ccProg`**.

Input layout (`CgLay`): `RV[i] = nmem (RVb + i)` (the index of the reverse dart, or `i`),
`TK[i] = nmem (TKb + i) < nk` (the class number of the tail), `YF[i] = nmem (YFb + i)` (nonzero iff
the tail is in `Y`), `i < n`; a table `LS[k] = nmem (LSb + k)`, `k < nk`, zero; the output
`OFF[i] = 3 i` (`i ≤ n`) and the slots `ADJ[3 i + r]`, `r < 3`; then the label and queue arrays of
`bfProg`. Registers `4420 = n`, `4421 = RVb`, `4422 = TKb`, `4423 = YFb`, `4424 = LSb`,
`4425 = OFFb`, `4426 = ADJb`; written `4427 … 4436`.

* `cgW1`, `cgW2`, `cgW3` (the writes of one index), `CgMem` (the memory after the indices
  `< j`), `cgMem_in`, `cgMem_zero`, `cgMem_pos`;
* `cgA`, `cgB`, `cgC`, `cgBody`, **`cgBuild`**, **`cgBuild_exec`** (`35 n + 8` steps);
* `bfAdj_cg` (the CSR adjacency is `cgAdj`), `bfIn_cg`, **`ccProg_exec`** (`104 n + 16`
  steps), **`ccProg_comp`**: for an enumeration of the darts `N` (`CgEnum`),
  `LAB[i] = LAB[j] ↔ e j ∈ comp M N Hs Y (e i)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Relation WordRAM WordRAM.Machine

/-! ### The memory of the scan -/

/-- The class numbers read from the input. -/
def cgKey (m : ℕ → ℕ) (TKb : ℕ) (i : ℕ) : ℕ := m (TKb + i)

/-- The flags read from the input. -/
def cgYf (m : ℕ → ℕ) (YFb : ℕ) (i : ℕ) : Bool := decide (0 < m (YFb + i))

/-- The writes common to every index `j` (offset `o = 3 j`, reverse slot `x`). -/
def cgW1 (m : ℕ → ℕ) (OFFb ADJb j o x : ℕ) : ℕ → ℕ :=
  upd (upd (upd (upd m (OFFb + j) o) (ADJb + o) x) (ADJb + o + 1) j) (ADJb + o + 1 + 1) j

/-- The link to the previous index `p - 1` of the class. -/
def cgW3 (m : ℕ → ℕ) (ADJb o j p : ℕ) : ℕ → ℕ :=
  upd (upd m (ADJb + o + 1) (p - 1)) ((p - 1) + (p - 1) + (p - 1) + ADJb + 1 + 1) j

/-- The last index of the class. -/
def cgW2 (m : ℕ → ℕ) (LSb k j : ℕ) : ℕ → ℕ := upd m (LSb + k) (j + 1)

/-- The layout: `RV (n) | TK (n) | YF (n) | LS (nk) | OFF (n + 1) | ADJ (3 n)`. -/
structure CgLay (n nk RVb TKb YFb LSb OFFb ADJb : ℕ) : Prop where
  l1 : RVb + n ≤ TKb
  l2 : TKb + n ≤ YFb
  l3 : YFb + n ≤ LSb
  l4 : LSb + nk ≤ OFFb
  l5 : OFFb + n + 1 ≤ ADJb

/-- The memory after the indices `< j`. -/
structure CgMem (m₀ m : ℕ → ℕ) (n nk RVb TKb YFb LSb OFFb ADJb j : ℕ) : Prop where
  off : ∀ i < j, m (OFFb + i) = 3 * i
  s0 : ∀ i < j, m (ADJb + 3 * i) = m₀ (RVb + i)
  s1 : ∀ i < j, m (ADJb + 3 * i + 1) = cgS1 (cgKey m₀ TKb) (cgYf m₀ YFb) i
  s2 : ∀ i < j, m (ADJb + 3 * i + 2) = cgS2 (cgKey m₀ TKb) (cgYf m₀ YFb) j i
  ls : ∀ k < nk, m (LSb + k) = lastF (cgKey m₀ TKb) (cgYf m₀ YFb) k j
  frame : ∀ a, ¬ (LSb ≤ a ∧ a < LSb + nk) → ¬ (OFFb ≤ a ∧ a < OFFb + n + 1) →
    ¬ (ADJb ≤ a ∧ a < ADJb + 3 * n) → m a = m₀ a

section Pure

variable {m₀ m : ℕ → ℕ} {n nk RVb TKb YFb LSb OFFb ADJb j : ℕ}

lemma cgMem_start (h0 : ∀ k < nk, m₀ (LSb + k) = 0) :
    CgMem m₀ m₀ n nk RVb TKb YFb LSb OFFb ADJb 0 :=
  ⟨fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega),
    fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega),
    fun k hk => by rw [h0 k hk]; rfl, fun _ _ _ _ => rfl⟩

lemma cgW1_apply (a : ℕ) : cgW1 m OFFb ADJb j (3 * j) (m₀ (RVb + j)) a =
    if a = ADJb + 3 * j + 2 then j else if a = ADJb + 3 * j + 1 then j else
    if a = ADJb + 3 * j then m₀ (RVb + j) else if a = OFFb + j then 3 * j else m a := by
  unfold cgW1
  simp only [upd_apply, show ADJb + 3 * j + 1 + 1 = ADJb + 3 * j + 2 by omega]

lemma cgW3_apply {o p : ℕ} (a : ℕ) : cgW3 m ADJb o j p a =
    if a = ADJb + 3 * (p - 1) + 2 then j else if a = ADJb + o + 1 then p - 1 else m a := by
  unfold cgW3
  simp only [upd_apply, show p - 1 + (p - 1) + (p - 1) + ADJb + 1 + 1 = ADJb + 3 * (p - 1) + 2 by
    omega]

lemma cgW2_apply {k : ℕ} (a : ℕ) : cgW2 m LSb k j a = if a = LSb + k then j + 1 else m a := rfl

lemma cgYf_true {i : ℕ} (h : 0 < m₀ (YFb + i)) : cgYf m₀ YFb i = true := by
  unfold cgYf; simp [h]

lemma cgYf_false {i : ℕ} (h : m₀ (YFb + i) = 0) : cgYf m₀ YFb i = false := by
  unfold cgYf; simp [h]

/-- **An index in `Y`**: only the common writes. -/
lemma cgMem_in (hL : CgLay n nk RVb TKb YFb LSb OFFb ADJb)
    (hM : CgMem m₀ m n nk RVb TKb YFb LSb OFFb ADJb j) (hj : j < n) (hy : 0 < m₀ (YFb + j)) :
    CgMem m₀ (cgW1 m OFFb ADJb j (3 * j) (m₀ (RVb + j))) n nk RVb TKb YFb LSb OFFb ADJb
      (j + 1) := by
  obtain ⟨l1, l2, l3, l4, l5⟩ := hL
  have hyt := cgYf_true (m₀ := m₀) hy
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun k hk => ?_,
    fun a h1 h2 h3 => ?_⟩
  all_goals rw [cgW1_apply]
  · split_ifs <;> first | omega | exact hM.off i (by omega)
  · split_ifs
    all_goals first | omega | (rw [show i = j by omega]) | exact hM.s0 i (by omega)
  · split_ifs
    all_goals first | omega | (rw [show i = j by omega, cgS1_of_in hyt]) |
      exact hM.s1 i (by omega)
  · split_ifs
    all_goals first | omega | (rw [show i = j by omega, cgS2_self_succ]) |
      (rw [cgS2_succ_of_in hyt]; exact hM.s2 i (by omega))
  · split_ifs
    all_goals first | omega | skip
    rw [lastF_succ, cgIteF (fun h => by rw [hyt] at h; exact Bool.noConfusion h.1)]
    exact hM.ls k hk
  · split_ifs
    all_goals first | omega | exact hM.frame a h1 h2 h3

/-- **An index off `Y`, first of its class**: the common writes and the table. -/
lemma cgMem_zero (hL : CgLay n nk RVb TKb YFb LSb OFFb ADJb)
    (hM : CgMem m₀ m n nk RVb TKb YFb LSb OFFb ADJb j) (hj : j < n) (hy : m₀ (YFb + j) = 0)
    (hk : m₀ (TKb + j) < nk) (h0 : m (LSb + m₀ (TKb + j)) = 0) :
    CgMem m₀ (cgW2 (cgW1 m OFFb ADJb j (3 * j) (m₀ (RVb + j))) LSb (m₀ (TKb + j)) j)
      n nk RVb TKb YFb LSb OFFb ADJb (j + 1) := by
  obtain ⟨l1, l2, l3, l4, l5⟩ := hL
  have hyf := cgYf_false (m₀ := m₀) hy
  have hl0 : lastF (cgKey m₀ TKb) (cgYf m₀ YFb) (cgKey m₀ TKb j) j = 0 := by
    exact (hM.ls _ hk).symm.trans h0
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun k hk' => ?_,
    fun a h1 h2 h3 => ?_⟩
  all_goals rw [cgW2_apply, cgW1_apply]
  · split_ifs <;> first | omega | exact hM.off i (by omega)
  · split_ifs
    all_goals first | omega | (rw [show i = j by omega]) | exact hM.s0 i (by omega)
  · split_ifs
    all_goals first | omega | (rw [show i = j by omega, cgS1_of_zero hl0]) |
      exact hM.s1 i (by omega)
  · split_ifs
    all_goals first | omega | (rw [show i = j by omega, cgS2_self_succ]) |
      (rw [cgS2_succ_of_zero hyf hl0 (by omega)]; exact hM.s2 i (by omega))
  · split_ifs with e1
    all_goals first | omega | skip
    · rw [lastF_succ, cgIteT ⟨hyf, by unfold cgKey; omega⟩]
    · rw [lastF_succ, cgIteF (fun h => by unfold cgKey at h; omega)]
      exact hM.ls k hk'
  · split_ifs
    all_goals first | omega | exact hM.frame a h1 h2 h3

/-- **An index off `Y` after the index `p - 1` of its class**: the link, the table. -/
lemma cgMem_pos (hL : CgLay n nk RVb TKb YFb LSb OFFb ADJb)
    (hM : CgMem m₀ m n nk RVb TKb YFb LSb OFFb ADJb j) (hj : j < n) (hy : m₀ (YFb + j) = 0)
    (hk : m₀ (TKb + j) < nk) (hp : 0 < m (LSb + m₀ (TKb + j))) :
    CgMem m₀ (cgW2 (cgW3 (cgW1 m OFFb ADJb j (3 * j) (m₀ (RVb + j))) ADJb (3 * j) j
        (m (LSb + m₀ (TKb + j)))) LSb (m₀ (TKb + j)) j)
      n nk RVb TKb YFb LSb OFFb ADJb (j + 1) := by
  obtain ⟨l1, l2, l3, l4, l5⟩ := hL
  have hyf := cgYf_false (m₀ := m₀) hy
  set p := m (LSb + m₀ (TKb + j)) with hpdef
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hlq : lastF (cgKey m₀ TKb) (cgYf m₀ YFb) (cgKey m₀ TKb j) j = q + 1 := by
    exact (hM.ls _ hk).symm.trans hq
  have hqj : q < j := (lastF_pos hlq).1
  obtain ⟨hs2q, hs2o⟩ := cgS2_succ_of_pos hyf hlq
  have hs1 := cgS1_of_pos hyf hlq
  have hp1 : p - 1 = q := by omega
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun k hk' => ?_,
    fun a h1 h2 h3 => ?_⟩
  all_goals rw [cgW2_apply, cgW3_apply, cgW1_apply, hp1]
  · split_ifs <;> first | omega | exact hM.off i (by omega)
  · split_ifs
    all_goals first | omega | (rw [show i = j by omega]) | exact hM.s0 i (by omega)
  · split_ifs
    all_goals first | omega | (rw [show i = j by omega, hs1]) | exact hM.s1 i (by omega)
  · split_ifs
    all_goals first | omega | (rw [show i = q by omega, hs2q]) |
      (rw [show i = j by omega, cgS2_self_succ]) |
      (rw [hs2o i (by omega) (by omega)]; exact hM.s2 i (by omega))
  · split_ifs with e1
    all_goals first | omega | skip
    · rw [lastF_succ, cgIteT ⟨hyf, by unfold cgKey; omega⟩]
    · rw [lastF_succ, cgIteF (fun h => by unfold cgKey at h; omega)]
      exact hM.ls k hk'
  · split_ifs
    all_goals first | omega | exact hM.frame a h1 h2 h3

lemma cgW1_other {a : ℕ} (h1 : a ≠ ADJb + 3 * j + 2) (h2 : a ≠ ADJb + 3 * j + 1)
    (h3 : a ≠ ADJb + 3 * j) (h4 : a ≠ OFFb + j) :
    cgW1 m OFFb ADJb j (3 * j) (m₀ (RVb + j)) a = m a := by
  rw [cgW1_apply, cgIteF h1, cgIteF h2, cgIteF h3, cgIteF h4]

lemma lastF_le (key : ℕ → ℕ) (yf : ℕ → Bool) (k : ℕ) : ∀ j, lastF key yf k j ≤ j
  | 0 => le_rfl
  | j + 1 => by
    rw [lastF_succ]; split_ifs
    · exact le_rfl
    · exact le_trans (lastF_le key yf k j) (by omega)

lemma cgMem_last (hL : CgLay n nk RVb TKb YFb LSb OFFb ADJb)
    (hM : CgMem m₀ m n nk RVb TKb YFb LSb OFFb ADJb n) :
    CgMem m₀ (upd m (OFFb + n) (3 * n)) n nk RVb TKb YFb LSb OFFb ADJb n := by
  obtain ⟨l1, l2, l3, l4, l5⟩ := hL
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun k hk => ?_,
    fun a h1 h2 h3 => ?_⟩
  · rw [upd_other _ _ _ (by omega)]; exact hM.off i hi
  · rw [upd_other _ _ _ (by omega)]; exact hM.s0 i hi
  · rw [upd_other _ _ _ (by omega)]; exact hM.s1 i hi
  · rw [upd_other _ _ _ (by omega)]; exact hM.s2 i hi
  · rw [upd_other _ _ _ (by omega)]; exact hM.ls k hk
  · rw [upd_other _ _ _ (fun h => h2 ⟨by omega, by omega⟩)]; exact hM.frame a h1 h2 h3

end Pure

/-! ### The program of the scan -/

open WordRAM.Machine.Stmt WordRAM.Programs

/-- The common writes at the index `j` (`o = r4430 = 3 j`), then the flag `YF[j]` in `4432`. -/
def cgA : Stmt :=
  block [.addN 4431 4425 4429, .storeN 4431 4430, .addN 4431 4421 4429, .loadN 4432 4431,
    .addN 4433 4426 4430, .storeN 4433 4432, .addN 4433 4433 4427, .storeN 4433 4429,
    .addN 4434 4433 4427, .storeN 4434 4429, .addN 4431 4423 4429, .loadN 4432 4431]

/-- The link to the previous index `p - 1` (`p = r4436`). -/
def cgC : Stmt :=
  block [.subN 4432 4436 4427, .storeN 4433 4432, .addN 4431 4432 4432, .addN 4431 4431 4432,
    .addN 4431 4431 4426, .addN 4431 4431 4427, .addN 4431 4431 4427, .storeN 4431 4429]

/-- An index off `Y`: read the table, link, update the table. -/
def cgB : Stmt :=
  .seq (block [.addN 4431 4422 4429, .loadN 4432 4431, .addN 4435 4424 4432, .loadN 4436 4435])
    (.seq (.ifLtN 4428 4436 cgC .skip) (block [.addN 4432 4429 4427, .storeN 4435 4432]))

/-- One index of the scan. -/
def cgBody : Stmt :=
  .seq cgA (.seq (.ifLtN 4428 4432 .skip cgB)
    (block [.addN 4429 4429 4427, .addN 4430 4430 4427, .addN 4430 4430 4427,
      .addN 4430 4430 4427]))

/-- **The graph `cgAdj` in CSR form.** -/
def cgBuild : Stmt :=
  .seq (block [.constN 4427 1, .constN 4428 0, .constN 4429 0, .constN 4430 0])
    (.seq (.whileLtN 4429 4420 cgBody) (block [.addN 4431 4425 4429, .storeN 4431 4430]))

section Exec

variable {P : Input} {W : ℕ}

theorem cgA_exec (c : Config) (hc : WordsBounded W c) {RVb YFb OFFb ADJb j o : ℕ}
    (r1 : c.nreg 4421 = RVb) (r3 : c.nreg 4423 = YFb) (r5 : c.nreg 4425 = OFFb)
    (r6 : c.nreg 4426 = ADJb) (r7 : c.nreg 4427 = 1) (r9 : c.nreg 4429 = j)
    (r10 : c.nreg 4430 = o) (d1 : RVb + j < OFFb) (d2 : YFb + j < OFFb) (d3 : OFFb + j < ADJb)
    (w1 : ADJb + o + 2 ≤ W) :
    ∃ c' k, Exec P W cgA c c' k ∧ k = 12 ∧
      c'.nmem = cgW1 c.nmem OFFb ADJb j o (c.nmem (RVb + j)) ∧
      c'.nreg 4432 = c.nmem (YFb + j) ∧ c'.nreg 4433 = ADJb + o + 1 ∧
      (∀ x, (x < 4431 ∨ 4434 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cgA
  exec_block
  all_goals try (config_simp; simp only [r1, r3, r5, r6, r7, r9, r10]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r1, r3, r5, r6, r7, r9, r10, cgW1]
    rw [upd_other _ _ _ (by omega)]
  · config_simp; simp only [r1, r3, r5, r6, r7, r9, r10, upd_apply]
    split_ifs <;> first | omega | rfl
  · config_simp; simp only [r6, r7, r10]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem cgC_exec (c : Config) (hc : WordsBounded W c) {ADJb j o p : ℕ}
    (r6 : c.nreg 4426 = ADJb) (r7 : c.nreg 4427 = 1) (r9 : c.nreg 4429 = j)
    (r13 : c.nreg 4433 = ADJb + o + 1) (r16 : c.nreg 4436 = p) (hp : 0 < p)
    (w1 : ADJb + 3 * p ≤ W) :
    ∃ c' k, Exec P W cgC c c' k ∧ k = 8 ∧ c'.nmem = cgW3 c.nmem ADJb o j p ∧
      (∀ x, (x < 4431 ∨ 4432 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cgC
  exec_block
  all_goals try (config_simp; simp only [r6, r7, r9, r13, r16]; omega)
  refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r6, r7, r9, r13, r16, cgW3]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem cgB_exec (c : Config) (hc : WordsBounded W c) {TKb LSb ADJb j o : ℕ}
    (r2 : c.nreg 4422 = TKb) (r4 : c.nreg 4424 = LSb) (r6 : c.nreg 4426 = ADJb)
    (r7 : c.nreg 4427 = 1) (r8 : c.nreg 4428 = 0) (r9 : c.nreg 4429 = j)
    (r13 : c.nreg 4433 = ADJb + o + 1)
    (w1 : TKb + j ≤ W) (w2 : LSb + c.nmem (TKb + j) ≤ W)
    (w3 : ADJb + 3 * c.nmem (LSb + c.nmem (TKb + j)) ≤ W) (w4 : j + 1 ≤ W) :
    ∃ c' k, Exec P W cgB c c' k ∧ k ≤ 15 ∧
      (0 < c.nmem (LSb + c.nmem (TKb + j)) → c'.nmem = cgW2 (cgW3 c.nmem ADJb o j
        (c.nmem (LSb + c.nmem (TKb + j)))) LSb (c.nmem (TKb + j)) j) ∧
      (c.nmem (LSb + c.nmem (TKb + j)) = 0 → c'.nmem = cgW2 c.nmem LSb (c.nmem (TKb + j)) j) ∧
      (∀ x, x ≠ 4431 → x ≠ 4432 → x ≠ 4435 → x ≠ 4436 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cgB
  set key := c.nmem (TKb + j) with hkey
  set p := c.nmem (LSb + key) with hp
  obtain ⟨c₁, k₁, e₁, hk₁, g5, g6, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.addN 4431 4422 4429, .loadN 4432 4431, .addN 4435 4424 4432,
        .loadN 4436 4435]) c c₁ k₁ ∧ k₁ = 4 ∧ c₁.nreg 4435 = LSb + key ∧ c₁.nreg 4436 = p ∧
      (∀ x, x ≠ 4431 → x ≠ 4432 → x ≠ 4435 → x ≠ 4436 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try (config_simp; simp only [r2, r4, r9, ← hkey]; omega)
    refine ⟨rfl, ?_, ?_, fun x a b d e => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [r2, r4, r9, ← hkey]
    · config_simp; simp only [r2, r4, r9, ← hkey, ← hp]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 4431 → x ≠ 4432 → x ≠ 4435 → x ≠ 4436 → c₁.nreg x = c.nreg x := gn₁
  obtain ⟨c₂, k₂, e₂, hk₂, H1, H2, gn₂, g35₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
      Exec P W (.ifLtN 4428 4436 cgC .skip) c₁ c₂ k₂ ∧ k₂ ≤ 9 ∧
      (0 < p → c₂.nmem = cgW3 c.nmem ADJb o j p) ∧ (p = 0 → c₂.nmem = c.nmem) ∧
      (∀ x, x ≠ 4431 → x ≠ 4432 → x ≠ 4435 → x ≠ 4436 → c₂.nreg x = c.nreg x) ∧
      (c₂.nreg 4435 = LSb + key) ∧ c₂.rreg = c.rreg ∧ c₂.rmem = c.rmem ∧
      c₂.output = c.output := by
    by_cases hh : c₁.nreg 4428 < c₁.nreg 4436
    · have hp0 : 0 < p := by rw [q _ (by omega) (by omega) (by omega) (by omega), r8, g6] at hh
                             exact hh
      obtain ⟨c₂, k₂, e₂, hk₂, hm₂, hn₂, hr₂, hrm₂, ho₂⟩ := cgC_exec (P := P) c₁ hw₁
        (by rw [q _ (by omega) (by omega) (by omega) (by omega), r6])
        (by rw [q _ (by omega) (by omega) (by omega) (by omega), r7])
        (by rw [q _ (by omega) (by omega) (by omega) (by omega), r9])
        (by rw [q _ (by omega) (by omega) (by omega) (by omega), r13]) g6 hp0 w3
      rw [gm₁] at hm₂
      refine ⟨c₂, k₂ + 1, .ifLtN_true hh e₂, by omega, fun _ => hm₂, fun h => absurd h (by omega),
        fun x a b d e => by rw [hn₂ x (by omega), q x a b d e], by rw [hn₂ _ (by omega), g5],
        by rw [hr₂, gr₁], by rw [hrm₂, grm₁], by rw [ho₂, go₁]⟩
    · have hp0 : p = 0 := by
        rw [q _ (by omega) (by omega) (by omega) (by omega), r8, g6] at hh; omega
      exact ⟨c₁, 2, .ifLtN_false hh (.skip hw₁), by omega, fun h => absurd hp0 (by omega),
        fun _ => gm₁, q, g5, gr₁, grm₁, go₁⟩
  have hw₂ := e₂.wb_right
  obtain ⟨c₃, k₃, e₃, hk₃, hm₃, hn₃, hr₃, hrm₃, ho₃⟩ : ∃ c₃ k₃,
      Exec P W (block [.addN 4432 4429 4427, .storeN 4435 4432]) c₂ c₃ k₃ ∧ k₃ = 2 ∧
      c₃.nmem = cgW2 c₂.nmem LSb key j ∧ (∀ x, x ≠ 4432 → c₃.nreg x = c₂.nreg x) ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have p7 : c₂.nreg 4427 = 1 := by rw [gn₂ _ (by omega) (by omega) (by omega) (by omega), r7]
    have p9 : c₂.nreg 4429 = j := by rw [gn₂ _ (by omega) (by omega) (by omega) (by omega), r9]
    exec_block
    all_goals try ((try config_simp); (try simp only [p7, p9, g35₂]); omega)
    refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl⟩
    · config_simp; simp only [p7, p9, g35₂, cgW2]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, fun h => ?_, fun h => ?_,
    fun x a b d e => by rw [hn₃ x b, gn₂ x a b d e], by rw [hr₃, gr₂], by rw [hrm₃, grm₂],
    by rw [ho₃, go₂]⟩
  · rw [hm₃, H1 h]
  · rw [hm₃, H2 h]

/-- **One index of the scan**: the memory invariant `CgMem` advances. -/
theorem cgBody_exec (c : Config) (hc : WordsBounded W c) {m₀ : ℕ → ℕ}
    {n nk RVb TKb YFb LSb OFFb ADJb j : ℕ} (hL : CgLay n nk RVb TKb YFb LSb OFFb ADJb)
    (hW : ADJb + 3 * n + 1 ≤ W) (hTK : ∀ i < n, m₀ (TKb + i) < nk)
    (r1 : c.nreg 4421 = RVb) (r2 : c.nreg 4422 = TKb) (r3 : c.nreg 4423 = YFb)
    (r4 : c.nreg 4424 = LSb) (r5 : c.nreg 4425 = OFFb) (r6 : c.nreg 4426 = ADJb)
    (r7 : c.nreg 4427 = 1) (r8 : c.nreg 4428 = 0) (r9 : c.nreg 4429 = j)
    (r10 : c.nreg 4430 = 3 * j) (hj : j < n)
    (hM : CgMem m₀ c.nmem n nk RVb TKb YFb LSb OFFb ADJb j) :
    ∃ c' k, Exec P W cgBody c c' k ∧ k ≤ 33 ∧ c'.nreg 4429 = j + 1 ∧
      c'.nreg 4430 = 3 * (j + 1) ∧ CgMem m₀ c'.nmem n nk RVb TKb YFb LSb OFFb ADJb (j + 1) ∧
      (∀ x, (x < 4429 ∨ 4436 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hLay := hL
  obtain ⟨l1, l2, l3, l4, l5⟩ := hL
  unfold cgBody
  have eRV : c.nmem (RVb + j) = m₀ (RVb + j) := hM.frame _ (by omega) (by omega) (by omega)
  have eYF : c.nmem (YFb + j) = m₀ (YFb + j) := hM.frame _ (by omega) (by omega) (by omega)
  have eTK : c.nmem (TKb + j) = m₀ (TKb + j) := hM.frame _ (by omega) (by omega) (by omega)
  have hk := hTK j hj
  obtain ⟨c₁, k₁, e₁, hk₁, hm₁, g32, g33, gn₁, gr₁, grm₁, go₁⟩ := cgA_exec (P := P) c hc r1 r3 r5
    r6 r7 r9 r10 (by omega) (by omega) (by omega) (by omega)
  rw [eRV] at hm₁
  rw [eYF] at g32
  have hw₁ := e₁.wb_right
  have q : ∀ x, (x < 4431 ∨ 4434 < x) → c₁.nreg x = c.nreg x := gn₁
  -- the branch
  obtain ⟨c₂, k₂, e₂, hk₂, hM₂, gn₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
      Exec P W (.ifLtN 4428 4432 .skip cgB) c₁ c₂ k₂ ∧ k₂ ≤ 17 ∧
      CgMem m₀ c₂.nmem n nk RVb TKb YFb LSb OFFb ADJb (j + 1) ∧
      (∀ x, (x < 4431 ∨ 4436 < x) → c₂.nreg x = c.nreg x) ∧
      c₂.rreg = c.rreg ∧ c₂.rmem = c.rmem ∧ c₂.output = c.output := by
    by_cases hh : c₁.nreg 4428 < c₁.nreg 4432
    · have hy : 0 < m₀ (YFb + j) := by rw [q _ (by omega), r8, g32] at hh; exact hh
      refine ⟨c₁, 1, .ifLtN_true hh (.skip hw₁), by omega, by rw [hm₁]; exact cgMem_in hLay hM hj hy,
        fun x hx => q x (by omega), gr₁, grm₁, go₁⟩
    · have hy : m₀ (YFb + j) = 0 := by rw [q _ (by omega), r8, g32] at hh; omega
      have eTK₁ : c₁.nmem (TKb + j) = m₀ (TKb + j) := by
        rw [hm₁, cgW1_other (by omega) (by omega) (by omega) (by omega), eTK]
      have eLS₁ : c₁.nmem (LSb + m₀ (TKb + j)) = c.nmem (LSb + m₀ (TKb + j)) := by
        rw [hm₁, cgW1_other (by omega) (by omega) (by omega) (by omega)]
      have hpj : c.nmem (LSb + m₀ (TKb + j)) ≤ j := by
        rw [hM.ls _ hk]; exact lastF_le _ _ _ _
      obtain ⟨c₂, k₂, e₂, hk₂, H1, H2, hn₂, hr₂, hrm₂, ho₂⟩ := cgB_exec (P := P) (o := 3 * j) c₁ hw₁
        (by rw [q _ (by omega), r2]) (by rw [q _ (by omega), r4]) (by rw [q _ (by omega), r6])
        (by rw [q _ (by omega), r7]) (by rw [q _ (by omega), r8]) (by rw [q _ (by omega), r9])
        g33 (by omega) (by rw [eTK₁]; omega) (by rw [eTK₁, eLS₁]; omega) (by omega)
      rw [eTK₁, eLS₁] at H1 H2
      refine ⟨c₂, k₂ + 2, .ifLtN_false hh e₂, by omega, ?_, fun x hx => ?_, by rw [hr₂, gr₁],
        by rw [hrm₂, grm₁], by rw [ho₂, go₁]⟩
      · by_cases hp : 0 < c.nmem (LSb + m₀ (TKb + j))
        · rw [H1 hp, hm₁]
          exact cgMem_pos hLay hM hj hy hk hp
        · rw [H2 (by omega), hm₁]
          exact cgMem_zero hLay hM hj hy hk (by omega)
      · rw [hn₂ x (by omega) (by omega) (by omega) (by omega), q x (by omega)]
  have hw₂ := e₂.wb_right
  obtain ⟨c₃, k₃, e₃, hk₃, h29, h30, hn₃, hm₃, hr₃, hrm₃, ho₃⟩ : ∃ c₃ k₃,
      Exec P W (block [.addN 4429 4429 4427, .addN 4430 4430 4427, .addN 4430 4430 4427,
        .addN 4430 4430 4427]) c₂ c₃ k₃ ∧ k₃ = 4 ∧ c₃.nreg 4429 = j + 1 ∧
      c₃.nreg 4430 = 3 * (j + 1) ∧ (∀ x, x ≠ 4429 → x ≠ 4430 → c₃.nreg x = c₂.nreg x) ∧
      c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have p7 : c₂.nreg 4427 = 1 := by rw [gn₂ _ (by omega), r7]
    have p9 : c₂.nreg 4429 = j := by rw [gn₂ _ (by omega), r9]
    have p10 : c₂.nreg 4430 = 3 * j := by rw [gn₂ _ (by omega), r10]
    exec_block
    all_goals try ((try config_simp); (try simp only [p7, p9, p10]); omega)
    refine ⟨rfl, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [p7, p9]
    · config_simp; simp only [p7, p10]; omega
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, h29, h30, by rw [hm₃]; exact hM₂,
    fun x hx => ?_, by rw [hr₃, gr₂], by rw [hrm₃, grm₂], by rw [ho₃, go₂]⟩
  rw [hn₃ x (by omega) (by omega), gn₂ x (by omega)]

/-- **The graph `cgAdj` in CSR form on the machine**: within `35 n + 8` steps the memory holds
`CgMem … n` (offsets `3 i`, slots `rv i`, `cgS1 i`, `cgS2 n i`, the table, the rest unchanged)
and `OFF[n] = 3 n`; registers outside `4427 … 4436` kept. -/
theorem cgBuild_exec (c : Config) (hc : WordsBounded W c)
    {n nk RVb TKb YFb LSb OFFb ADJb : ℕ} (hL : CgLay n nk RVb TKb YFb LSb OFFb ADJb)
    (hW : ADJb + 3 * n + 1 ≤ W) (hTK : ∀ i < n, c.nmem (TKb + i) < nk)
    (hLS : ∀ k < nk, c.nmem (LSb + k) = 0)
    (r0 : c.nreg 4420 = n) (r1 : c.nreg 4421 = RVb) (r2 : c.nreg 4422 = TKb)
    (r3 : c.nreg 4423 = YFb) (r4 : c.nreg 4424 = LSb) (r5 : c.nreg 4425 = OFFb)
    (r6 : c.nreg 4426 = ADJb) :
    ∃ c' k, Exec P W cgBuild c c' k ∧ k ≤ 35 * n + 8 ∧
      CgMem c.nmem c'.nmem n nk RVb TKb YFb LSb OFFb ADJb n ∧ c'.nmem (OFFb + n) = 3 * n ∧
      (∀ x, (x < 4427 ∨ 4436 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hLay := hL
  obtain ⟨l1, l2, l3, l4, l5⟩ := hL
  unfold cgBuild
  obtain ⟨c₁, k₁, e₁, hk₁, g7, g8, g9, g10, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 4427 1, .constN 4428 0, .constN 4429 0, .constN 4430 0]) c c₁ k₁ ∧
      k₁ = 4 ∧ c₁.nreg 4427 = 1 ∧ c₁.nreg 4428 = 0 ∧ c₁.nreg 4429 = 0 ∧ c₁.nreg 4430 = 0 ∧
      (∀ x, (x < 4427 ∨ 4430 < x) → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; done)
    config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, (x < 4427 ∨ 4430 < x) → c₁.nreg x = c.nreg x := gn₁
  let J : ℕ → Config → Prop := fun j c' =>
    (∀ x, (x < 4429 ∨ 4436 < x) → c'.nreg x = c₁.nreg x) ∧ c'.nreg 4430 = 3 * j ∧
    CgMem c.nmem c'.nmem n nk RVb TKb YFb LSb OFFb ADJb j ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h9₂, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P) (a := 4429)
    (b := 4420) (body := cgBody) J (B := 33) c₁ hw₁ g9 (by rw [q _ (by omega), r0])
    (Nat.zero_le n) ⟨fun _ _ => rfl, by rw [g10], by rw [gm₁]; exact cgMem_start hLS, rfl, rfl,
      rfl⟩
    (fun j c' hlo hhi hw h9 h0 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 4429 ∨ 4436 < x) → c'.nreg x = c₁.nreg x := j1
      obtain ⟨c'', t, ex, ht, h9', h10', hM', hn', hr', hrm', ho'⟩ := cgBody_exec (P := P) c' hw
        hLay hW hTK (by rw [f _ (by omega), q _ (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega), r2]) (by rw [f _ (by omega), q _ (by omega), r3])
        (by rw [f _ (by omega), q _ (by omega), r4]) (by rw [f _ (by omega), q _ (by omega), r5])
        (by rw [f _ (by omega), q _ (by omega), r6]) (by rw [f _ (by omega), g7])
        (by rw [f _ (by omega), g8]) h9 j2 hhi j3
      exact ⟨c'', t, ex, ht, h9', by rw [hn' _ (by omega)]; exact h0,
        fun x hx => by rw [hn' x hx, f x hx], h10', hM', by rw [hr', j4], by rw [hrm', j5],
        by rw [ho', j6]⟩)
  obtain ⟨c₃, k₃, e₃, hk₃, hm₃, hn₃, hr₃, hrm₃, ho₃⟩ : ∃ c₃ k₃,
      Exec P W (block [.addN 4431 4425 4429, .storeN 4431 4430]) c₂ c₃ k₃ ∧ k₃ = 2 ∧
      c₃.nmem = upd c₂.nmem (OFFb + n) (3 * n) ∧ (∀ x, x ≠ 4431 → c₃.nreg x = c₂.nreg x) ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have p5 : c₂.nreg 4425 = OFFb := by rw [j1 _ (by omega), q _ (by omega), r5]
    exec_block
    all_goals try ((try config_simp); (try simp only [p5, h9₂]); omega)
    refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl⟩
    · config_simp; simp only [p5, h9₂, j2]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, by rw [hm₃]; exact cgMem_last hLay j3,
    by rw [hm₃, upd_same], fun x hx => ?_, by rw [hr₃, j4, gr₁], by rw [hrm₃, j5, grm₁],
    by rw [ho₃, j6, go₁]⟩
  rw [hn₃ x (by omega), j1 x (by omega), q x (by omega)]

end Exec

/-! ### The labelling of the components -/

section CC

variable {m₀ m : ℕ → ℕ} {n nk RVb TKb YFb LSb OFFb ADJb : ℕ}

lemma cg_off (hM : CgMem m₀ m n nk RVb TKb YFb LSb OFFb ADJb n) (hlast : m (OFFb + n) = 3 * n)
    {u : ℕ} (hu : u ≤ n) : m (OFFb + u) = 3 * u := by
  rcases Nat.lt_or_eq_of_le hu with h | rfl
  · exact hM.off u h
  · exact hlast

/-- **The CSR adjacency written by `cgBuild` is `cgAdj`.** -/
lemma bfAdj_cg (hM : CgMem m₀ m n nk RVb TKb YFb LSb OFFb ADJb n)
    (hlast : m (OFFb + n) = 3 * n) (u v : ℕ) :
    bfAdj m n OFFb ADJb u v ↔
      cgAdj (cgKey m₀ TKb) (cgYf m₀ YFb) n (fun i => m₀ (RVb + i)) u v := by
  constructor
  · rintro ⟨hu, i, h1, h2, rfl⟩
    rw [cg_off hM hlast (by omega)] at h1
    rw [show OFFb + u + 1 = OFFb + (u + 1) by omega, cg_off hM hlast (by omega)] at h2
    refine ⟨hu, ?_⟩
    obtain ⟨r, hr, rfl⟩ : ∃ r < 3, i = 3 * u + r := ⟨i - 3 * u, by omega, by omega⟩
    interval_cases r
    · exact Or.inl (by rw [Nat.add_zero, hM.s0 u hu])
    · exact Or.inr (Or.inl (by rw [← add_assoc, hM.s1 u hu]))
    · exact Or.inr (Or.inr (by rw [← add_assoc, hM.s2 u hu]))
  · rintro ⟨hu, h | h | h⟩
    · refine ⟨hu, 3 * u, ?_, ?_, ?_⟩
      · rw [cg_off hM hlast (by omega)]
      · rw [show OFFb + u + 1 = OFFb + (u + 1) by omega, cg_off hM hlast (by omega)]; omega
      · rw [hM.s0 u hu, h]
    · refine ⟨hu, 3 * u + 1, ?_, ?_, ?_⟩
      · rw [cg_off hM hlast (by omega)]; omega
      · rw [show OFFb + u + 1 = OFFb + (u + 1) by omega, cg_off hM hlast (by omega)]; omega
      · rw [← add_assoc, hM.s1 u hu, h]
    · refine ⟨hu, 3 * u + 2, ?_, ?_, ?_⟩
      · rw [cg_off hM hlast (by omega)]; omega
      · rw [show OFFb + u + 1 = OFFb + (u + 1) by omega, cg_off hM hlast (by omega)]; omega
      · rw [← add_assoc, hM.s2 u hu, h]

/-- The graph written by `cgBuild` meets the input conditions of `bfProg`. -/
lemma bfIn_cg (hM : CgMem m₀ m n nk RVb TKb YFb LSb OFFb ADJb n)
    (hlast : m (OFFb + n) = 3 * n) (hrv : RvOK n (fun i => m₀ (RVb + i))) :
    BfIn m n OFFb ADJb (3 * n) := by
  refine ⟨fun u hu => ?_, hlast, fun u v h => ?_, fun u v h => ?_⟩
  · rw [cg_off hM hlast (by omega), show OFFb + u + 1 = OFFb + (u + 1) by omega,
      cg_off hM hlast (by omega)]; omega
  · exact cgAdj_lt hrv ((bfAdj_cg hM hlast u v).1 h)
  · exact (bfAdj_cg hM hlast v u).2 (cgAdj_symm hrv ((bfAdj_cg hM hlast u v).1 h))

end CC

/-- **The components off a hole on the machine**: the graph, then the labels. -/
def ccProg : Stmt := .seq cgBuild bfProg

section Exec

variable {P : Input} {W : ℕ}

/-- **`ccProg`**: under the layouts `CgLay` and `BfLay n (3 n) …` (the label and queue arrays
after the slots), the table and the labels zero, within `104 n + 16` steps,
`LAB[u] = LAB[v] ↔ ReflTransGen (cgAdj key yf n rv) u v` and `0 < LAB[u] ≤ n` for `u, v < n`
(`rv i = RV[i]`, `key i = TK[i]`, `yf i = (0 < YF[i])`); memory outside the table, the offsets,
the slots, the labels and the queue kept; registers outside `4405 … 4436` kept. -/
theorem ccProg_exec (c : Config) (hc : WordsBounded W c)
    {n nk RVb TKb YFb LSb OFFb ADJb LABb Qb : ℕ} (hL : CgLay n nk RVb TKb YFb LSb OFFb ADJb)
    (hB : BfLay n (3 * n) OFFb ADJb LABb Qb W) (hTK : ∀ i < n, c.nmem (TKb + i) < nk)
    (hrv : RvOK n (fun i => c.nmem (RVb + i)))
    (hLS : ∀ k < nk, c.nmem (LSb + k) = 0) (hLAB : ∀ u < n, c.nmem (LABb + u) = 0)
    (r0 : c.nreg 4420 = n) (r1 : c.nreg 4421 = RVb) (r2 : c.nreg 4422 = TKb)
    (r3 : c.nreg 4423 = YFb) (r4 : c.nreg 4424 = LSb) (r5 : c.nreg 4425 = OFFb)
    (r6 : c.nreg 4426 = ADJb) (s0 : c.nreg 4400 = n) (s1 : c.nreg 4401 = OFFb)
    (s2 : c.nreg 4402 = ADJb) (s3 : c.nreg 4403 = LABb) (s4 : c.nreg 4404 = Qb) :
    ∃ c' k, Exec P W ccProg c c' k ∧ k ≤ 104 * n + 16 ∧
      (∀ u < n, ∀ v < n, (c'.nmem (LABb + u) = c'.nmem (LABb + v) ↔
        ReflTransGen (cgAdj (cgKey c.nmem TKb) (cgYf c.nmem YFb) n (fun i => c.nmem (RVb + i)))
          u v)) ∧
      (∀ u < n, 0 < c'.nmem (LABb + u) ∧ c'.nmem (LABb + u) ≤ n) ∧
      (∀ a, ¬ (LSb ≤ a ∧ a < LSb + nk) → ¬ (OFFb ≤ a ∧ a < ADJb + 3 * n) →
        ¬ (LABb ≤ a ∧ a < Qb + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4405 ∨ 4436 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hLc := hL
  have hBc := hB
  obtain ⟨l1, l2, l3, l4, l5⟩ := hL
  obtain ⟨b1, b2, b3, b4⟩ := hB
  obtain ⟨c₁, k₁, e₁, hk₁, hM₁, hlast₁, hn₁, hr₁, hrm₁, ho₁⟩ := cgBuild_exec (P := P) c hc hLc
    (by omega) hTK hLS r0 r1 r2 r3 r4 r5 r6
  have hw₁ := e₁.wb_right
  have hG := bfIn_cg hM₁ hlast₁ hrv
  obtain ⟨c₂, k₂, e₂, hk₂, H1, H2, H3, hn₂, hr₂, hrm₂, ho₂⟩ := bfProg_exec (P := P) c₁ hw₁ hBc hG
    (by rw [hn₁ _ (by omega), s0]) (by rw [hn₁ _ (by omega), s1]) (by rw [hn₁ _ (by omega), s2])
    (by rw [hn₁ _ (by omega), s3]) (by rw [hn₁ _ (by omega), s4])
    (fun u hu => by rw [hM₁.frame _ (by omega) (by omega) (by omega), hLAB u hu])
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, fun u hu v hv => ?_, H2, fun a h1 h2 h3 => ?_,
    fun x hx => ?_, by rw [hr₂, hr₁], by rw [hrm₂, hrm₁], by rw [ho₂, ho₁]⟩
  · rw [H1 u hu v hv]
    have : bfAdj c₁.nmem n OFFb ADJb = cgAdj (cgKey c.nmem TKb) (cgYf c.nmem YFb) n
        (fun i => c.nmem (RVb + i)) := by
      funext u v; exact propext (bfAdj_cg hM₁ hlast₁ u v)
    rw [this]
  · rw [H3 a (fun h => h3 ⟨h.1, by omega⟩) (fun h => h3 ⟨by omega, h.2⟩)]
    exact hM₁.frame a h1 (fun h => h2 ⟨h.1, by omega⟩) (fun h => h2 ⟨by omega, h.2⟩)
  · rw [hn₂ x (by omega), hn₁ x (by omega)]

/-- **The components off a hole, labelled on the machine**: for an enumeration `e` of the darts
`N` described by the input arrays (`CgEnum`) and `Y` closed under the holes, after `ccProg`
(`104 n + 16` steps), `LAB[i] = LAB[j] ↔ e j ∈ comp M N Hs Y (e i)` for `i, j < n`. -/
theorem ccProg_comp {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {M : CombMap D V F} {N : Finset D} {Hs : List (Finset V)}
    {Y : Finset V} {e : ℕ → D} (hY : HClosed Hs Y)
    (c : Config) (hc : WordsBounded W c)
    {n nk RVb TKb YFb LSb OFFb ADJb LABb Qb : ℕ} (hL : CgLay n nk RVb TKb YFb LSb OFFb ADJb)
    (hB : BfLay n (3 * n) OFFb ADJb LABb Qb W) (hTK : ∀ i < n, c.nmem (TKb + i) < nk)
    (hE : CgEnum M N Hs Y n e (fun i => c.nmem (RVb + i)) (cgKey c.nmem TKb) (cgYf c.nmem YFb))
    (hLS : ∀ k < nk, c.nmem (LSb + k) = 0) (hLAB : ∀ u < n, c.nmem (LABb + u) = 0)
    (r0 : c.nreg 4420 = n) (r1 : c.nreg 4421 = RVb) (r2 : c.nreg 4422 = TKb)
    (r3 : c.nreg 4423 = YFb) (r4 : c.nreg 4424 = LSb) (r5 : c.nreg 4425 = OFFb)
    (r6 : c.nreg 4426 = ADJb) (s0 : c.nreg 4400 = n) (s1 : c.nreg 4401 = OFFb)
    (s2 : c.nreg 4402 = ADJb) (s3 : c.nreg 4403 = LABb) (s4 : c.nreg 4404 = Qb) :
    ∃ c' k, Exec P W ccProg c c' k ∧ k ≤ 104 * n + 16 ∧
      (∀ i < n, ∀ j < n, (c'.nmem (LABb + i) = c'.nmem (LABb + j) ↔
        e j ∈ comp M N Hs Y (e i))) ∧
      (∀ u < n, 0 < c'.nmem (LABb + u) ∧ c'.nmem (LABb + u) ≤ n) ∧
      (∀ a, ¬ (LSb ≤ a ∧ a < LSb + nk) → ¬ (OFFb ≤ a ∧ a < ADJb + 3 * n) →
        ¬ (LABb ≤ a ∧ a < Qb + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4405 ∨ 4436 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', k, ex, hk, H1, H2, H3, H4, H5, H6, H7⟩ := ccProg_exec (P := P) c hc hL hB hTK
    hE.rvOK hLS hLAB r0 r1 r2 r3 r4 r5 r6 s0 s1 s2 s3 s4
  exact ⟨c', k, ex, hk, fun i hi j hj => by rw [H1 i hi j hj, mem_comp_iff_cgAdj hY hE hi hj],
    H2, H3, H4, H5, H6, H7⟩

end Exec

end BKMNW

end PlanarFlow
