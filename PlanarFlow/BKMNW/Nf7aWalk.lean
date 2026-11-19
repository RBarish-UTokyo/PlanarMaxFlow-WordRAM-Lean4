module

public import PlanarFlow.BKMNW.Nf7aCw
public import PlanarFlow.BKMNW.TwoGroupsProg

/-!
# The corner walk of `fixP` on the machine

**`cwProg`** walks `N = r9400` steps around the path from the dart index `t₀ = mem[r9402]` (the
first dart of the path): at the index `t` it reads the label `f = FL[t]` and the mark `MK[f]`;
if `MK[f] = 1` it records the corner (`MK[f] := cnt + 2`, `BT[cnt] := t`, `cnt := cnt + 1`);
then `t := NX[t]` if `ON[t] > 0` (a dart of the path) and `t := SG[t]` otherwise (`twF`).

Registers: `9400 = N`, `9402` (address of `t₀`), bases `9404 = NX`, `9405 = FL`, `9406 = ON`,
`9407 = MK`, `9410 = BT`, `9431 = SG`; written `9439 … 9449` (`9440 = n`, `9441 = t`,
`9442 = cnt`, `9443 = 1`, `9444 = 2`, `9445 = 0`).

* `twF` (the step of the walk on the arrays), `cwBody_exec` (`≤ 24` steps);
* **`cwProg_exec`** (`26 N + 10` steps): the registers `t = twF^[N] t₀`, `cnt`, the marks
  `MK[a] = (cwRun g tt mk0 N).mks a` (`a ≤ m`) and the corners `BT[x] = (cwRun …).bt x`
  (`x < cnt`) of the model `cwRun` (`Nf7aCw.lean`) with `g n = FL[twF^[n] t₀]`,
  `tt n = twF^[n] t₀`, `mk0 a = MK[a]`; all other memory and registers kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- The step of the walk on the arrays. -/
def twF (NXb SGb ONb : ℕ) (mem : ℕ → ℕ) (i : ℕ) : ℕ :=
  if 0 < mem (ONb + i) then mem (NXb + i) else mem (SGb + i)

/-! ### The program -/

/-- `f := FL[t]`, `v := MK[f]`, `o := ON[t]`. -/
def cwA : Stmt :=
  block [.addN 9446 9405 9441, .loadN 9446 9446, .addN 9447 9407 9446, .loadN 9447 9447,
    .addN 9448 9406 9441, .loadN 9448 9448]

/-- The next index into `9439`. -/
def fcwN : Stmt :=
  .ifLtN 9445 9448 (block [.addN 9449 9404 9441, .loadN 9439 9449])
    (block [.addN 9449 9431 9441, .loadN 9439 9449])

/-- Record the corner. -/
def cwRec : Stmt :=
  block [.addN 9448 9442 9444, .addN 9449 9407 9446, .storeN 9449 9448, .addN 9449 9410 9442,
    .storeN 9449 9441, .addN 9442 9442 9443]

/-- Record when `v = 1`. -/
def cwR : Stmt := .ifLtN 9447 9444 (.ifLtN 9445 9447 cwRec .skip) .skip

/-- `t := next`, `n := n + 1`. -/
def cwD : Stmt := block [.copyN 9441 9439, .addN 9440 9440 9443]

/-- One step of the walk. -/
def cwBody : Stmt := .seq cwA (.seq fcwN (.seq cwR cwD))

/-- The start. -/
def cwInit : Stmt :=
  block [.constN 9440 0, .loadN 9441 9402, .constN 9442 0, .constN 9443 1, .constN 9444 2,
    .constN 9445 0]

/-- **The corner walk.** -/
def cwProg : Stmt := .seq cwInit (.whileLtN 9440 9400 cwBody)

/-! ### The run -/

variable {P : Input} {W : ℕ}

theorem cwA_exec (c : Config) (hc : WordsBounded W c) {FLb MKb ONb t : ℕ}
    (r05 : c.nreg 9405 = FLb) (r06 : c.nreg 9406 = ONb) (r07 : c.nreg 9407 = MKb)
    (r41 : c.nreg 9441 = t) (h1 : FLb + t ≤ W) (h2 : MKb + c.nmem (FLb + t) ≤ W)
    (h3 : ONb + t ≤ W) :
    ∃ c' k, Exec P W cwA c c' k ∧ k = 6 ∧ c'.nreg 9446 = c.nmem (FLb + t) ∧
      c'.nreg 9447 = c.nmem (MKb + c.nmem (FLb + t)) ∧ c'.nreg 9448 = c.nmem (ONb + t) ∧
      (∀ r, (r < 9446 ∨ 9448 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cwA
  exec_block
  all_goals try ((try config_simp); (try simp only [r05, r06, r07, r41]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r05, r06, r07, r41])
  simp only [upd_apply]; split_ifs <;> omega

theorem fcwN_exec (c : Config) (hc : WordsBounded W c) {NXb SGb ONb t : ℕ}
    (r04 : c.nreg 9404 = NXb) (r31 : c.nreg 9431 = SGb) (r41 : c.nreg 9441 = t)
    (r45 : c.nreg 9445 = 0) (r48 : c.nreg 9448 = c.nmem (ONb + t)) (h1 : NXb + t ≤ W)
    (h2 : SGb + t ≤ W) :
    ∃ c' k, Exec P W fcwN c c' k ∧ k ≤ 4 ∧ c'.nreg 9439 = twF NXb SGb ONb c.nmem t ∧
      (∀ r, r ≠ 9439 → r ≠ 9449 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fcwN
  by_cases ho : 0 < c.nmem (ONb + t)
  · obtain ⟨c', k, e, hk, g39, gk, gm, gr, grm, go⟩ : ∃ c' k,
        Exec P W (block [.addN 9449 9404 9441, .loadN 9439 9449]) c c' k ∧ k = 2 ∧
        c'.nreg 9439 = c.nmem (NXb + t) ∧ (∀ r, r ≠ 9439 → r ≠ 9449 → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
      exec_block
      all_goals try ((try config_simp); (try simp only [r04, r41]); omega)
      refine ⟨rfl, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
      all_goals config_simp
      · simp only [r04, r41]
      · simp only [upd_apply]; split_ifs <;> omega
    have hcond : c.nreg 9445 < c.nreg 9448 := by rw [r45, r48]; exact ho
    refine ⟨c', _, .ifLtN_true hcond e, by omega, ?_, gk, gm, gr, grm, go⟩
    rw [g39]; simp only [twF, ho, ↓reduceIte]
  · obtain ⟨c', k, e, hk, g39, gk, gm, gr, grm, go⟩ : ∃ c' k,
        Exec P W (block [.addN 9449 9431 9441, .loadN 9439 9449]) c c' k ∧ k = 2 ∧
        c'.nreg 9439 = c.nmem (SGb + t) ∧ (∀ r, r ≠ 9439 → r ≠ 9449 → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
      exec_block
      all_goals try ((try config_simp); (try simp only [r31, r41]); omega)
      refine ⟨rfl, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
      all_goals config_simp
      · simp only [r31, r41]
      · simp only [upd_apply]; split_ifs <;> omega
    have hcond : ¬ c.nreg 9445 < c.nreg 9448 := by rw [r45, r48]; exact ho
    refine ⟨c', _, .ifLtN_false hcond e, by omega, ?_, gk, gm, gr, grm, go⟩
    rw [g39]; simp only [twF, ho, ↓reduceIte]

theorem cwRec_exec (c : Config) (hc : WordsBounded W c) {MKb BTb t cnt f : ℕ}
    (r07 : c.nreg 9407 = MKb) (r10 : c.nreg 9410 = BTb) (r41 : c.nreg 9441 = t)
    (r42 : c.nreg 9442 = cnt) (r43 : c.nreg 9443 = 1) (r44 : c.nreg 9444 = 2)
    (r46 : c.nreg 9446 = f) (h1 : cnt + 2 ≤ W) (h2 : MKb + f ≤ W) (h3 : BTb + cnt ≤ W) :
    ∃ c' k, Exec P W cwRec c c' k ∧ k = 6 ∧ c'.nreg 9442 = cnt + 1 ∧
      c'.nmem = upd (upd c.nmem (MKb + f) (cnt + 2)) (BTb + cnt) t ∧
      (∀ r, r ≠ 9442 → r ≠ 9448 → r ≠ 9449 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cwRec
  exec_block
  all_goals try ((try config_simp); (try simp only [r07, r10, r41, r42, r43, r44, r46]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r07, r10, r41, r42, r43, r44, r46])
  simp only [upd_apply]; split_ifs <;> omega

theorem cwR_exec (c : Config) (hc : WordsBounded W c) {MKb BTb t cnt f v : ℕ}
    (r07 : c.nreg 9407 = MKb) (r10 : c.nreg 9410 = BTb) (r41 : c.nreg 9441 = t)
    (r42 : c.nreg 9442 = cnt) (r43 : c.nreg 9443 = 1) (r44 : c.nreg 9444 = 2)
    (r45 : c.nreg 9445 = 0) (r46 : c.nreg 9446 = f) (r47 : c.nreg 9447 = v)
    (h1 : cnt + 2 ≤ W) (h2 : MKb + f ≤ W) (h3 : BTb + cnt ≤ W) :
    ∃ c' k, Exec P W cwR c c' k ∧ k ≤ 10 ∧
      c'.nreg 9442 = (if v = 1 then cnt + 1 else cnt) ∧
      c'.nmem = (if v = 1 then upd (upd c.nmem (MKb + f) (cnt + 2)) (BTb + cnt) t else c.nmem) ∧
      (∀ r, r ≠ 9442 → r ≠ 9448 → r ≠ 9449 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cwR
  by_cases hv : v = 1
  · subst hv
    obtain ⟨c', k, e, hk, g42, gm, gk, gr, grm, go⟩ :=
      cwRec_exec (P := P) c hc r07 r10 r41 r42 r43 r44 r46 h1 h2 h3
    refine ⟨c', _, .ifLtN_true (by rw [r47, r44]; omega)
      (.ifLtN_true (by rw [r45, r47]; omega) e), by omega, by simp [g42], by simp [gm], gk, gr,
      grm, go⟩
  · by_cases h2' : v < 2
    · refine ⟨c, _, .ifLtN_true (by rw [r47, r44]; exact h2')
        (.ifLtN_false (by rw [r45, r47]; omega) (.skip hc)), by omega, by simp [hv, r42],
        by simp [hv], fun _ _ _ _ => rfl, rfl, rfl, rfl⟩
    · refine ⟨c, _, .ifLtN_false (by rw [r47, r44]; exact h2') (.skip hc), by omega,
        by simp [hv, r42], by simp [hv], fun _ _ _ _ => rfl, rfl, rfl, rfl⟩

theorem cwD_exec (c : Config) (hc : WordsBounded W c) {n : ℕ} (r40 : c.nreg 9440 = n)
    (r43 : c.nreg 9443 = 1) (h1 : n + 1 ≤ W) :
    ∃ c' k, Exec P W cwD c c' k ∧ k = 2 ∧ c'.nreg 9440 = n + 1 ∧
      c'.nreg 9441 = c.nreg 9439 ∧ (∀ r, r ≠ 9440 → r ≠ 9441 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cwD
  exec_block
  all_goals try ((try config_simp); (try simp only [r40, r43]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r40, r43])
  simp only [upd_apply]; split_ifs <;> omega

/-- **One step of the walk.** -/
theorem cwBody_exec (c : Config) (hc : WordsBounded W c)
    {NXb SGb ONb FLb MKb BTb n t cnt : ℕ}
    (r04 : c.nreg 9404 = NXb) (r05 : c.nreg 9405 = FLb) (r06 : c.nreg 9406 = ONb)
    (r07 : c.nreg 9407 = MKb) (r10 : c.nreg 9410 = BTb) (r31 : c.nreg 9431 = SGb)
    (r40 : c.nreg 9440 = n) (r41 : c.nreg 9441 = t) (r42 : c.nreg 9442 = cnt)
    (r43 : c.nreg 9443 = 1) (r44 : c.nreg 9444 = 2) (r45 : c.nreg 9445 = 0)
    (h1 : FLb + t ≤ W) (h2 : MKb + c.nmem (FLb + t) ≤ W) (h3 : ONb + t ≤ W) (h4 : NXb + t ≤ W)
    (h5 : SGb + t ≤ W) (h6 : cnt + 2 ≤ W) (h7 : BTb + cnt ≤ W) (h8 : n + 1 ≤ W) :
    ∃ c' k, Exec P W cwBody c c' k ∧ k ≤ 24 ∧ c'.nreg 9440 = n + 1 ∧
      c'.nreg 9441 = twF NXb SGb ONb c.nmem t ∧
      c'.nreg 9442 = (if c.nmem (MKb + c.nmem (FLb + t)) = 1 then cnt + 1 else cnt) ∧
      c'.nmem = (if c.nmem (MKb + c.nmem (FLb + t)) = 1 then
        upd (upd c.nmem (MKb + c.nmem (FLb + t)) (cnt + 2)) (BTb + cnt) t else c.nmem) ∧
      (∀ r, r ≠ 9439 → r ≠ 9440 → r ≠ 9441 → r ≠ 9442 → (r < 9446 ∨ 9449 < r) →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a46, a47, a48, ak, am, ar, arm, ao⟩ :=
    cwA_exec (P := P) c hc r05 r06 r07 r41 h1 h2 h3
  have q1 : ∀ r, (r < 9446 ∨ 9448 < r) → c₁.nreg r = c.nreg r := ak
  obtain ⟨c₂, k₂, e₂, hk₂, b39, bk, bm, br, brm, bo⟩ :=
    fcwN_exec (P := P) c₁ e₁.wb_right (NXb := NXb) (SGb := SGb) (ONb := ONb) (t := t)
      (by rw [q1 _ (by omega), r04]) (by rw [q1 _ (by omega), r31]) (by rw [q1 _ (by omega), r41])
      (by rw [q1 _ (by omega), r45]) (by rw [a48, am]) h4 h5
  have q2 : ∀ r, r ≠ 9439 → r ≠ 9449 → c₂.nreg r = c₁.nreg r := bk
  rw [am] at b39
  obtain ⟨c₃, k₃, e₃, hk₃, d42, dm, dk, dr, drm, do'⟩ :=
    cwR_exec (P := P) c₂ e₂.wb_right (MKb := MKb) (BTb := BTb) (t := t) (cnt := cnt)
      (f := c.nmem (FLb + t)) (v := c.nmem (MKb + c.nmem (FLb + t)))
      (by rw [q2 _ (by omega) (by omega), q1 _ (by omega), r07])
      (by rw [q2 _ (by omega) (by omega), q1 _ (by omega), r10])
      (by rw [q2 _ (by omega) (by omega), q1 _ (by omega), r41])
      (by rw [q2 _ (by omega) (by omega), q1 _ (by omega), r42])
      (by rw [q2 _ (by omega) (by omega), q1 _ (by omega), r43])
      (by rw [q2 _ (by omega) (by omega), q1 _ (by omega), r44])
      (by rw [q2 _ (by omega) (by omega), q1 _ (by omega), r45])
      (by rw [q2 _ (by omega) (by omega), a46]) (by rw [q2 _ (by omega) (by omega), a47]) h6
      h2 h7
  have q3 : ∀ r, r ≠ 9442 → r ≠ 9448 → r ≠ 9449 → c₃.nreg r = c₂.nreg r := dk
  obtain ⟨c₄, k₄, e₄, hk₄, f40, f41, fk, fm, fr, frm, fo⟩ :=
    cwD_exec (P := P) c₃ e₃.wb_right (n := n)
      (by rw [q3 _ (by omega) (by omega) (by omega), q2 _ (by omega) (by omega),
        q1 _ (by omega), r40])
      (by rw [q3 _ (by omega) (by omega) (by omega), q2 _ (by omega) (by omega),
        q1 _ (by omega), r43]) h8
  refine ⟨c₄, _, e₁.seq (e₂.seq (e₃.seq e₄)), by omega, f40, ?_, ?_, ?_, fun r h1 h2 h3 h4 hr => ?_,
    by rw [fr, dr, br, ar], by rw [frm, drm, brm, arm], by rw [fo, do', bo, ao]⟩
  · rw [f41, q3 _ (by omega) (by omega) (by omega), b39]
  · rw [fk _ (by omega) (by omega), d42]
  · rw [fm, dm, bm, am]
  · rw [fk _ (by omega) (by omega), q3 _ (by omega) (by omega) (by omega),
      q2 _ (by omega) (by omega), q1 _ (by omega)]

/-- **The corner walk on the machine.** The labels `FL[i] ≤ m`, the next indices `NX[i]`,
`SG[i] < m` (`i < m`), the marks in `[MK, MK + m]`, the corners in `[BT, BT + m)`, the arrays
`NX`, `SG`, `ON`, `FL` and the start disjoint from the two written regions, `N ≤ m`. -/
theorem cwProg_exec (c : Config) (hc : WordsBounded W c)
    {N m NXb SGb ONb FLb MKb BTb t₀b : ℕ}
    (r00 : c.nreg 9400 = N) (r02 : c.nreg 9402 = t₀b) (r04 : c.nreg 9404 = NXb)
    (r05 : c.nreg 9405 = FLb) (r06 : c.nreg 9406 = ONb) (r07 : c.nreg 9407 = MKb)
    (r10 : c.nreg 9410 = BTb) (r31 : c.nreg 9431 = SGb) (hNm : N ≤ m)
    (ht₀ : c.nmem t₀b < m) (hMK : ∀ a ≤ m, c.nmem (MKb + a) ≤ 1)
    (hFL : ∀ i < m, c.nmem (FLb + i) ≤ m) (hNX : ∀ i < m, c.nmem (NXb + i) < m)
    (hSG : ∀ i < m, c.nmem (SGb + i) < m)
    (dMK : ∀ a, MKb ≤ a → a ≤ MKb + m → (a < FLb ∨ FLb + m ≤ a) ∧ (a < ONb ∨ ONb + m ≤ a) ∧
      (a < NXb ∨ NXb + m ≤ a) ∧ (a < SGb ∨ SGb + m ≤ a) ∧ a ≠ t₀b)
    (dBT : ∀ a, BTb ≤ a → a < BTb + m → (a < FLb ∨ FLb + m ≤ a) ∧ (a < ONb ∨ ONb + m ≤ a) ∧
      (a < NXb ∨ NXb + m ≤ a) ∧ (a < SGb ∨ SGb + m ≤ a) ∧ (a < MKb ∨ MKb + m < a))
    (hW : FLb + m + MKb + ONb + NXb + SGb + BTb + m + 3 ≤ W) :
    let tt : ℕ → ℕ := fun n => (twF NXb SGb ONb c.nmem)^[n] (c.nmem t₀b)
    let g : ℕ → ℕ := fun n => c.nmem (FLb + tt n)
    let mk0 : ℕ → ℕ := fun a => if a ≤ m then c.nmem (MKb + a) else 0
    ∃ c' k, Exec P W cwProg c c' k ∧ k ≤ 26 * N + 10 ∧
      c'.nreg 9441 = tt N ∧ c'.nreg 9442 = (cwRun g tt mk0 N).cnt ∧
      (∀ a ≤ m, c'.nmem (MKb + a) = (cwRun g tt mk0 N).mks a) ∧
      (∀ x < (cwRun g tt mk0 N).cnt, c'.nmem (BTb + x) = (cwRun g tt mk0 N).bt x) ∧
      (∀ a, ¬ (MKb ≤ a ∧ a ≤ MKb + m) → ¬ (BTb ≤ a ∧ a < BTb + m) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 9439 ∨ 9449 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  intro tt g mk0
  obtain ⟨c₁, k₁, e₁, hk₁, a40, a41, a42, a43, a44, a45, ak, am, ar, arm, ao⟩ : ∃ c₁ k₁,
      Exec P W cwInit c c₁ k₁ ∧ k₁ = 6 ∧ c₁.nreg 9440 = 0 ∧ c₁.nreg 9441 = c.nmem t₀b ∧
      c₁.nreg 9442 = 0 ∧ c₁.nreg 9443 = 1 ∧ c₁.nreg 9444 = 2 ∧ c₁.nreg 9445 = 0 ∧
      (∀ r, (r < 9440 ∨ 9445 < r) → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold cwInit
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r02])
    simp only [upd_apply]; split_ifs <;> omega
  have q1 : ∀ r, (r < 9440 ∨ 9445 < r) → c₁.nreg r = c.nreg r := ak
  -- the iterates stay below `m`
  have htt : ∀ n, tt n < m := by
    intro n
    induction n with
    | zero => exact ht₀
    | succ n ih =>
      show (twF NXb SGb ONb c.nmem)^[n + 1] (c.nmem t₀b) < m
      rw [Function.iterate_succ_apply']
      unfold twF
      split_ifs
      · exact hNX _ ih
      · exact hSG _ ih
  have hg : ∀ n, g n ≤ m := fun n => hFL _ (htt n)
  let J : ℕ → Config → Prop := fun n c' =>
    c'.nreg 9441 = tt n ∧ c'.nreg 9442 = (cwRun g tt mk0 n).cnt ∧
    (∀ a ≤ m, c'.nmem (MKb + a) = (cwRun g tt mk0 n).mks a) ∧
    (∀ x < (cwRun g tt mk0 n).cnt, c'.nmem (BTb + x) = (cwRun g tt mk0 n).bt x) ∧
    (∀ a, ¬ (MKb ≤ a ∧ a ≤ MKb + m) → ¬ (BTb ≤ a ∧ a < BTb + m) → c'.nmem a = c.nmem a) ∧
    (∀ r, (r < 9440 ∨ 9441 < r) → (r < 9446 ∨ 9449 < r) → r ≠ 9439 → r ≠ 9442 →
      c'.nreg r = c₁.nreg r) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  have hJ0 : J 0 c₁ := by
    refine ⟨a41, a42, fun a ha => ?_, fun x hx => absurd hx (by simp [cwRun]), fun a _ _ => by
      rw [am], fun _ _ _ _ _ => rfl, ar, arm, ao⟩
    simp only [cwRun, mk0, ha, ↓reduceIte, am]
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h40, j1, j2, j3, j4, j5, j6, j7, j8, j9⟩ := tgRange (P := P)
    (a := 9440) (b := 9400) (body := cwBody) J (lo := 0) (hi := N) (B := 24) c₁ e₁.wb_right a40
    (by rw [q1 _ (by omega), r00]) (Nat.zero_le _) hJ0
    (fun n c' _ hn hw h40 h00 ⟨j1, j2, j3, j4, j5, j6, j7, j8, j9⟩ => by
      have f : ∀ r, (r < 9439 ∨ 9449 < r) → r ≠ 9440 → r ≠ 9441 → c'.nreg r = c.nreg r :=
        fun r h1 h2 h3 => by rw [j6 r (by omega) (by omega) (by omega) (by omega),
          q1 r (by omega)]
      have g43 : c'.nreg 9443 = 1 := by
        rw [j6 _ (by omega) (by omega) (by omega) (by omega), a43]
      have g44 : c'.nreg 9444 = 2 := by
        rw [j6 _ (by omega) (by omega) (by omega) (by omega), a44]
      have g45 : c'.nreg 9445 = 0 := by
        rw [j6 _ (by omega) (by omega) (by omega) (by omega), a45]
      have ht := htt n
      set s := cwRun g tt mk0 n with hs
      have hI := cwRun_inv g tt mk0 (fun a => by
        simp only [mk0]; split_ifs with ha
        · exact hMK a ha
        · omega) n
      rw [← hs] at hI
      have hcnt : s.cnt ≤ n := hI.cnt_le
      -- the reads
      have eFL : c'.nmem (FLb + tt n) = g n :=
        j5 _ (fun h => by have := dMK _ h.1 h.2; omega) (fun h => by have := dBT _ h.1 h.2; omega)
      have eON : c'.nmem (ONb + tt n) = c.nmem (ONb + tt n) :=
        j5 _ (fun h => by have := dMK _ h.1 h.2; omega) (fun h => by have := dBT _ h.1 h.2; omega)
      have eNX : c'.nmem (NXb + tt n) = c.nmem (NXb + tt n) :=
        j5 _ (fun h => by have := dMK _ h.1 h.2; omega) (fun h => by have := dBT _ h.1 h.2; omega)
      have eSG : c'.nmem (SGb + tt n) = c.nmem (SGb + tt n) :=
        j5 _ (fun h => by have := dMK _ h.1 h.2; omega) (fun h => by have := dBT _ h.1 h.2; omega)
      have eMK : c'.nmem (MKb + g n) = s.mks (g n) := j3 _ (hg n)
      obtain ⟨c'', t, ex, hk, b40, b41, b42, bm, bk, br, brm, bo⟩ :=
        cwBody_exec (P := P) c' hw (NXb := NXb) (SGb := SGb) (ONb := ONb) (FLb := FLb)
          (MKb := MKb) (BTb := BTb) (n := n) (t := tt n) (cnt := s.cnt)
          (by rw [f _ (by omega) (by omega) (by omega), r04])
          (by rw [f _ (by omega) (by omega) (by omega), r05])
          (by rw [f _ (by omega) (by omega) (by omega), r06])
          (by rw [f _ (by omega) (by omega) (by omega), r07])
          (by rw [f _ (by omega) (by omega) (by omega), r10])
          (by rw [f _ (by omega) (by omega) (by omega), r31]) h40 j1 j2 g43 g44 g45
          (by omega) (by rw [eFL]; have := hg n; omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)
      rw [eFL, eMK] at b42 bm
      have hstep : cwRun g tt mk0 (n + 1) = cwStep (g n) (tt n) n s := rfl
      refine ⟨c'', t, ex, hk, b40, by rw [bk _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h00, ?_⟩
      refine ⟨?_, ?_, fun a ha => ?_, fun x hx => ?_, fun a h1 h2 => ?_,
        fun r h1 h2 h3 h4 => ?_, by rw [br, j7], by rw [brm, j8], by rw [bo, j9]⟩
      · rw [b41]
        show twF NXb SGb ONb c'.nmem (tt n) = (twF NXb SGb ONb c.nmem)^[n + 1] (c.nmem t₀b)
        rw [Function.iterate_succ_apply']
        show twF NXb SGb ONb c'.nmem (tt n) = twF NXb SGb ONb c.nmem (tt n)
        unfold twF; rw [eON, eNX, eSG]
      · rw [b42, hstep]; unfold cwStep
        split_ifs <;> rfl
      · rw [bm, hstep]; unfold cwStep
        by_cases hv : s.mks (g n) = 1
        · simp only [hv, ↓reduceIte]
          rw [upd_other _ _ _ (fun h => by
            have := dBT (BTb + s.cnt) (by omega) (by omega); omega)]
          by_cases hag : a = g n
          · subst hag; rw [upd_same]; simp
          · rw [upd_other _ _ _ (by omega), j3 a ha]; simp [hag]
        · simp only [hv, ↓reduceIte]; exact j3 a ha
      · rw [bm, hstep]; unfold cwStep
        rw [hstep] at hx; unfold cwStep at hx
        by_cases hv : s.mks (g n) = 1
        · simp only [hv, ↓reduceIte] at hx ⊢
          by_cases hxc : x = s.cnt
          · subst hxc; rw [upd_same]; simp
          · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (fun h => by
              have := dBT (BTb + x) (by omega) (by omega); have := hg n; omega), j4 x (by omega)]
            simp [hxc]
        · simp only [hv, ↓reduceIte] at hx ⊢; exact j4 x hx
      · rw [bm]
        split_ifs
        · rw [upd_other _ _ _ (fun h => h2 ⟨by omega, by omega⟩),
            upd_other _ _ _ (fun h => h1 ⟨by omega, by have := hg n; omega⟩)]
          exact j5 a h1 h2
        · exact j5 a h1 h2
      · rw [bk r (by omega) (by omega) (by omega) h4 (by omega)]; exact j6 r h1 h2 h3 h4)
  refine ⟨c₂, _, e₁.seq e₂, by rw [hk₁]; simp only [Nat.sub_zero] at hk₂; omega, j1, j2, j3, j4, j5, fun r hr => ?_, j7, j8,
    j9⟩
  rcases Nat.lt_or_ge r 9440 with h | h
  · rw [j6 r (Or.inl h) (by omega) (by omega) (by omega), q1 r (Or.inl h)]
  · rw [j6 r (by omega) (by omega) (by omega) (by omega), q1 r (by omega)]

end BKMNW

end PlanarFlow
