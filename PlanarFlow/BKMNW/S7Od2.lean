module

public import PlanarFlow.BKMNW.S7Od

/-!
# Stage 7 of `sepL` (III), machine part (II): the positions of the classes

From the class numbers `ID` (`n` darts, `ID[i] < nI`) and a scratch base `Ob`:

`odA = odSA ; IO ; (LT[ID[j]] := j) ; LS ; IM ; lkProg ; P1`

* `IO` at `Ob` (`IO[i] = i`), `LT` at `Ob + n` (`nI` cells), `LS` at `Ob + n + nI`
  (`LS[i] = LT[ID[i]]`, the last dart of the class), `IM` at `LS + n` (`LS[i] = i`), `CI`/`IX` at
  `IM + n`, `IM + 2 n` (the compaction of `IM`), `P1` at `IM + 3 n` (`P1[i] = CI[LS[i]] + 1`);
* **`odA_exec`** (`50 n + 30` steps): `LS` meets the hypotheses `lst_lt`, `lst_id`, `lst_max` of
  `OdIn`, `P1[i] = odPos LS i + 1`, `r6306 = odM LS n` (the number of classes).

Registers `7100 = n`, `7150 = IDb`, `7151 = nI`, `7152 = Ob`, `6521 = 1`; written `7155`,
`7170 … 7174`, `7180`, `7160 … 7167`, `6300 … 6309`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- The bases of the positions. -/
def odSA : Stmt :=
  block [.copyN 7155 7152, .addN 7170 7152 7100, .addN 7171 7170 7151, .addN 7172 7171 7100,
    .addN 7173 7172 7100, .addN 7174 7173 7100, .addN 7180 7174 7100]

/-- The registers of the scatter of the last darts. -/
def odSv1 : Stmt := block [.copyN 7160 7100, .copyN 7161 7150, .copyN 7162 7155, .copyN 7163 7170]

/-- The registers of the compaction. -/
def odLk : Stmt := block [.copyN 6300 7100, .copyN 6301 7172, .copyN 6302 7173, .copyN 6303 7174]

/-- **The positions of the classes.** -/
def odA : Stmt :=
  .seq odSA (.seq (mapRunS vbIO 7100 7155) (.seq (.seq odSv1 svProg)
    (.seq (mapRunS vbLS 7100 7171) (.seq (mapRunS vbIM 7100 7172)
      (.seq (.seq odLk lkProg) (mapRunS vbP1 7100 7180))))))

/-- The registers of the positions. -/
structure OdRegsA (c : Config) (n nI Ob IDb : ℕ) : Prop where
  r00 : c.nreg 7100 = n
  r50 : c.nreg 7150 = IDb
  r51 : c.nreg 7151 = nI
  r52 : c.nreg 7152 = Ob
  r55 : c.nreg 7155 = Ob
  r70 : c.nreg 7170 = Ob + n
  r71 : c.nreg 7171 = Ob + n + nI
  r72 : c.nreg 7172 = Ob + 2 * n + nI
  r73 : c.nreg 7173 = Ob + 3 * n + nI
  r74 : c.nreg 7174 = Ob + 4 * n + nI
  r80 : c.nreg 7180 = Ob + 5 * n + nI
  r21 : c.nreg 6521 = 1

lemma OdRegsA.congr {c c' : Config} {n nI Ob IDb : ℕ} (h : OdRegsA c n nI Ob IDb)
    (e : ∀ x, (x = 7100 ∨ (7150 ≤ x ∧ x ≤ 7155) ∨ (7170 ≤ x ∧ x ≤ 7174) ∨ x = 7180 ∨
      x = 6521) → c'.nreg x = c.nreg x) : OdRegsA c' n nI Ob IDb :=
  ⟨by rw [e _ (by omega)]; exact h.r00, by rw [e _ (by omega)]; exact h.r50,
    by rw [e _ (by omega)]; exact h.r51, by rw [e _ (by omega)]; exact h.r52,
    by rw [e _ (by omega)]; exact h.r55, by rw [e _ (by omega)]; exact h.r70,
    by rw [e _ (by omega)]; exact h.r71, by rw [e _ (by omega)]; exact h.r72,
    by rw [e _ (by omega)]; exact h.r73, by rw [e _ (by omega)]; exact h.r74,
    by rw [e _ (by omega)]; exact h.r80, by rw [e _ (by omega)]; exact h.r21⟩

section Exec

variable {P : Input} {W : ℕ}

theorem odSA_exec (c : Config) (hc : WordsBounded W c) {n nI Ob IDb : ℕ}
    (r00 : c.nreg 7100 = n) (r50 : c.nreg 7150 = IDb) (r51 : c.nreg 7151 = nI)
    (r52 : c.nreg 7152 = Ob) (r21 : c.nreg 6521 = 1) (w : Ob + 6 * n + nI ≤ W) :
    ∃ c' t, Exec P W odSA c c' t ∧ t = 7 ∧ OdRegsA c' n nI Ob IDb ∧ c'.nmem = c.nmem ∧
      (∀ x, x ≠ 7155 → (x < 7170 ∨ 7174 < x) → x ≠ 7180 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold odSA
  exec_block
  all_goals try (config_simp; (try simp only [r00, r50, r51, r52, r21]); omega)
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, fun x h1 h2 h3 => ?_,
    rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r00, r50, r51, r52, r21]); done)
  all_goals try (config_simp; (try simp only [r00, r50, r51, r52, r21]); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other])

theorem cp4_exec (c : Config) (hc : WordsBounded W c) {a0 a1 a2 a3 b0 b1 b2 b3 v0 v1 v2 v3 : ℕ}
    (d01 : a0 ≠ a1) (d02 : a0 ≠ a2) (d03 : a0 ≠ a3) (d12 : a1 ≠ a2) (d13 : a1 ≠ a3)
    (d23 : a2 ≠ a3) (e1 : b1 ≠ a0) (e2 : b2 ≠ a0 ∧ b2 ≠ a1) (e3 : b3 ≠ a0 ∧ b3 ≠ a1 ∧ b3 ≠ a2)
    (q0 : c.nreg b0 = v0) (q1 : c.nreg b1 = v1) (q2 : c.nreg b2 = v2) (q3 : c.nreg b3 = v3) :
    ∃ c' t, Exec P W (block [.copyN a0 b0, .copyN a1 b1, .copyN a2 b2, .copyN a3 b3]) c c' t ∧
      t = 4 ∧ c'.nreg a0 = v0 ∧ c'.nreg a1 = v1 ∧ c'.nreg a2 = v2 ∧ c'.nreg a3 = v3 ∧
      c'.nmem = c.nmem ∧ (∀ x, x ≠ a0 → x ≠ a1 → x ≠ a2 → x ≠ a3 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, fun x h0 h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals simp only [upd_apply]
  all_goals split_ifs <;> simp_all

lemma svF_congr {key key' val val' : ℕ → ℕ} {m : ℕ} (hk : ∀ j < m, key j = key' j)
    (hv : ∀ j < m, val j = val' j) (x old : ℕ) :
    svF key val m x old = svF key' val' m x old := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [svF, hk m (by omega), hv m (by omega)]
    rw [ih (fun j hj => hk j (by omega)) (fun j hj => hv j (by omega))]

/-- The scatter of the indices gives the last index of every key. -/
lemma svF_last {key val : ℕ → ℕ} {m i : ℕ} (hval : ∀ j < m, val j = j) (hi : i < m)
    (old : ℕ) :
    svF key val m (key i) old < m ∧ key (svF key val m (key i) old) = key i ∧
      ∀ j < m, key j = key i → j ≤ svF key val m (key i) old := by
  rcases svF_spec key val m (key i) old with ⟨hn, -⟩ | ⟨j, hj, h1, h2, h3⟩
  · exact absurd ⟨i, hi, rfl⟩ hn
  · rw [h2, hval j hj]; exact ⟨hj, h1, h3⟩

/-- The last index of a class is its own last index. -/
lemma lst_lst' {key lst : ℕ → ℕ} {n i : ℕ}
    (h : ∀ i < n, lst i < n ∧ key (lst i) = key i ∧ ∀ j < n, key j = key i → j ≤ lst i)
    (hi : i < n) : lst (lst i) = lst i := by
  obtain ⟨h1, h2, h3⟩ := h i hi
  obtain ⟨g1, g2, g3⟩ := h (lst i) h1
  have a := g3 (lst i) h1 rfl
  have b := h3 (lst (lst i)) g1 (by rw [g2, h2])
  omega

set_option maxHeartbeats 4000000 in
/-- **The positions of the classes** (see the module docstring). -/
theorem odA_exec (c : Config) (hc : WordsBounded W c) {n nI Ob IDb : ℕ}
    (r00 : c.nreg 7100 = n) (r50 : c.nreg 7150 = IDb) (r51 : c.nreg 7151 = nI)
    (r52 : c.nreg 7152 = Ob) (r21 : c.nreg 6521 = 1)
    (hid : ∀ i < n, c.nmem (IDb + i) < nI) (lay : IDb + n ≤ Ob ∧ Ob + 6 * n + nI ≤ W)
    (hn : n + 2 ≤ W) :
    ∃ c' t, Exec P W odA c c' t ∧ t ≤ 70 * n + 40 ∧ OdRegsA c' n nI Ob IDb ∧
      ∃ lst : ℕ → ℕ, (∀ i < n, c'.nmem (Ob + n + nI + i) = lst i) ∧
      (∀ i < n, lst i < n ∧ c.nmem (IDb + lst i) = c.nmem (IDb + i) ∧
        ∀ j < n, c.nmem (IDb + j) = c.nmem (IDb + i) → j ≤ lst i) ∧
      (∀ i < n, c'.nmem (Ob + 5 * n + nI + i) = odPos lst i + 1) ∧
      c'.nreg 6306 = odM lst n ∧
      (∀ a, (a < Ob ∨ Ob + 6 * n + nI ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6300 ∨ (6309 < x ∧ x < 6520) ∨ x = 6521 ∨ (6529 < x ∧ x < 7155) ∨
        (7155 < x ∧ x < 7160) ∨ (7167 < x ∧ x < 7170) ∨ (7174 < x ∧ x < 7180) ∨ 7180 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2⟩ := lay
  set m₀ := c.nmem with hm₀
  unfold odA
  obtain ⟨c₁, t₁, e₁, ht₁, R1, m1, n1, rr1, rm1, o1⟩ := odSA_exec (P := P) c hc r00 r50 r51 r52
    r21 l2
  have gv : ∀ c' : Config, (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c₁.nreg x) →
      OdRegsA c' n nI Ob IDb := fun c' h => R1.congr fun x hx =>
    h x (by unfold vscr; omega) (by omega) (by omega)
  -- `IO`
  obtain ⟨c₂, t₂, e₂, ht₂, f2, fm2, fn2, fr2, frm2, fo2⟩ := mapRun_exec (P := P) c₁ e₁.wb_right
    (vb := vbIO) (bnd := 7100) (ob := 7155) (m := n) (Ob := Ob) (B := 1) (fun i => i) R1.r00
    R1.r21 R1.r55 (by omega) (by omega) (by unfold vscr; omega) (by unfold vscr; omega)
    (by omega) (by omega) (by omega) (by omega)
    (fun i hi c' hw h20 hr hm => by
      obtain ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩ := vbIO_exec (P := P) c' hw h20
      exact ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩)
  have R2 := gv c₂ fn2
  -- `LT[ID[j]] := j`
  obtain ⟨c₃, t₃, e₃, ht₃, s0, s1, s2, s3, sm3, sn3, sr3, srm3, so3⟩ := cp4_exec (P := P) c₂
    e₂.wb_right (a0 := 7160) (a1 := 7161) (a2 := 7162) (a3 := 7163) (b0 := 7100) (b1 := 7150)
    (b2 := 7155) (b3 := 7170) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ R2.r00 R2.r50 R2.r55 R2.r70
  have R3 := R2.congr fun x hx => sn3 x (by omega) (by omega) (by omega) (by omega)
  have ID2 : ∀ i < n, c₃.nmem (IDb + i) = m₀ (IDb + i) := fun i hi => by
    rw [sm3, fm2 _ (by omega), m1]
  obtain ⟨c₄, t₄, e₄, ht₄, g4, gm4, gn4, gr4, grm4, go4⟩ := svProg_exec (P := P) c₃ e₃.wb_right
    (m := n) (nk := nI) (KEYb := IDb) (VALb := Ob) (Tb := Ob + n) s0 s1 s2 s3
    (fun j hj => by rw [ID2 j hj]; exact hid j hj) (Or.inl (by omega)) (Or.inl (by omega))
    (by omega) (by omega) (by omega) (by omega)
  have R4 := R3.congr fun x hx => gn4 x (by omega)
  -- the last darts
  set lsv : ℕ → ℕ := fun i => c₄.nmem (Ob + n + m₀ (IDb + i)) with hlsv
  have IO3 : ∀ j < n, c₃.nmem (Ob + j) = j := fun j hj => by rw [sm3]; exact f2 j hj
  have hls : ∀ i < n, lsv i < n ∧ m₀ (IDb + lsv i) = m₀ (IDb + i) ∧
      ∀ j < n, m₀ (IDb + j) = m₀ (IDb + i) → j ≤ lsv i := by
    intro i hi
    have e : lsv i = svF (fun j => m₀ (IDb + j)) (fun j => j) n (m₀ (IDb + i))
        (c₃.nmem (Ob + n + m₀ (IDb + i))) := by
      simp only [hlsv]
      rw [g4 _ (hid i hi)]
      exact svF_congr (fun j hj => ID2 j hj) (fun j hj => IO3 j hj) _ _
    rw [e]
    exact svF_last (key := fun j => m₀ (IDb + j)) (fun j hj => rfl) hi _
  have hll : ∀ i < n, lsv (lsv i) = lsv i := fun i hi =>
    lst_lst' (key := fun j => m₀ (IDb + j)) hls hi
  have ID4 : ∀ i < n, c₄.nmem (IDb + i) = m₀ (IDb + i) := fun i hi => by
    rw [gm4 _ (by omega)]; exact ID2 i hi
  -- `LS`
  obtain ⟨c₅, t₅, e₅, ht₅, f5, fm5, fn5, fr5, frm5, fo5⟩ := mapRun_exec (P := P) c₄ e₄.wb_right
    (vb := vbLS) (bnd := 7100) (ob := 7171) (m := n) (Ob := Ob + n + nI) (B := 4) lsv R4.r00
    R4.r21 R4.r71 (by omega) (by omega) (by unfold vscr; omega) (by unfold vscr; omega)
    (by omega) (by omega) (by omega) (by omega)
    (fun i hi c' hw h20 hr hm => by
      have g : OdRegsA c' n nI Ob IDb := R4.congr fun x hx =>
        hr x (by unfold vscr; omega) (by omega) (by omega)
      have hx := hid i hi
      obtain ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩ := vbLS_exec (P := P) c' hw
        (IDb := IDb) (LTb := Ob + n) (x := m₀ (IDb + i)) (y := lsv i) h20 g.r50 g.r70
        (by rw [hm _ (by omega)]; exact ID4 i hi) (by rw [hm _ (by omega)]) (by omega)
        (by omega)
      exact ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩)
  have R5 := R4.congr fun x hx => fn5 x (by unfold vscr; omega) (by omega) (by omega)
  -- `IM`
  obtain ⟨c₆, t₆, e₆, ht₆, f6, fm6, fn6, fr6, frm6, fo6⟩ := mapRun_exec (P := P) c₅ e₅.wb_right
    (vb := vbIM) (bnd := 7100) (ob := 7172) (m := n) (Ob := Ob + 2 * n + nI) (B := 7)
    (fun i => pdEq (lsv i) i) R5.r00 R5.r21 R5.r72 (by omega) (by omega)
    (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
    (fun i hi c' hw h20 hr hm => by
      have g : OdRegsA c' n nI Ob IDb := R5.congr fun x hx =>
        hr x (by unfold vscr; omega) (by omega) (by omega)
      obtain ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩ := vbIM_exec (P := P) c' hw
        (LSb := Ob + n + nI) (a := lsv i) h20 g.r71 g.r21
        (by rw [hm _ (by omega)]; exact f5 i hi) (by omega)
      exact ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩)
  have R6 := R5.congr fun x hx => fn6 x (by unfold vscr; omega) (by omega) (by omega)
  have IM6 : ∀ i < n, c₆.nmem (Ob + 2 * n + nI + i) = odR lsv i := fun i hi => by
    rw [f6 i hi, pdEq_eq]; rfl
  -- the compaction
  obtain ⟨c₇, t₇, e₇, ht₇, s0', s1', s2', s3', sm7, sn7, sr7, srm7, so7⟩ := cp4_exec (P := P) c₆
    e₆.wb_right (a0 := 6300) (a1 := 6301) (a2 := 6302) (a3 := 6303) (b0 := 7100) (b1 := 7172)
    (b2 := 7173) (b3 := 7174) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ R6.r00 R6.r72 R6.r73 R6.r74
  have R7 := R6.congr fun x hx => sn7 x (by omega) (by omega) (by omega) (by omega)
  obtain ⟨c₈, t₈, e₈, ht₈, k8, k8', km8, kn8, kr8, krm8, ko8⟩ := lkProg_exec (P := P) c₇
    e₇.wb_right (m := n) (Fb := Ob + 2 * n + nI) (CIb := Ob + 3 * n + nI)
    (IXb := Ob + 4 * n + nI) s0' s1' s2' s3' (by omega) (by omega) (by omega) (by omega)
  have R8 := R7.congr fun x hx => kn8 x (by omega)
  have IM7 : ∀ i < n, c₇.nmem (Ob + 2 * n + nI + i) = odR lsv i := fun i hi => by
    rw [sm7]; exact IM6 i hi
  have hcnt : ∀ i ≤ n, cnt (fun j => c₇.nmem (Ob + 2 * n + nI + j)) i = cnt (odR lsv) i :=
    fun i hi => cnt_congr fun j hj => IM7 j (by omega)
  -- `P1`
  have hpos : ∀ i < n, c₈.nmem (Ob + 3 * n + nI + lsv i) = odPos lsv i := fun i hi => by
    have hl := (hls i hi).1
    have hf : 0 < c₇.nmem (Ob + 2 * n + nI + lsv i) := by
      rw [IM7 _ hl]; unfold odR; rw [hll i hi]; simp
    rw [(k8' _ hl hf).1, hcnt _ hl.le]; rfl
  obtain ⟨c₉, t₉, e₉, ht₉, f9, fm9, fn9, fr9, frm9, fo9⟩ := mapRun_exec (P := P) c₈ e₈.wb_right
    (vb := vbP1) (bnd := 7100) (ob := 7180) (m := n) (Ob := Ob + 5 * n + nI) (B := 5)
    (fun i => odPos lsv i + 1) R8.r00 R8.r21 R8.r80 (by omega) (by omega)
    (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
    (fun i hi c' hw h20 hr hm => by
      have g : OdRegsA c' n nI Ob IDb := R8.congr fun x hx =>
        hr x (by unfold vscr; omega) (by omega) (by omega)
      have hl := (hls i hi).1
      have hle : odPos lsv i ≤ n := by
        unfold odPos; exact (cnt_le _ _).trans hl.le
      obtain ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩ := vbP1_exec (P := P) c' hw
        (LSb := Ob + n + nI) (CIb := Ob + 3 * n + nI) (a := lsv i) (v := odPos lsv i) h20 g.r71
        g.r73 g.r21
        (by rw [hm _ (by omega), km8 _ (by omega), sm7, fm6 _ (by omega)]; exact f5 i hi)
        (by rw [hm _ (by omega)]; exact hpos i hi) (by omega) (by omega) (by omega)
      exact ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩)
  have R9 := R8.congr fun x hx => fn9 x (by unfold vscr; omega) (by omega) (by omega)
  refine ⟨c₉, t₁ + (t₂ + ((t₃ + t₄) + (t₅ + (t₆ + ((t₇ + t₈) + t₉))))),
    .seq e₁ (.seq e₂ (.seq (.seq e₃ e₄) (.seq e₅ (.seq e₆ (.seq (.seq e₇ e₈) e₉))))), ?_, R9,
    lsv, fun i hi => ?_, hls, f9, ?_, fun a ha => ?_, fun x hx => ?_, ?_, ?_, ?_⟩
  · have := cnt_le (fun j => c₇.nmem (Ob + 2 * n + nI + j)) n
    omega
  · rw [fm9 _ (by omega), km8 _ (by omega), sm7, fm6 _ (by omega)]; exact f5 i hi
  · rw [fn9 _ (by unfold vscr; omega) (by omega) (by omega), k8, hcnt n le_rfl]; rfl
  · rw [fm9 a (by omega), km8 a (by omega), sm7, fm6 a (by omega), fm5 a (by omega),
      gm4 a (by omega), sm3, fm2 a (by omega), m1]
  · rw [fn9 x (by unfold vscr at *; omega) (by omega) (by omega), kn8 x (by omega),
      sn7 x (by omega) (by omega) (by omega) (by omega),
      fn6 x (by unfold vscr at *; omega) (by omega) (by omega),
      fn5 x (by unfold vscr at *; omega) (by omega) (by omega), gn4 x (by omega),
      sn3 x (by omega) (by omega) (by omega) (by omega),
      fn2 x (by unfold vscr at *; omega) (by omega) (by omega), n1 x (by omega) (by omega) (by omega)]
  · rw [fr9, kr8, sr7, fr6, fr5, gr4, sr3, fr2, rr1]
  · rw [frm9, krm8, srm7, frm6, frm5, grm4, srm3, frm2, rm1]
  · rw [fo9, ko8, so7, fo6, fo5, go4, so3, fo2, o1]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
