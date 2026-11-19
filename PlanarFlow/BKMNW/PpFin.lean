module

public import PlanarFlow.BKMNW.PpSo

/-!
# The final arrays of the preprocessing and the registers of the max-flow program

`fin`: with `F₀ = B + 84 n + KM + 1` (`r8732`) and `N` valid slots, the six arrays of the
max-flow program by gathers through the sorted slots (`SRT`, `B + 35 n`) and their positions
(`POS`, `B + 42 n`):

* `REV[i] = POS[RVS[SRT[i]]]` at `F₀`, `SIG[i] = POS[ROS[SRT[i]]]` at `F₀ + 7 n`,
  `CAP[i] = CPS[SRT[i]]` at `F₀ + 14 n`, `KR[i] = KRS[SRT[i]]` at `F₀ + 21 n`,
  `VT[i] = KY[SRT[i]]` at `F₀ + 28 n`, `RT[i] = POS[RTS[SRT[i]]]` at `F₀ + 35 n`;
* the registers `6700 … 6707` (`N`, the bases, the tag `1`, `Z = BIG`, `Hb = F₀ + 42 n + 2`) and
  `mem[Hb - 1] = F₀ + 28 n`, `mem[Hb - 2] = F₀ + 35 n`.

**`gat_exec`** (one gather), **`finR_exec`** (the registers).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs MfDrv Feas

variable {P : Input} {W : ℕ}

/-- `r := r_a + k n`. -/
def setR (r a k : ℕ) : Stmt := block [.constN 8778 k, .mulN 8778 8700 8778, .addN r 8778 a]

theorem setR_exec (c : Config) (hc : WordsBounded W c) {r a k n A : ℕ} (hr : r ≠ 8778)
    (ha : a ≠ 8778) (r00 : c.nreg 8700 = n) (ra : c.nreg a = A) (w : A + k * n + k ≤ W) :
    ∃ c' t, Exec P W (setR r a k) c c' t ∧ t = 3 ∧ c'.nreg r = A + k * n ∧
      (∀ x, x ≠ r → x ≠ 8778 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hkn : n * k = k * n := Nat.mul_comm _ _
  unfold setR
  exec_block
  · omega
  · config_simp; rw [r00, hkn]; omega
  · config_simp; simp (disch := omega) only [upd_other]; rw [r00, ra, hkn]; omega
  refine ⟨rfl, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp (disch := omega) only [upd_other]; rw [r00, ra, hkn]; omega
  · config_simp; simp (disch := omega) only [upd_other]

/-- **One gather**: `8727 := B + a n`, `8742 := F₀ + 7 j n`, then the map loop. -/
def gat (a j : ℕ) (vb : Stmt) : Stmt :=
  .seq (setR 8727 8730 a) (.seq (setR 8742 8732 (7 * j)) (mapL vb))

theorem gat_exec (c : Config) (hc : WordsBounded W c) {vb : Stmt} {n B F₀ a j m B' : ℕ}
    (g : ℕ → ℕ) (r00 : c.nreg 8700 = n) (r30 : c.nreg 8730 = B) (r32 : c.nreg 8732 = F₀)
    (r41 : c.nreg 8741 = m) (r04 : c.nreg 8704 = 1) (hm : m ≤ 7 * n)
    (w1 : F₀ + 7 * j * n + 7 * n + 7 * j ≤ W) (w2 : B + a * n + a ≤ W) (w3 : m + 1 ≤ W)
    (hvb : ∀ i < m, ∀ c' : Config, WordsBounded W c' → c'.nreg 8740 = i →
      c'.nreg 8727 = B + a * n →
      (∀ x, ¬ wscr x → x ≠ 8727 → x ≠ 8778 → c'.nreg x = c.nreg x) →
      (∀ a', ¬ (F₀ + 7 * j * n ≤ a' ∧ a' < F₀ + 7 * j * n + m) → c'.nmem a' = c.nmem a') →
      ∃ c'' t, Exec P W vb c' c'' t ∧ VBPost c' (g i) B' c'' t) :
    ∃ c' t, Exec P W (gat a j vb) c c' t ∧ t ≤ (B' + 5) * m + 9 ∧
      (∀ i < m, c'.nmem (F₀ + 7 * j * n + i) = g i) ∧
      (∀ a', ¬ (F₀ + 7 * j * n ≤ a' ∧ a' < F₀ + 7 * j * n + m) → c'.nmem a' = c.nmem a') ∧
      (∀ x, ¬ wscr x → x ≠ 8727 → x ≠ 8778 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, v1, f1, m1, rr1, rm1, o1⟩ := setR_exec (P := P) (r := 8727)
    (a := 8730) (k := a) (n := n) (A := B) c hc (by omega) (by omega) r00 r30 w2
  obtain ⟨c₂, t₂, e₂, ht₂, v2, f2, m2, rr2, rm2, o2⟩ := setR_exec (P := P) (r := 8742)
    (a := 8732) (k := 7 * j) (n := n) (A := F₀) c₁ e₁.wb_right (by omega) (by omega)
    (by rw [f1 _ (by omega) (by omega)]; exact r00) (by rw [f1 _ (by omega) (by omega)]; exact r32)
    (by rw [Nat.mul_assoc] at w1 ⊢; omega)
  rw [Nat.mul_assoc] at v2
  obtain ⟨c₃, t₃, e₃, ht₃, a3, m3, f3, rr3, rm3, o3⟩ := mapL_exec (P := P) c₂ e₂.wb_right
    (vb := vb) (m := m) (Ob := F₀ + 7 * j * n) (B := B') g
    (by rw [f2 _ (by omega) (by omega), f1 _ (by omega) (by omega)]; exact r41)
    (by rw [f2 _ (by omega) (by omega), f1 _ (by omega) (by omega)]; exact r04)
    (by rw [v2, Nat.mul_assoc]) (by rw [Nat.mul_assoc] at w1 ⊢; omega) w3
    (fun i hi c' hw h40 hr hmm => hvb i hi c' hw h40
      (by rw [hr _ (by unfold pscr; omega) (by omega) (by omega), f2 _ (by omega) (by omega)]
          exact v1)
      (fun x hx h1 h2 => by
        unfold wscr at hx
        rw [hr x (fun h => hx (Or.inl h)) (by omega) (by omega), f2 x (by omega) h2,
          f1 x h1 h2])
      (fun a' ha => by rw [hmm a' ha, m2, m1]))
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, a3,
    fun a' ha => by rw [m3 a' ha, m2, m1], fun x hx h1 h2 => ?_, by rw [rr3, rr2, rr1],
    by rw [rm3, rm2, rm1], by rw [o3, o2, o1]⟩
  unfold wscr at hx
  rw [f3 x (fun h => hx (Or.inl h)) (by omega) (by omega), f2 x (by omega) h2, f1 x h1 h2]

/-- The registers and the heap of the max-flow program. -/
def finR : Stmt :=
  block [.copyN 6700 8731, .copyN 6701 8732, .constN 8778 7, .mulN 8778 8700 8778,
    .addN 6702 8732 8778, .addN 6703 6702 8778, .addN 6704 6703 8778, .constN 6705 1,
    .copyN 6706 8708, .addN 8779 6704 8778, .addN 8777 8779 8778, .addN 8776 8777 8778,
    .addN 6707 8776 8705, .subN 8775 6707 8704, .storeN 8775 8779, .subN 8775 8775 8704,
    .storeN 8775 8777]

theorem finR_exec (c : Config) (hc : WordsBounded W c) {n N F₀ Z : ℕ}
    (r00 : c.nreg 8700 = n) (r04 : c.nreg 8704 = 1) (r05 : c.nreg 8705 = 2)
    (r31 : c.nreg 8731 = N) (r32 : c.nreg 8732 = F₀) (r08 : c.nreg 8708 = Z)
    (hW : F₀ + 42 * n + 10 ≤ W) :
    ∃ c' t, Exec P W finR c c' t ∧ t = 17 ∧ c'.nreg 6700 = N ∧ c'.nreg 6701 = F₀ ∧
      c'.nreg 6702 = F₀ + 7 * n ∧ c'.nreg 6703 = F₀ + 14 * n ∧ c'.nreg 6704 = F₀ + 21 * n ∧
      c'.nreg 6705 = 1 ∧ c'.nreg 6706 = Z ∧ c'.nreg 6707 = F₀ + 42 * n + 2 ∧
      c'.nmem (F₀ + 42 * n + 2 - 1) = F₀ + 28 * n ∧
      c'.nmem (F₀ + 42 * n + 2 - 1 - 1) = F₀ + 35 * n ∧
      (∀ a, a < F₀ + 42 * n → c'.nmem a = c.nmem a) ∧
      (∀ x, x < 6700 ∨ (6707 < x ∧ x < 8775) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold finR
  exec_block
  all_goals try omega
  all_goals try (config_simp; (try simp only [r00, r32, r05, r04]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, fun x hx => ?_,
    rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals simp (disch := omega) only [upd_other, upd_same, r00, r04, r05, r31, r32, r08]
  all_goals try ring_nf
  all_goals try simp (disch := omega) only [upd_same, upd_other]

/-- The bases of the gathers. -/
def fin0 : Stmt :=
  block [.constN 8778 84, .mulN 8778 8700 8778, .addN 8732 8778 8730, .addN 8732 8732 8709,
    .addN 8732 8732 8704, .copyN 8741 8731, .constN 8778 35, .mulN 8778 8700 8778,
    .addN 8725 8778 8730, .constN 8778 42, .mulN 8778 8700 8778, .addN 8726 8778 8730]

/-- **The final arrays and the registers of the max-flow program.** -/
def fin : Stmt := .seq fin0 (.seq (gat 49 0 vbG1) (.seq (gat 56 1 vbG1) (.seq (gat 70 2 vbG2)
  (.seq (gat 77 3 vbG2) (.seq (gat 14 4 vbG2) (.seq (gat 63 5 vbG1) finR))))))

theorem fin0_exec (c : Config) (hc : WordsBounded W c) {n B KM N : ℕ}
    (r00 : c.nreg 8700 = n) (r04 : c.nreg 8704 = 1) (r09 : c.nreg 8709 = KM)
    (r30 : c.nreg 8730 = B) (r31 : c.nreg 8731 = N) (hW : B + 84 * n + KM + 100 ≤ W) :
    ∃ c' t, Exec P W fin0 c c' t ∧ t = 12 ∧ c'.nreg 8732 = B + 84 * n + KM + 1 ∧
      c'.nreg 8741 = N ∧ c'.nreg 8725 = B + 35 * n ∧ c'.nreg 8726 = B + 42 * n ∧
      (∀ x, x ≠ 8732 → x ≠ 8741 → x ≠ 8725 → x ≠ 8726 → x ≠ 8778 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fin0
  exec_block
  all_goals try omega
  all_goals try (config_simp; (try simp only [r00, r30, r09, r04]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x h1 h2 h3 h4 h5 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals simp (disch := omega) only [upd_other, upd_same, r00, r04, r09, r30, r31]
  all_goals try ring

end Pp

end BKMNW

end PlanarFlow
