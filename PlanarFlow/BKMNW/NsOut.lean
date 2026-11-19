module

public import PlanarFlow.BKMNW.NsNum

/-!
# Writing the input part of the root frame of a negSSSP call

From the scratch arrays (`CD` the closure list, `POS` its inverse, `RV`, `NX` the first returns,
`LAB` the labels `+ 1`, `MLN` the least lengths in the offset `K`) the program `wrProg` writes the
input part of the frame at `A` (`InP`): for `h < k` the five words `CD[h]`, `POS[RV[x]] - 1`,
`POS[NX[x]] - 1`, `LAB[x] - 1`, `LAB[RV[x]] - 1` (`x = CD[h]`) at `A + 4 + j k + h`, for
`h < m'` the length `MLN[x] + L - K` at `A + 4 + 5 k + h`, and the header `m, m', k, L`.

* `wr1`/`wrL1` (**`wr1_exec`**), `wr2`/`wrL2` (`wr2_exec`), `wrH`; **`wrProg_exec`**: within
  `31 k + 11 m' + 21` steps; memory outside `[A, A + 4 + 5 k + m')` kept.

Registers: `7500 = m`, `7501 = RVb`, `7504 = K`, `7506 = A`, `7510 = NXb`, `7512 = LABb`,
`7515 = MLb`, `7516 = POb`, `7517 = CDb`, `7525 = L`, `7526 = k`, `7527 = m'`; written `7522`,
`7530`, `7550 … 7556`, scratch `7531 … 7538`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace PlanarFlow

namespace BKMNW

namespace NsStep

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- One closure dart: the five words. -/
def wr1 : Stmt := block [
  .addN 7531 7517 7530, .loadN 7532 7531,
  .addN 7531 7501 7532, .loadN 7533 7531,
  .addN 7531 7516 7533, .loadN 7534 7531, .subN 7534 7534 7522,
  .addN 7531 7510 7532, .loadN 7535 7531,
  .addN 7531 7516 7535, .loadN 7536 7531, .subN 7536 7536 7522,
  .addN 7531 7512 7532, .loadN 7537 7531, .subN 7537 7537 7522,
  .addN 7531 7512 7533, .loadN 7538 7531, .subN 7538 7538 7522,
  .addN 7531 7550 7530, .storeN 7531 7532,
  .addN 7531 7551 7530, .storeN 7531 7534,
  .addN 7531 7552 7530, .storeN 7531 7536,
  .addN 7531 7553 7530, .storeN 7531 7537,
  .addN 7531 7554 7530, .storeN 7531 7538,
  .addN 7530 7530 7522]

/-- One kept dart: the length. -/
def wr2 : Stmt := block [
  .addN 7531 7517 7530, .loadN 7532 7531, .addN 7531 7515 7532, .loadN 7533 7531,
  .addN 7533 7533 7525, .subN 7533 7533 7504, .addN 7531 7555 7530, .storeN 7531 7533,
  .addN 7530 7530 7522]

/-- The bases `A + 4 + j k`. -/
def wrInit : Stmt := block [.constN 7522 1, .constN 7556 4, .addN 7550 7506 7556,
  .addN 7551 7550 7526, .addN 7552 7551 7526, .addN 7553 7552 7526, .addN 7554 7553 7526,
  .addN 7555 7554 7526, .constN 7530 0]

/-- The header. -/
def wrH : Stmt := block [.storeN 7506 7500, .addN 7531 7506 7522, .storeN 7531 7527,
  .addN 7531 7531 7522, .storeN 7531 7526, .addN 7531 7531 7522, .storeN 7531 7525]

/-- **The frame writer.** -/
def wrProg : Stmt := .seq wrInit (.seq (.whileLtN 7530 7526 wr1)
  (.seq (.seq (block [.constN 7530 0]) (.whileLtN 7530 7527 wr2)) wrH))

variable {P : Input} {W : ℕ}

/-- Five writes at `B + j k + h`, `j < 5`. -/
def upd5 (mem : ℕ → ℕ) (B k h v0 v1 v2 v3 v4 : ℕ) : ℕ → ℕ :=
  upd (upd (upd (upd (upd mem (B + h) v0) (B + k + h) v1) (B + 2 * k + h) v2) (B + 3 * k + h) v3)
    (B + 4 * k + h) v4

lemma upd5_other {mem : ℕ → ℕ} {B k h v0 v1 v2 v3 v4 a : ℕ} (h0 : a ≠ B + h)
    (h1 : a ≠ B + k + h) (h2 : a ≠ B + 2 * k + h) (h3 : a ≠ B + 3 * k + h)
    (h4 : a ≠ B + 4 * k + h) : upd5 mem B k h v0 v1 v2 v3 v4 a = mem a := by
  unfold upd5
  rw [upd_other _ _ _ h4, upd_other _ _ _ h3, upd_other _ _ _ h2, upd_other _ _ _ h1,
    upd_other _ _ _ h0]

lemma upd5_cells {mem : ℕ → ℕ} {B k h v0 v1 v2 v3 v4 : ℕ} (hk : h < k) :
    upd5 mem B k h v0 v1 v2 v3 v4 (B + h) = v0 ∧ upd5 mem B k h v0 v1 v2 v3 v4 (B + k + h) = v1 ∧
    upd5 mem B k h v0 v1 v2 v3 v4 (B + 2 * k + h) = v2 ∧
    upd5 mem B k h v0 v1 v2 v3 v4 (B + 3 * k + h) = v3 ∧
    upd5 mem B k h v0 v1 v2 v3 v4 (B + 4 * k + h) = v4 := by
  unfold upd5
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
      upd_other _ _ _ (by omega), upd_same]
  · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
      upd_same]
  · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_same]
  · rw [upd_other _ _ _ (by omega), upd_same]
  · rw [upd_same]

/-- The five words of the closure dart `h'` (values read in `m₀`). -/
def W5 (m₀ mem : ℕ → ℕ) (B k CDb RVb POb NXb LABb h' : ℕ) : Prop :=
  mem (B + h') = m₀ (CDb + h') ∧
    mem (B + k + h') = m₀ (POb + m₀ (RVb + m₀ (CDb + h'))) - 1 ∧
    mem (B + 2 * k + h') = m₀ (POb + m₀ (NXb + m₀ (CDb + h'))) - 1 ∧
    mem (B + 3 * k + h') = m₀ (LABb + m₀ (CDb + h')) - 1 ∧
    mem (B + 4 * k + h') = m₀ (LABb + m₀ (RVb + m₀ (CDb + h'))) - 1

lemma W5.upd5 {m₀ mem : ℕ → ℕ} {B k CDb RVb POb NXb LABb h' h v0 v1 v2 v3 v4 : ℕ}
    (hw : W5 m₀ mem B k CDb RVb POb NXb LABb h') (hh : h' < h) (hk : h < k) :
    W5 m₀ (upd5 mem B k h v0 v1 v2 v3 v4) B k CDb RVb POb NXb LABb h' := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := hw
  exact ⟨by rw [upd5_other (by omega) (by omega) (by omega) (by omega) (by omega)]; exact b1,
    by rw [upd5_other (by omega) (by omega) (by omega) (by omega) (by omega)]; exact b2,
    by rw [upd5_other (by omega) (by omega) (by omega) (by omega) (by omega)]; exact b3,
    by rw [upd5_other (by omega) (by omega) (by omega) (by omega) (by omega)]; exact b4,
    by rw [upd5_other (by omega) (by omega) (by omega) (by omega) (by omega)]; exact b5⟩

lemma W5.of {m₀ mem mem' : ℕ → ℕ} {B k CDb RVb POb NXb LABb h' : ℕ}
    (hw : W5 m₀ mem B k CDb RVb POb NXb LABb h') (hk : h' < k)
    (e : ∀ a, B ≤ a → a < B + 5 * k → mem' a = mem a) :
    W5 m₀ mem' B k CDb RVb POb NXb LABb h' := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := hw
  exact ⟨by rw [e _ (by omega) (by omega)]; exact b1, by rw [e _ (by omega) (by omega)]; exact b2,
    by rw [e _ (by omega) (by omega)]; exact b3, by rw [e _ (by omega) (by omega)]; exact b4,
    by rw [e _ (by omega) (by omega)]; exact b5⟩

/-- The registers of the writer. -/
def WrRegs (c : Config) (m RVb K A NXb LABb MLb POb CDb L k m' : ℕ) : Prop :=
  c.nreg 7500 = m ∧ c.nreg 7501 = RVb ∧ c.nreg 7504 = K ∧ c.nreg 7506 = A ∧
    c.nreg 7510 = NXb ∧ c.nreg 7512 = LABb ∧ c.nreg 7515 = MLb ∧ c.nreg 7516 = POb ∧
    c.nreg 7517 = CDb ∧ c.nreg 7525 = L ∧ c.nreg 7526 = k ∧ c.nreg 7527 = m'

lemma WrRegs.of {c d : Config} {m RVb K A NXb LABb MLb POb CDb L k m' : ℕ}
    (h : WrRegs c m RVb K A NXb LABb MLb POb CDb L k m')
    (hd : ∀ r, r < 7530 → r ≠ 7522 → d.nreg r = c.nreg r) :
    WrRegs d m RVb K A NXb LABb MLb POb CDb L k m' := by
  obtain ⟨a0, a1, a4, a6, a10, a12, a15, a16, a17, a25, a26, a27⟩ := h
  exact ⟨by rw [hd _ (by omega) (by omega), a0], by rw [hd _ (by omega) (by omega), a1],
    by rw [hd _ (by omega) (by omega), a4], by rw [hd _ (by omega) (by omega), a6],
    by rw [hd _ (by omega) (by omega), a10], by rw [hd _ (by omega) (by omega), a12],
    by rw [hd _ (by omega) (by omega), a15], by rw [hd _ (by omega) (by omega), a16],
    by rw [hd _ (by omega) (by omega), a17], by rw [hd _ (by omega) (by omega), a25],
    by rw [hd _ (by omega) (by omega), a26], by rw [hd _ (by omega) (by omega), a27]⟩

theorem wr1_exec (c : Config) (hc : WordsBounded W c)
    {m RVb K A NXb LABb MLb POb CDb L k m' h x r p1 s p2 a b : ℕ}
    (hR : WrRegs c m RVb K A NXb LABb MLb POb CDb L k m') (r22 : c.nreg 7522 = 1)
    (r30 : c.nreg 7530 = h) (r50 : c.nreg 7550 = A + 4) (r51 : c.nreg 7551 = A + 4 + k)
    (r52 : c.nreg 7552 = A + 4 + 2 * k) (r53 : c.nreg 7553 = A + 4 + 3 * k)
    (r54 : c.nreg 7554 = A + 4 + 4 * k)
    (hx : c.nmem (CDb + h) = x) (hr : c.nmem (RVb + x) = r) (hp1 : c.nmem (POb + r) = p1)
    (hs : c.nmem (NXb + x) = s) (hp2 : c.nmem (POb + s) = p2) (ha : c.nmem (LABb + x) = a)
    (hb : c.nmem (LABb + r) = b)
    (w1 : CDb + h ≤ W) (w2 : RVb + x ≤ W) (w3 : POb + r ≤ W) (w4 : NXb + x ≤ W)
    (w5 : POb + s ≤ W) (w6 : LABb + x ≤ W) (w7 : LABb + r ≤ W) (w8 : A + 4 + 4 * k + h ≤ W)
    (w9 : h + 1 ≤ W) :
    ∃ c' t, Exec P W wr1 c c' t ∧ t = 29 ∧ c'.nreg 7530 = h + 1 ∧
      c'.nmem = upd5 c.nmem (A + 4) k h x (p1 - 1) (p2 - 1) (a - 1) (b - 1) ∧
      (∀ x, (x < 7530 ∨ 7538 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨a0, a1, a4, a6, a10, a12, a15, a16, a17, a25, a26, a27⟩ := hR
  unfold wr1
  exec_block
  all_goals try (config_simp; simp only [a1, a10, a12, a16, a17, r22, r30, r50, r51, r52, r53,
    r54, hx, hr, hp1, hs, hp2, ha, hb]; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r22, r30]
  · config_simp; simp only [a1, a10, a12, a16, a17, r22, r30, r50, r51, r52, r53, r54, hx, hr,
      hp1, hs, hp2, ha, hb]; rfl
  · config_simp; simp (disch := omega) only [Machine.upd_other]

theorem wr2_exec (c : Config) (hc : WordsBounded W c)
    {m RVb K A NXb LABb MLb POb CDb L k m' h x ml : ℕ}
    (hR : WrRegs c m RVb K A NXb LABb MLb POb CDb L k m') (r22 : c.nreg 7522 = 1)
    (r30 : c.nreg 7530 = h) (r55 : c.nreg 7555 = A + 4 + 5 * k)
    (hx : c.nmem (CDb + h) = x) (hml : c.nmem (MLb + x) = ml)
    (w1 : CDb + h ≤ W) (w2 : MLb + x ≤ W) (w3 : ml + L ≤ W) (w8 : A + 4 + 5 * k + h ≤ W)
    (w9 : h + 1 ≤ W) :
    ∃ c' t, Exec P W wr2 c c' t ∧ t = 9 ∧ c'.nreg 7530 = h + 1 ∧
      c'.nmem = upd c.nmem (A + 4 + 5 * k + h) (ml + L - K) ∧
      (∀ x, (x < 7530 ∨ 7538 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨a0, a1, a4, a6, a10, a12, a15, a16, a17, a25, a26, a27⟩ := hR
  unfold wr2
  exec_block
  all_goals try (config_simp; simp only [a4, a15, a17, a25, r22, r30, r55, hx, hml]; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r22, r30]
  · config_simp; simp only [a4, a15, a17, a25, r22, r30, r55, hx, hml]
  · config_simp; simp (disch := omega) only [Machine.upd_other]

/-- **Loop 1**: the five words of every closure dart. -/
theorem wrL1_exec (c : Config) (hc : WordsBounded W c)
    {m RVb K A NXb LABb MLb POb CDb L k m' : ℕ}
    (hR : WrRegs c m RVb K A NXb LABb MLb POb CDb L k m') (r22 : c.nreg 7522 = 1)
    (r30 : c.nreg 7530 = 0) (r50 : c.nreg 7550 = A + 4) (r51 : c.nreg 7551 = A + 4 + k)
    (r52 : c.nreg 7552 = A + 4 + 2 * k) (r53 : c.nreg 7553 = A + 4 + 3 * k)
    (r54 : c.nreg 7554 = A + 4 + 4 * k)
    (hxk : ∀ h < k, c.nmem (CDb + h) < m) (hrv : ∀ h < k, c.nmem (RVb + c.nmem (CDb + h)) < m)
    (hnx : ∀ h < k, c.nmem (NXb + c.nmem (CDb + h)) < m)
    (dC : CDb + k ≤ A) (dP : POb + m ≤ A) (dN : NXb + m ≤ A) (dL : LABb + m ≤ A)
    (dR : RVb + m ≤ A ∨ A + 4 + 5 * k ≤ RVb) (wR : RVb + m ≤ W) (wA : A + 4 + 5 * k ≤ W) :
    ∃ c' t, Exec P W (.whileLtN 7530 7526 wr1) c c' t ∧ t ≤ 31 * k + 2 ∧
      (∀ h < k, W5 c.nmem c'.nmem (A + 4) k CDb RVb POb NXb LABb h) ∧
      (∀ a, (a < A + 4 ∨ A + 4 + 5 * k ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 7530 ∨ 7538 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun h c' =>
    (∀ x, (x < 7530 ∨ 7538 < x) → c'.nreg x = c.nreg x) ∧
    (∀ h' < h, W5 m₀ c'.nmem (A + 4) k CDb RVb POb NXb LABb h') ∧
    (∀ a, (a < A + 4 ∨ A + 4 + 5 * k ≤ a) → c'.nmem a = m₀ a) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h30, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 7530)
    (b := 7526) (body := wr1) J (B := 29) c hc r30 hR.2.2.2.2.2.2.2.2.2.2.1 (Nat.zero_le k)
    ⟨fun _ _ => rfl, fun h hh => absurd hh (by omega), fun a _ => rfl, rfl, rfl, rfl⟩
    (fun h c' hlo hhi hw h30 h26 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 7530 ∨ 7538 < x) → c'.nreg x = c.nreg x := j1
      have hR' := hR.of fun r hr _ => f r (by omega)
      have hx := hxk h hhi
      have hr := hrv h hhi
      have hs := hnx h hhi
      have e1 : c'.nmem (CDb + h) = m₀ (CDb + h) := j3 _ (by omega)
      have e2 : c'.nmem (RVb + m₀ (CDb + h)) = m₀ (RVb + m₀ (CDb + h)) := j3 _ (by omega)
      have e3 : c'.nmem (POb + m₀ (RVb + m₀ (CDb + h))) = m₀ (POb + m₀ (RVb + m₀ (CDb + h))) :=
        j3 _ (by omega)
      have e4 : c'.nmem (NXb + m₀ (CDb + h)) = m₀ (NXb + m₀ (CDb + h)) := j3 _ (by omega)
      have e5 : c'.nmem (POb + m₀ (NXb + m₀ (CDb + h))) = m₀ (POb + m₀ (NXb + m₀ (CDb + h))) :=
        j3 _ (by omega)
      have e6 : c'.nmem (LABb + m₀ (CDb + h)) = m₀ (LABb + m₀ (CDb + h)) := j3 _ (by omega)
      have e7 : c'.nmem (LABb + m₀ (RVb + m₀ (CDb + h))) = m₀ (LABb + m₀ (RVb + m₀ (CDb + h))) :=
        j3 _ (by omega)
      obtain ⟨c'', t, ex, ht, h30', hm', hn', hr', hrm', ho'⟩ := wr1_exec (P := P) c' hw hR'
        (by rw [f _ (by omega), r22]) h30 (by rw [f _ (by omega), r50])
        (by rw [f _ (by omega), r51]) (by rw [f _ (by omega), r52]) (by rw [f _ (by omega), r53])
        (by rw [f _ (by omega), r54]) e1 e2 e3 e4 e5 e6 e7 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      refine ⟨c'', t, ex, ht.le, h30', by rw [hn' _ (by omega)]; exact h26,
        fun x hx => by rw [hn' x hx, f x hx], fun h' hh' => ?_, fun a ha => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hh' with hh' | rfl
        · exact (j2 h' hh').upd5 hh' hhi
        · exact upd5_cells hhi
      · rw [hm', upd5_other (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact j3 a ha)
  exact ⟨c₂, k₂, e₂, by omega, j2, j3, j1, j4, j5, j6⟩

/-- **Loop 2**: the lengths of the kept darts. -/
theorem wrL2_exec (c : Config) (hc : WordsBounded W c)
    {m RVb K A NXb LABb MLb POb CDb L k m' : ℕ}
    (hR : WrRegs c m RVb K A NXb LABb MLb POb CDb L k m') (r22 : c.nreg 7522 = 1)
    (r55 : c.nreg 7555 = A + 4 + 5 * k)
    (hxk : ∀ h < m', c.nmem (CDb + h) < m)
    (hml : ∀ h < m', c.nmem (MLb + c.nmem (CDb + h)) + L ≤ W)
    (dC : CDb + m' ≤ A) (dM : MLb + m ≤ A) (wA : A + 4 + 5 * k + m' ≤ W) :
    ∃ c' t, Exec P W (.seq (block [.constN 7530 0]) (.whileLtN 7530 7527 wr2)) c c' t ∧
      t ≤ 11 * m' + 3 ∧
      (∀ h < m', c'.nmem (A + 4 + 5 * k + h) = c.nmem (MLb + c.nmem (CDb + h)) + L - K) ∧
      (∀ a, (a < A + 4 + 5 * k ∨ A + 4 + 5 * k + m' ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 7530 ∨ 7538 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₃, k₃, e₃, hk₃, f30, fn₃, fm₃, fr₃, frm₃, fo₃⟩ : ∃ c₃ k₃,
      Exec P W (block [.constN 7530 0]) c c₃ k₃ ∧ k₃ = 1 ∧ c₃.nreg 7530 = 0 ∧
      (∀ x, x ≠ 7530 → c₃.nreg x = c.nreg x) ∧ c₃.nmem = c.nmem ∧
      c₃.rreg = c.rreg ∧ c₃.rmem = c.rmem ∧ c₃.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp; simp (disch := omega) only [Machine.upd_other]
  set m₀ := c.nmem with hm₀
  have hR₃ := hR.of fun r hr _ => fn₃ r (by omega)
  let J2 : ℕ → Config → Prop := fun h c' =>
    (∀ x, (x < 7530 ∨ 7538 < x) → c'.nreg x = c.nreg x) ∧
    (∀ h' < h, c'.nmem (A + 4 + 5 * k + h') = m₀ (MLb + m₀ (CDb + h')) + L - K) ∧
    (∀ a, (a < A + 4 + 5 * k ∨ A + 4 + 5 * k + m' ≤ a) → c'.nmem a = m₀ a) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₄, k₄, e₄, hk₄, hw₄, h30₄, i1, i2, i3, i4, i5, i6⟩ := lnRange (P := P) (a := 7530)
    (b := 7527) (body := wr2) J2 (B := 9) c₃ e₃.wb_right f30 hR₃.2.2.2.2.2.2.2.2.2.2.2
    (Nat.zero_le m')
    ⟨fun x hx => fn₃ x (by omega), fun h hh => absurd hh (by omega), fun a _ => by rw [fm₃],
      fr₃, frm₃, fo₃⟩
    (fun h c' hlo hhi hw h30 h27 ⟨i1, i2, i3, i4, i5, i6⟩ => by
      have f : ∀ x, (x < 7530 ∨ 7538 < x) → c'.nreg x = c.nreg x := i1
      have hR' := hR.of fun r hr _ => f r (by omega)
      have hx := hxk h hhi
      have e1 : c'.nmem (CDb + h) = m₀ (CDb + h) := i3 _ (by omega)
      have e2 : c'.nmem (MLb + m₀ (CDb + h)) = m₀ (MLb + m₀ (CDb + h)) := i3 _ (by omega)
      obtain ⟨c'', t, ex, ht, h30', hm', hn', hr', hrm', ho'⟩ := wr2_exec (P := P) c' hw hR'
        (by rw [f _ (by omega), r22]) h30 (by rw [f _ (by omega), r55]) e1 e2 (by omega)
        (by omega) (hml h hhi) (by omega) (by omega)
      refine ⟨c'', t, ex, ht.le, h30', by rw [hn' _ (by omega)]; exact h27,
        fun x hx => by rw [hn' x hx, f x hx], fun h' hh' => ?_, fun a ha => ?_,
        by rw [hr', i4], by rw [hrm', i5], by rw [ho', i6]⟩
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hh' with hh' | rfl
        · rw [upd_other _ _ _ (by omega)]; exact i2 h' hh'
        · rw [upd_same]
      · rw [hm', upd_other _ _ _ (by omega)]; exact i3 a ha)
  exact ⟨c₄, k₃ + k₄, .seq e₃ e₄, by omega, i2, i3, i1, i4, i5, i6⟩

set_option maxHeartbeats 1000000 in
/-- **The frame writer** (see the module docstring): within `31 k + 11 m' + 21` steps. -/
theorem wrProg_exec (c : Config) (hc : WordsBounded W c)
    {m RVb K A NXb LABb MLb POb CDb L k m' : ℕ}
    (hR : WrRegs c m RVb K A NXb LABb MLb POb CDb L k m')
    (hxk : ∀ h < k, c.nmem (CDb + h) < m) (hrv : ∀ h < k, c.nmem (RVb + c.nmem (CDb + h)) < m)
    (hnx : ∀ h < k, c.nmem (NXb + c.nmem (CDb + h)) < m)
    (hml : ∀ h < m', c.nmem (MLb + c.nmem (CDb + h)) + L ≤ W) (hmk : m' ≤ k)
    (dC : CDb + k ≤ A) (dP : POb + m ≤ A) (dN : NXb + m ≤ A) (dL : LABb + m ≤ A)
    (dM : MLb + m ≤ A) (dR : RVb + m ≤ A ∨ A + 4 + 5 * k + m' ≤ RVb) (wR : RVb + m ≤ W)
    (wA : A + 4 + 5 * k + m' ≤ W) :
    ∃ c' t, Exec P W wrProg c c' t ∧ t ≤ 31 * k + 11 * m' + 21 ∧
      c'.nmem A = m ∧ c'.nmem (A + 1) = m' ∧ c'.nmem (A + 2) = k ∧ c'.nmem (A + 3) = L ∧
      (∀ h < k, W5 c.nmem c'.nmem (A + 4) k CDb RVb POb NXb LABb h) ∧
      (∀ h < m', c'.nmem (A + 4 + 5 * k + h) = c.nmem (MLb + c.nmem (CDb + h)) + L - K) ∧
      (∀ a, (a < A ∨ A + 4 + 5 * k + m' ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 7522 ∨ (7522 < r ∧ r < 7530) ∨ (7538 < r ∧ r < 7550) ∨ 7556 < r) →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨a0, a1, a4, a6, a10, a12, a15, a16, a17, a25, a26, a27⟩ := hR
  unfold wrProg
  obtain ⟨c₁, k₁, e₁, hk₁, g22, g50, g51, g52, g53, g54, g55, g30, gn₁, gm₁, gr₁, grm₁, go₁⟩ :
      ∃ c₁ k₁, Exec P W wrInit c c₁ k₁ ∧ k₁ = 9 ∧ c₁.nreg 7522 = 1 ∧ c₁.nreg 7550 = A + 4 ∧
      c₁.nreg 7551 = A + 4 + k ∧ c₁.nreg 7552 = A + 4 + 2 * k ∧ c₁.nreg 7553 = A + 4 + 3 * k ∧
      c₁.nreg 7554 = A + 4 + 4 * k ∧ c₁.nreg 7555 = A + 4 + 5 * k ∧ c₁.nreg 7530 = 0 ∧
      (∀ x, x ≠ 7522 → x ≠ 7530 → (x < 7550 ∨ 7556 < x) → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold wrInit
    exec_block
    all_goals try ((try config_simp); (try simp only [a6, a26]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x a b d => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; simp only [a6, a26]; try omega)
    all_goals try (config_simp; done)
    all_goals (config_simp; simp (disch := omega) only [Machine.upd_other])
  have hR₀ : WrRegs c m RVb K A NXb LABb MLb POb CDb L k m' :=
    ⟨a0, a1, a4, a6, a10, a12, a15, a16, a17, a25, a26, a27⟩
  have hR₁ : WrRegs c₁ m RVb K A NXb LABb MLb POb CDb L k m' :=
    hR₀.of fun r hr hr' => gn₁ r hr' (by omega) (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, j2, j3, j1, j4, j5, j6⟩ := wrL1_exec (P := P) c₁ e₁.wb_right hR₁ g22 g30
    g50 g51 g52 g53 g54 (fun h hh => by rw [gm₁]; exact hxk h hh)
    (fun x hx => by rw [gm₁]; exact hrv x hx) (fun x hx => by rw [gm₁]; exact hnx x hx)
    dC dP dN dL (by omega) wR (by omega)
  have hR₂ := hR₁.of fun r hr _ => j1 r (by omega)
  have hm2 : ∀ a, (a < A + 4 ∨ A + 4 + 5 * k ≤ a) → c₂.nmem a = c.nmem a := fun a ha => by
    rw [j3 a ha, gm₁]
  obtain ⟨c₄, k₄, e₄, hk₄, i2, i3, i1, i4, i5, i6⟩ := wrL2_exec (P := P) c₂ e₂.wb_right hR₂
    (by rw [j1 _ (by omega), g22]) (by rw [j1 _ (by omega), g55])
    (fun h hh => by rw [hm2 _ (by omega)]; exact hxk h (by omega))
    (fun h hh => by
      rw [hm2 (CDb + h) (by omega), hm2 (MLb + c.nmem (CDb + h)) (by have := hxk h (by omega); omega)]
      exact hml h hh) (by omega) dM wA
  have hR₄ := hR₂.of fun r hr _ => i1 r (by omega)
  obtain ⟨b0, b1, b4, b6, b10, b12, b15, b16, b17, b25, b26, b27⟩ := hR₄
  obtain ⟨c₅, k₅, e₅, hk₅, gm₅, gn₅, gr₅, grm₅, go₅⟩ : ∃ c₅ k₅,
      Exec P W wrH c₄ c₅ k₅ ∧ k₅ = 7 ∧
      c₅.nmem = upd (upd (upd (upd c₄.nmem A m) (A + 1) m') (A + 2) k) (A + 3) L ∧
      (∀ x, x ≠ 7531 → c₅.nreg x = c₄.nreg x) ∧
      c₅.rreg = c₄.rreg ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output := by
    have h22 : c₄.nreg 7522 = 1 := by rw [i1 _ (by omega), j1 _ (by omega), g22]
    have hw₄ := e₄.wb_right
    unfold wrH
    exec_block
    all_goals try (config_simp; simp only [b0, b6, b25, b26, b27, h22]; omega)
    refine ⟨rfl, ?_, fun x a => ?_, rfl, rfl, rfl⟩
    · config_simp; simp only [b0, b6, b25, b26, b27, h22]
    · config_simp; simp (disch := omega) only [Machine.upd_other]
  have hm4 : ∀ a, (a < A + 4 ∨ A + 4 + 5 * k + m' ≤ a) → c₄.nmem a = c.nmem a := fun a ha => by
    rw [i3 a (by omega), hm2 a (by omega)]
  have hm5 : ∀ a, (a < A ∨ A + 4 ≤ a) → c₅.nmem a = c₄.nmem a := fun a ha => by
    rw [gm₅, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
      upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
  have j2' : ∀ h < k, W5 c.nmem c₂.nmem (A + 4) k CDb RVb POb NXb LABb h := by
    rw [← gm₁]; exact j2
  refine ⟨c₅, k₁ + (k₂ + (k₄ + k₅)), .seq e₁ (.seq e₂ (.seq e₄ e₅)), by omega,
    ?_, ?_, ?_, ?_, fun h hh => ?_, fun h hh => ?_, fun a ha => ?_, fun r hr => ?_,
    by rw [gr₅, i4, j4, gr₁], by rw [grm₅, i5, j5, grm₁], by rw [go₅, i6, j6, go₁]⟩
  · rw [gm₅, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
      upd_same]
  · rw [gm₅, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_same]
  · rw [gm₅, upd_other _ _ _ (by omega), upd_same]
  · rw [gm₅, upd_same]
  · exact (j2' h hh).of hh fun a h1 h2 => by rw [hm5 a (Or.inr h1), i3 a (by omega)]
  · rw [hm5 _ (Or.inr (by omega)), i2 h hh, hm2 (CDb + h) (by omega),
      hm2 (MLb + c.nmem (CDb + h)) (by have := hxk h (by omega); omega)]
  · rw [hm5 a (by omega), hm4 a (by omega)]
  · rw [gn₅ r (by omega), i1 r (by omega), j1 r (by omega)]
    exact gn₁ r (by omega) (by omega) (by omega)

end NsStep

end BKMNW

end PlanarFlow
