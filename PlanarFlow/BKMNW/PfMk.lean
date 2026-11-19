module

public import PlanarFlow.BKMNW.LgS5DD

/-!
# The path's flags on the record, the machine part (I): a mark loop and the value blocks

* `pfMkBody`, **`pfMk`** (`T[KEY[j]] := 1` for `j < m`; registers `6030 = m`, `6031 = KEYb`,
  `6032 = Tb`, written `6033 … 6035`), `pfMkBody_exec`, **`pfMk_exec`** (`7 m + 4` steps: the
  table is `1` at the keys and unchanged elsewhere);
* the value blocks of the keys (`mapRunS`, counter `6520`): `vbPA` (`VK[IX[PD[j] - 1]]` if
  `PD[j] ≠ 0`, else `n`), `vbPB` / `vbPC` / `vbPD` (`IX[PD[j] - 1]`, `RP[IX[PD[j] - 1]]`,
  `VK[RP[IX[PD[j] - 1]]]` if `PD[j + 1] ≠ 0`, else `n`), `vbPV` (`VM[VK[i]]`), with their exec
  lemmas. Registers `6000 = n`, `6001 = RPb`, `6002 = IXb`, `6003 = PDb`, `6004 = VKb`,
  `6005 = VMb`, `6010 = 1`.
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

/-! ### The mark loop -/

/-- One mark: `T[KEY[j]] := 1`. -/
def pfMkBody : Stmt :=
  block [.addN 6035 6031 6034, .loadN 6035 6035, .addN 6035 6032 6035, .storeN 6035 6033,
    .addN 6034 6034 6033]

/-- **The mark loop**: `T[KEY[j]] := 1` for `j < m`. -/
def pfMk : Stmt := .seq (block [.constN 6033 1, .constN 6034 0]) (.whileLtN 6034 6030 pfMkBody)

/-- The key of the tails: `VK[IX[PD[j] - 1]]` if `PD[j] ≠ 0`, else `n`. -/
def vbPA : Stmt :=
  block [.addN 6524 6003 6520, .loadN 6524 6524, .divN 6525 6524 6524, .subN 6526 6524 6010,
    .addN 6526 6002 6526, .loadN 6526 6526, .addN 6526 6004 6526, .loadN 6526 6526,
    .mulN 6527 6525 6526, .subN 6528 6010 6525, .mulN 6528 6528 6000, .addN 6523 6527 6528]

/-- The first dart: `IX[PD[j] - 1]` if `PD[j + 1] ≠ 0`, else `n`. -/
def vbPB : Stmt :=
  block [.addN 6524 6003 6520, .loadN 6526 6524, .addN 6524 6524 6010, .loadN 6524 6524,
    .divN 6525 6524 6524, .subN 6526 6526 6010, .addN 6526 6002 6526, .loadN 6526 6526,
    .mulN 6527 6525 6526, .subN 6528 6010 6525, .mulN 6528 6528 6000, .addN 6523 6527 6528]

/-- The reverse: `RP[IX[PD[j] - 1]]` if `PD[j + 1] ≠ 0`, else `n`. -/
def vbPC : Stmt :=
  block [.addN 6524 6003 6520, .loadN 6526 6524, .addN 6524 6524 6010, .loadN 6524 6524,
    .divN 6525 6524 6524, .subN 6526 6526 6010, .addN 6526 6002 6526, .loadN 6526 6526,
    .addN 6526 6001 6526, .loadN 6526 6526,
    .mulN 6527 6525 6526, .subN 6528 6010 6525, .mulN 6528 6528 6000, .addN 6523 6527 6528]

/-- The head's key: `VK[RP[IX[PD[j] - 1]]]` if `PD[j + 1] ≠ 0`, else `n`. -/
def vbPD : Stmt :=
  block [.addN 6524 6003 6520, .loadN 6526 6524, .addN 6524 6524 6010, .loadN 6524 6524,
    .divN 6525 6524 6524, .subN 6526 6526 6010, .addN 6526 6002 6526, .loadN 6526 6526,
    .addN 6526 6001 6526, .loadN 6526 6526, .addN 6526 6004 6526, .loadN 6526 6526,
    .mulN 6527 6525 6526, .subN 6528 6010 6525, .mulN 6528 6528 6000, .addN 6523 6527 6528]

/-- The vertex flag: `VM[VK[i]]`. -/
def vbPV : Stmt :=
  block [.addN 6524 6004 6520, .loadN 6524 6524, .addN 6524 6005 6524, .loadN 6523 6524]

section Exec

variable {P : Input} {W : ℕ}

theorem pfMkBody_exec (c : Config) (hc : WordsBounded W c) {m KEYb Tb j : ℕ}
    (r1 : c.nreg 6031 = KEYb) (r2 : c.nreg 6032 = Tb) (r3 : c.nreg 6033 = 1)
    (r4 : c.nreg 6034 = j) (w1 : KEYb + j ≤ W) (w2 : Tb + c.nmem (KEYb + j) ≤ W)
    (w3 : j + 1 ≤ W) :
    ∃ c' t, Exec P W pfMkBody c c' t ∧ t = 5 ∧ c'.nreg 6034 = j + 1 ∧
      c'.nmem = upd c.nmem (Tb + c.nmem (KEYb + j)) 1 ∧
      (∀ x, (x < 6034 ∨ 6035 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pfMkBody
  exec_block
  all_goals try (config_simp; (try simp only [r1, r2, r3, r4]); omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r1, r2, r3, r4]); done)
  · config_simp; simp (disch := omega) only [upd_other]

/-- **The mark loop**: with keys `KEY[j] < nk` (`j < m`) outside the table `[Tb, Tb + nk)`,
within `7 m + 4` steps `T[x] = 1` if `x` is a key, else unchanged (`x < nk`); memory outside the
table and registers outside `6033 … 6035` kept. -/
theorem pfMk_exec (c : Config) (hc : WordsBounded W c) {m nk KEYb Tb : ℕ}
    (r0 : c.nreg 6030 = m) (r1 : c.nreg 6031 = KEYb) (r2 : c.nreg 6032 = Tb)
    (hkey : ∀ j < m, c.nmem (KEYb + j) < nk)
    (d1 : ∀ j < m, ¬ (Tb ≤ KEYb + j ∧ KEYb + j < Tb + nk))
    (w1 : KEYb + m ≤ W) (w2 : Tb + nk ≤ W) (w3 : m + 1 ≤ W) :
    ∃ c' t, Exec P W pfMk c c' t ∧ t ≤ 7 * m + 4 ∧
      (∀ x < nk, c'.nmem (Tb + x) =
        if ∃ j < m, c.nmem (KEYb + j) = x then 1 else c.nmem (Tb + x)) ∧
      (∀ a, ¬ (Tb ≤ a ∧ a < Tb + nk) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6033 ∨ 6035 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  classical
  unfold pfMk
  obtain ⟨c₁, k₁, e₁, hk₁, g3, g4, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 6033 1, .constN 6034 0]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 6033 = 1 ∧ c₁.nreg 6034 = 0 ∧
      (∀ x, x ≠ 6033 → x ≠ 6034 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; done)
    · config_simp; simp (disch := omega) only [upd_other]
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 6033 → x ≠ 6034 → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 6034 ∨ 6035 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ x < nk, c'.nmem (Tb + x) = if ∃ j < i, m₀ (KEYb + j) = x then 1 else m₀ (Tb + x)) ∧
    (∀ a, ¬ (Tb ≤ a ∧ a < Tb + nk) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h34, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P)
    (a := 6034) (b := 6030) (body := pfMkBody) J (B := 5) c₁ hw₁ g4
    (by rw [q _ (by omega) (by omega), r0]) (Nat.zero_le m)
    ⟨fun _ _ => rfl, fun x hx => by rw [gm₁]; simp, fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h34 h30 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 6034 ∨ 6035 < x) → c'.nreg x = c₁.nreg x := j1
      have eK : c'.nmem (KEYb + i) = m₀ (KEYb + i) := j3 _ (d1 i hhi)
      have hk := hkey i hhi
      obtain ⟨c'', t, ex, ht, h34', hm', hn', hr', hrm', ho'⟩ :=
        pfMkBody_exec (P := P) c' hw (KEYb := KEYb) (Tb := Tb) (m := m)
          (by rw [f _ (by omega), q _ (by omega) (by omega), r1])
          (by rw [f _ (by omega), q _ (by omega) (by omega), r2])
          (by rw [f _ (by omega), g3]) h34 (by omega) (by rw [eK]; omega) (by omega)
      rw [eK] at hm'
      refine ⟨c'', t, ex, ht.le, h34', by rw [hn' _ (by omega)]; exact h30,
        fun x hx => by rw [hn' x hx, f x hx], fun x hx => ?_, fun a ha => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm']
        by_cases hx' : m₀ (KEYb + i) = x
        · subst hx'
          rw [upd_same, iteT ⟨i, by omega, rfl⟩]
        · rw [upd_other _ _ _ (by omega), j2 x hx]
          congr 1
          apply propext
          constructor
          · rintro ⟨j, hj, h⟩; exact ⟨j, by omega, h⟩
          · rintro ⟨j, hj, h⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
            · exact ⟨j, hj, h⟩
            · exact absurd h hx'
      · rw [hm', upd_other _ _ _ (by omega)]; exact j3 a ha)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3,
    fun x hx => by rw [j1 x (by omega), q x (by omega) (by omega)], by rw [j4, gr₁],
    by rw [j5, grm₁], by rw [j6, go₁]⟩

theorem vbPA_exec (c : Config) (hc : WordsBounded W c) {j n PDb IXb VKb a i v : ℕ}
    (r20 : c.nreg 6520 = j) (r00 : c.nreg 6000 = n) (r02 : c.nreg 6002 = IXb)
    (r03 : c.nreg 6003 = PDb) (r04 : c.nreg 6004 = VKb) (r10 : c.nreg 6010 = 1)
    (ha : c.nmem (PDb + j) = a) (hi : c.nmem (IXb + (a - 1)) = i) (hv : c.nmem (VKb + i) = v)
    (w1 : PDb + j ≤ W) (w2 : IXb + (a - 1) ≤ W) (w3 : VKb + i ≤ W) (w4 : n ≤ W) :
    ∃ c' k, Exec P W vbPA c c' k ∧ k ≤ 12 ∧ c'.nreg 6523 = pdSel (a / a) v n ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have bv : v ≤ W := hv ▸ hc.2 _
  have hd := dself_le a
  have m1 : a / a * v ≤ W := fmul_le hd bv
  have m2 : (1 - a / a) * n ≤ W := fmul_le (Nat.sub_le _ _) w4
  have m3 : pdSel (a / a) v n ≤ W := pdSel_le hd bv w4
  unfold pdSel at m3
  unfold vbPA
  exec_block
  all_goals try (config_simp; (try simp only [r20, r00, r02, r03, r04, r10, ha, hi, hv]); omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r20, r00, r02, r03, r04, r10, ha, hi, hv, pdSel]
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

theorem vbPB_exec (c : Config) (hc : WordsBounded W c) {j n PDb IXb a b i : ℕ}
    (r20 : c.nreg 6520 = j) (r00 : c.nreg 6000 = n) (r02 : c.nreg 6002 = IXb)
    (r03 : c.nreg 6003 = PDb) (r10 : c.nreg 6010 = 1)
    (ha : c.nmem (PDb + j) = a) (hb : c.nmem (PDb + j + 1) = b)
    (hi : c.nmem (IXb + (a - 1)) = i)
    (w1 : PDb + j + 1 ≤ W) (w2 : IXb + (a - 1) ≤ W) (w4 : n ≤ W) :
    ∃ c' k, Exec P W vbPB c c' k ∧ k ≤ 12 ∧ c'.nreg 6523 = pdSel (b / b) i n ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have bi : i ≤ W := hi ▸ hc.2 _
  have hd := dself_le b
  have m1 : b / b * i ≤ W := fmul_le hd bi
  have m2 : (1 - b / b) * n ≤ W := fmul_le (Nat.sub_le _ _) w4
  have m3 : pdSel (b / b) i n ≤ W := pdSel_le hd bi w4
  unfold pdSel at m3
  unfold vbPB
  exec_block
  all_goals try (config_simp; (try simp only [r20, r00, r02, r03, r10, ha, hb, hi]); omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r20, r00, r02, r03, r10, ha, hb, hi, pdSel]
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

theorem vbPC_exec (c : Config) (hc : WordsBounded W c) {j n PDb IXb RPb a b i r : ℕ}
    (r20 : c.nreg 6520 = j) (r00 : c.nreg 6000 = n) (r01 : c.nreg 6001 = RPb)
    (r02 : c.nreg 6002 = IXb) (r03 : c.nreg 6003 = PDb) (r10 : c.nreg 6010 = 1)
    (ha : c.nmem (PDb + j) = a) (hb : c.nmem (PDb + j + 1) = b)
    (hi : c.nmem (IXb + (a - 1)) = i) (hr : c.nmem (RPb + i) = r)
    (w1 : PDb + j + 1 ≤ W) (w2 : IXb + (a - 1) ≤ W) (w3 : RPb + i ≤ W) (w4 : n ≤ W) :
    ∃ c' k, Exec P W vbPC c c' k ∧ k ≤ 14 ∧ c'.nreg 6523 = pdSel (b / b) r n ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have br : r ≤ W := hr ▸ hc.2 _
  have hd := dself_le b
  have m1 : b / b * r ≤ W := fmul_le hd br
  have m2 : (1 - b / b) * n ≤ W := fmul_le (Nat.sub_le _ _) w4
  have m3 : pdSel (b / b) r n ≤ W := pdSel_le hd br w4
  unfold pdSel at m3
  unfold vbPC
  exec_block
  all_goals try (config_simp; (try simp only [r20, r00, r01, r02, r03, r10, ha, hb, hi, hr]); omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r20, r00, r01, r02, r03, r10, ha, hb, hi, hr, pdSel]
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

theorem vbPD_exec (c : Config) (hc : WordsBounded W c) {j n PDb IXb RPb VKb a b i r v : ℕ}
    (r20 : c.nreg 6520 = j) (r00 : c.nreg 6000 = n) (r01 : c.nreg 6001 = RPb)
    (r02 : c.nreg 6002 = IXb) (r03 : c.nreg 6003 = PDb) (r04 : c.nreg 6004 = VKb)
    (r10 : c.nreg 6010 = 1)
    (ha : c.nmem (PDb + j) = a) (hb : c.nmem (PDb + j + 1) = b)
    (hi : c.nmem (IXb + (a - 1)) = i) (hr : c.nmem (RPb + i) = r) (hv : c.nmem (VKb + r) = v)
    (w1 : PDb + j + 1 ≤ W) (w2 : IXb + (a - 1) ≤ W) (w3 : RPb + i ≤ W) (w5 : VKb + r ≤ W)
    (w4 : n ≤ W) :
    ∃ c' k, Exec P W vbPD c c' k ∧ k ≤ 16 ∧ c'.nreg 6523 = pdSel (b / b) v n ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have bv : v ≤ W := hv ▸ hc.2 _
  have hd := dself_le b
  have m1 : b / b * v ≤ W := fmul_le hd bv
  have m2 : (1 - b / b) * n ≤ W := fmul_le (Nat.sub_le _ _) w4
  have m3 : pdSel (b / b) v n ≤ W := pdSel_le hd bv w4
  unfold pdSel at m3
  unfold vbPD
  exec_block
  all_goals try (config_simp; (try simp only [r20, r00, r01, r02, r03, r04, r10, ha, hb, hi, hr, hv]); omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r20, r00, r01, r02, r03, r04, r10, ha, hb, hi, hr, hv, pdSel]
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

theorem vbPV_exec (c : Config) (hc : WordsBounded W c) {i VKb VMb x : ℕ}
    (r20 : c.nreg 6520 = i) (r04 : c.nreg 6004 = VKb) (r05 : c.nreg 6005 = VMb)
    (hx : c.nmem (VKb + i) = x) (w1 : VKb + i ≤ W) (w2 : VMb + x ≤ W) :
    ∃ c' k, Exec P W vbPV c c' k ∧ k ≤ 4 ∧ c'.nreg 6523 = c.nmem (VMb + x) ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold vbPV
  exec_block
  all_goals try (config_simp; (try simp only [r20, r04, r05, hx]); omega)
  refine ⟨by norm_num, ?_, fun y hy => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r20, r04, r05, hx]
  · have := vb_frame_aux hy
    config_simp
    simp (disch := omega) only [upd_other]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
