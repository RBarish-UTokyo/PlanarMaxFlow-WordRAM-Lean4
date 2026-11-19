module

public import PlanarFlow.BKMNW.S7OdS

/-!
# Stage 7 of `sepL` (III), machine part (I): a scatter loop and the value blocks

* `svF` (the table after `T[KEY[j]] := VAL[j]` for `j < m`), **`svF_spec`** (the value of the
  last `j` with that key, or the old value);
* `svBody`, **`svProg`** (registers `7160 = m`, `7161 = KEYb`, `7162 = VALb`, `7163 = Tb`,
  written `7164 … 7167`), **`svProg_exec`** (`9 m + 4` steps);
* the value blocks (`mapRunS`, counter `6520`): `vbIO` (`i`), `vbLS` (`LT[ID[i]]`), `vbIM`
  (`pdEq LS[i] i`), `vbP1` (`CI[LS[i]] + 1`), `vbKO` (`OW[j + 1]`), `vbVH`
  (`K (1 - HT[j + 1]) [OW[j + 1] ≠ 0]`), `vbWT` (`W1[q + 1] + W2[q + 1]`), `vbLF` (the flag of
  the left piece) with their exec lemmas.

Registers (bases): `7150 = IDb`, `7170 = LTb`, `7171 = LSb`, `7173 = CIb`, `7176 = OWb + 1`,
`7177 = HTb + 1`, `7178 = W1b + 1`, `7179 = W2b + 1`, `7180 = P1b`, `7181 = hv`, `7182 = r7`,
`7183 = Mx`, `7143 = K`, `6521 = 1`.
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

/-- The table after `T[KEY[j]] := VAL[j]` for `j < m`. -/
def svF (key val : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, old => old
  | m + 1, x, old => if key m = x then val m else svF key val m x old

theorem svF_spec (key val : ℕ → ℕ) (m x old : ℕ) :
    ((¬ ∃ j < m, key j = x) ∧ svF key val m x old = old) ∨
      (∃ j < m, key j = x ∧ svF key val m x old = val j ∧ ∀ j' < m, key j' = x → j' ≤ j) := by
  induction m with
  | zero => left; simp [svF]
  | succ m ih =>
    by_cases hk : key m = x
    · right
      refine ⟨m, by omega, hk, by simp [svF, hk], fun j' hj' _ => by omega⟩
    · have e : svF key val (m + 1) x old = svF key val m x old := by simp [svF, hk]
      rw [e]
      rcases ih with ⟨hn, hsv⟩ | ⟨j, hj, h1, h2, h3⟩
      · left
        refine ⟨fun ⟨j, hj, hkj⟩ => ?_, hsv⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact hn ⟨j, hj, hkj⟩
        · exact hk hkj
      · right
        refine ⟨j, by omega, h1, h2, fun j' hj' h' => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
        · exact h3 j' hj' h'
        · exact absurd h' hk

/-- One scatter: `T[KEY[j]] := VAL[j]`. -/
def svBody : Stmt :=
  block [.addN 7166 7161 7165, .loadN 7166 7166, .addN 7166 7163 7166, .addN 7167 7162 7165,
    .loadN 7167 7167, .storeN 7166 7167, .addN 7165 7165 7164]

/-- **The scatter loop**: `T[KEY[j]] := VAL[j]` for `j < m`. -/
def svProg : Stmt := .seq (block [.constN 7164 1, .constN 7165 0]) (.whileLtN 7165 7160 svBody)

/-- `IO[i] = i`. -/
def vbIO : Stmt := block [.copyN 6523 6520]

/-- `LS[i] = LT[ID[i]]`. -/
def vbLS : Stmt := block [.addN 6524 7150 6520, .loadN 6524 6524, .addN 6524 7170 6524, .loadN 6523 6524]

/-- `IM[i] = pdEq LS[i] i`. -/
def vbIM : Stmt :=
  block [.addN 6524 7171 6520, .loadN 6524 6524, .subN 6525 6524 6520, .subN 6526 6520 6524,
    .addN 6525 6525 6526, .divN 6526 6525 6525, .subN 6523 6521 6526]

/-- `P1[i] = CI[LS[i]] + 1`. -/
def vbP1 : Stmt :=
  block [.addN 6524 7171 6520, .loadN 6524 6524, .addN 6524 7173 6524, .loadN 6524 6524,
    .addN 6523 6524 6521]

/-- `KO[j] = OW[j + 1]`. -/
def vbKO : Stmt := block [.addN 6524 7176 6520, .loadN 6523 6524]

/-- `VH[j] = K (1 - HT[j + 1]) (OW[j + 1] / OW[j + 1])`. -/
def vbVH : Stmt :=
  block [.addN 6524 7176 6520, .loadN 6524 6524, .divN 6524 6524 6524, .addN 6525 7177 6520,
    .loadN 6525 6525, .subN 6525 6521 6525, .mulN 6524 6524 6525, .mulN 6523 6524 7143]

/-- `WT[q] = W1[q + 1] + W2[q + 1]`. -/
def vbWT : Stmt :=
  block [.addN 6524 7178 6520, .loadN 6524 6524, .addN 6525 7179 6520, .loadN 6525 6525,
    .addN 6523 6524 6525]

/-- `LF[i] = hv · pdEq (P1[i] - 1) r7 + (1 - hv) · [P1[i] - 1 < Mx]`. -/
def vbLF : Stmt :=
  block [.addN 6524 7180 6520, .loadN 6524 6524, .subN 6524 6524 6521,
    .subN 6525 6524 7182, .subN 6526 7182 6524, .addN 6525 6525 6526, .divN 6526 6525 6525,
    .subN 6525 6521 6526, .mulN 6525 7181 6525,
    .subN 6526 7183 6524, .divN 6526 6526 6526, .subN 6527 6521 7181, .mulN 6526 6527 6526,
    .addN 6523 6525 6526]

/-- The value of `vbVH`. -/
def vhV (K t o : ℕ) : ℕ := o / o * (1 - t) * K

/-- The value of `vbLF`. -/
def lfV (hv r7 mx p : ℕ) : ℕ :=
  hv * (1 - ((p - 1 - r7) + (r7 - (p - 1))) / ((p - 1 - r7) + (r7 - (p - 1)))) +
    (1 - hv) * ((mx - (p - 1)) / (mx - (p - 1)))

lemma vhV_eq {K t o : ℕ} (ht : t ≤ 1) : vhV K t o = if o ≠ 0 ∧ t = 0 then K else 0 := by
  unfold vhV
  rw [dself_eq]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ht with rfl | rfl <;> split_ifs <;> simp_all

lemma lfV_eq {hv r7 mx p : ℕ} (hhv : hv ≤ 1) :
    lfV hv r7 mx p = if (if hv = 1 then p - 1 = r7 else p - 1 < mx) then 1 else 0 := by
  unfold lfV
  have e1 := pdEq_eq (p - 1) r7
  unfold pdEq at e1
  rw [e1, dself_eq]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hhv with rfl | rfl
  · simp only [zero_mul, zero_add, Nat.sub_zero, one_mul]
    split_ifs <;> omega
  · simp only [one_mul, Nat.sub_self, zero_mul, add_zero]
    split_ifs <;> simp_all

section Exec

variable {P : Input} {W : ℕ}

theorem svBody_exec (c : Config) (hc : WordsBounded W c) {KEYb VALb Tb j : ℕ}
    (r1 : c.nreg 7161 = KEYb) (r2 : c.nreg 7162 = VALb) (r3 : c.nreg 7163 = Tb)
    (r4 : c.nreg 7164 = 1) (r5 : c.nreg 7165 = j) (w1 : KEYb + j ≤ W) (w2 : VALb + j ≤ W)
    (w3 : Tb + c.nmem (KEYb + j) ≤ W) (w4 : j + 1 ≤ W) :
    ∃ c' t, Exec P W svBody c c' t ∧ t = 7 ∧ c'.nreg 7165 = j + 1 ∧
      c'.nmem = upd c.nmem (Tb + c.nmem (KEYb + j)) (c.nmem (VALb + j)) ∧
      (∀ x, (x < 7165 ∨ 7167 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold svBody
  exec_block
  all_goals try (config_simp; (try simp only [r1, r2, r3, r4, r5]); omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp (disch := omega) only [upd_other, upd_same, r1, r2, r3, r4, r5]); done)
  all_goals try (config_simp; simp (disch := omega) only [upd_other])

/-- **The scatter loop** (see the module docstring). -/
theorem svProg_exec (c : Config) (hc : WordsBounded W c) {m nk KEYb VALb Tb : ℕ}
    (r0 : c.nreg 7160 = m) (r1 : c.nreg 7161 = KEYb) (r2 : c.nreg 7162 = VALb)
    (r3 : c.nreg 7163 = Tb) (hkey : ∀ j < m, c.nmem (KEYb + j) < nk)
    (d1 : KEYb + m ≤ Tb ∨ Tb + nk ≤ KEYb) (d2 : VALb + m ≤ Tb ∨ Tb + nk ≤ VALb)
    (w1 : KEYb + m ≤ W) (w2 : VALb + m ≤ W) (w3 : Tb + nk ≤ W) (w4 : m + 1 ≤ W) :
    ∃ c' t, Exec P W svProg c c' t ∧ t ≤ 9 * m + 4 ∧
      (∀ x < nk, c'.nmem (Tb + x) = svF (fun j => c.nmem (KEYb + j))
        (fun j => c.nmem (VALb + j)) m x (c.nmem (Tb + x))) ∧
      (∀ a, ¬ (Tb ≤ a ∧ a < Tb + nk) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 7164 ∨ 7167 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold svProg
  obtain ⟨c₁, k₁, e₁, hk₁, g4, g5, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 7164 1, .constN 7165 0]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 7164 = 1 ∧ c₁.nreg 7165 = 0 ∧
      (∀ x, x ≠ 7164 → x ≠ 7165 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; done)
    · config_simp; simp (disch := omega) only [upd_other]
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 7164 → x ≠ 7165 → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 7165 ∨ 7167 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ x < nk, c'.nmem (Tb + x) = svF (fun j => m₀ (KEYb + j)) (fun j => m₀ (VALb + j)) i x
      (m₀ (Tb + x))) ∧
    (∀ a, ¬ (Tb ≤ a ∧ a < Tb + nk) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h65, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P)
    (a := 7165) (b := 7160) (body := svBody) J (B := 7) c₁ hw₁ g5
    (by rw [q _ (by omega) (by omega), r0]) (Nat.zero_le m)
    ⟨fun _ _ => rfl, fun x hx => by rw [gm₁]; rfl, fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h65 h60 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 7165 ∨ 7167 < x) → c'.nreg x = c₁.nreg x := j1
      have eK : c'.nmem (KEYb + i) = m₀ (KEYb + i) := j3 _ (by omega)
      have eV : c'.nmem (VALb + i) = m₀ (VALb + i) := j3 _ (by omega)
      have hk := hkey i hhi
      obtain ⟨c'', t, ex, ht, h65', hm', hn', hr', hrm', ho'⟩ :=
        svBody_exec (P := P) c' hw (KEYb := KEYb) (VALb := VALb) (Tb := Tb) (j := i)
          (by rw [f _ (by omega), q _ (by omega) (by omega), r1])
          (by rw [f _ (by omega), q _ (by omega) (by omega), r2])
          (by rw [f _ (by omega), q _ (by omega) (by omega), r3])
          (by rw [f _ (by omega), g4]) h65 (by omega) (by omega) (by rw [eK]; omega) (by omega)
      rw [eK, eV] at hm'
      refine ⟨c'', t, ex, ht.le, h65', by rw [hn' _ (by omega)]; exact h60,
        fun x hx => by rw [hn' x hx, f x hx], fun x hx => ?_, fun a ha => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm']
        by_cases hx' : m₀ (KEYb + i) = x
        · subst hx'
          rw [upd_same]; simp [svF]
        · rw [upd_other _ _ _ (by omega), j2 x hx]
          simp [svF, hx']
      · rw [hm', upd_other _ _ _ (by omega)]; exact j3 a ha)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3,
    fun x hx => by rw [j1 x (by omega), q x (by omega) (by omega)], by rw [j4, gr₁],
    by rw [j5, grm₁], by rw [j6, go₁]⟩

theorem vbIO_exec (c : Config) (hc : WordsBounded W c) {i : ℕ} (r20 : c.nreg 6520 = i) :
    ∃ c' k, Exec P W vbIO c c' k ∧ k ≤ 1 ∧ c'.nreg 6523 = i ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold vbIO
  exec_block
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r20]
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

theorem vbLS_exec (c : Config) (hc : WordsBounded W c) {i IDb LTb x y : ℕ}
    (r20 : c.nreg 6520 = i) (r50 : c.nreg 7150 = IDb) (r70 : c.nreg 7170 = LTb)
    (hx : c.nmem (IDb + i) = x) (hy : c.nmem (LTb + x) = y) (w1 : IDb + i ≤ W)
    (w2 : LTb + x ≤ W) :
    ∃ c' k, Exec P W vbLS c c' k ∧ k ≤ 4 ∧ c'.nreg 6523 = y ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold vbLS
  exec_block
  all_goals try (config_simp; (try simp only [r20, r50, r70, hx, hy]); omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r20, r50, r70, hx, hy]
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

theorem vbIM_exec (c : Config) (hc : WordsBounded W c) {i LSb a : ℕ}
    (r20 : c.nreg 6520 = i) (r71 : c.nreg 7171 = LSb) (r21 : c.nreg 6521 = 1)
    (ha : c.nmem (LSb + i) = a) (w1 : LSb + i ≤ W) :
    ∃ c' k, Exec P W vbIM c c' k ∧ k ≤ 7 ∧ c'.nreg 6523 = pdEq a i ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have ba : a ≤ W := ha ▸ hc.2 _
  have bi : i ≤ W := r20 ▸ hc.1 _
  unfold vbIM
  exec_block
  all_goals try (config_simp; (try simp only [r20, r71, r21, ha]); omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r20, r71, r21, ha, pdEq]
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

theorem vbP1_exec (c : Config) (hc : WordsBounded W c) {i LSb CIb a v : ℕ}
    (r20 : c.nreg 6520 = i) (r71 : c.nreg 7171 = LSb) (r73 : c.nreg 7173 = CIb)
    (r21 : c.nreg 6521 = 1) (ha : c.nmem (LSb + i) = a) (hv : c.nmem (CIb + a) = v)
    (w1 : LSb + i ≤ W) (w2 : CIb + a ≤ W) (w3 : v + 1 ≤ W) :
    ∃ c' k, Exec P W vbP1 c c' k ∧ k ≤ 5 ∧ c'.nreg 6523 = v + 1 ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold vbP1
  exec_block
  all_goals try (config_simp; (try simp only [r20, r71, r73, r21, ha, hv]); omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r20, r71, r73, r21, ha, hv]
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

theorem vbKO_exec (c : Config) (hc : WordsBounded W c) {j OWb o : ℕ}
    (r20 : c.nreg 6520 = j) (r76 : c.nreg 7176 = OWb + 1) (ho : c.nmem (OWb + 1 + j) = o)
    (w1 : OWb + 1 + j ≤ W) :
    ∃ c' k, Exec P W vbKO c c' k ∧ k ≤ 2 ∧ c'.nreg 6523 = o ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold vbKO
  exec_block
  all_goals try (config_simp; (try simp only [r20, r76, ho]); omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r20, r76, ho]
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

theorem vbVH_exec (c : Config) (hc : WordsBounded W c) {j OWb HTb K o t : ℕ}
    (r20 : c.nreg 6520 = j) (r76 : c.nreg 7176 = OWb + 1) (r77 : c.nreg 7177 = HTb + 1)
    (r43 : c.nreg 7143 = K) (r21 : c.nreg 6521 = 1)
    (ho : c.nmem (OWb + 1 + j) = o) (ht : c.nmem (HTb + 1 + j) = t) (ht1 : t ≤ 1)
    (w1 : OWb + 1 + j ≤ W) (w2 : HTb + 1 + j ≤ W) :
    ∃ c' k, Exec P W vbVH c c' k ∧ k ≤ 8 ∧ c'.nreg 6523 = vhV K t o ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have bK : K ≤ W := r43 ▸ hc.1 _
  have hd := dself_le o
  have m1 : o / o * (1 - t) ≤ 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd with h | h <;> rw [h] <;> omega
  have m2 : o / o * (1 - t) * K ≤ W := fmul_le m1 bK
  unfold vbVH
  exec_block
  all_goals try (config_simp; (try simp only [r20, r76, r77, r43, r21, ho, ht]); omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r20, r76, r77, r43, r21, ho, ht, vhV]
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

theorem vbWT_exec (c : Config) (hc : WordsBounded W c) {q W1b W2b a b : ℕ}
    (r20 : c.nreg 6520 = q) (r78 : c.nreg 7178 = W1b + 1) (r79 : c.nreg 7179 = W2b + 1)
    (ha : c.nmem (W1b + 1 + q) = a) (hb : c.nmem (W2b + 1 + q) = b)
    (w1 : W1b + 1 + q ≤ W) (w2 : W2b + 1 + q ≤ W) (w3 : a + b ≤ W) :
    ∃ c' k, Exec P W vbWT c c' k ∧ k ≤ 5 ∧ c'.nreg 6523 = a + b ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold vbWT
  exec_block
  all_goals try (config_simp; (try simp only [r20, r78, r79, ha, hb]); omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r20, r78, r79, ha, hb]
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

theorem vbLF_exec (c : Config) (hc : WordsBounded W c) {i P1b hv r7 mx p : ℕ}
    (r20 : c.nreg 6520 = i) (r80 : c.nreg 7180 = P1b) (r81 : c.nreg 7181 = hv)
    (r82 : c.nreg 7182 = r7) (r83 : c.nreg 7183 = mx) (r21 : c.nreg 6521 = 1)
    (hp : c.nmem (P1b + i) = p) (hhv : hv ≤ 1) (w1 : P1b + i ≤ W) :
    ∃ c' k, Exec P W vbLF c c' k ∧ k ≤ 14 ∧ c'.nreg 6523 = lfV hv r7 mx p ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have bp : p ≤ W := hp ▸ hc.2 _
  have b7 : r7 ≤ W := r82 ▸ hc.1 _
  have bm : mx ≤ W := r83 ▸ hc.1 _
  have hd1 := dself_le ((p - 1 - r7) + (r7 - (p - 1)))
  have hd2 := dself_le (mx - (p - 1))
  have hs1 : 1 - ((p - 1 - r7) + (r7 - (p - 1))) / ((p - 1 - r7) + (r7 - (p - 1))) ≤ 1 :=
    Nat.sub_le _ _
  have m1 : hv * (1 - ((p - 1 - r7) + (r7 - (p - 1))) / ((p - 1 - r7) + (r7 - (p - 1)))) ≤ 1 :=
    by rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hhv with h | h <;> rw [h] <;> omega
  have m2 : (1 - hv) * ((mx - (p - 1)) / (mx - (p - 1))) ≤ 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hhv with h | h <;> rw [h] <;> omega
  have m3 : hv * (1 - ((p - 1 - r7) + (r7 - (p - 1))) / ((p - 1 - r7) + (r7 - (p - 1)))) +
      (1 - hv) * ((mx - (p - 1)) / (mx - (p - 1))) ≤ 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hhv with h | h <;> rw [h] <;> simp <;> omega
  have bW : 1 ≤ W := by have := hc.1 6521; rw [r21] at this; exact this
  unfold vbLF
  exec_block
  all_goals try (config_simp; (try simp only [r20, r80, r81, r82, r83, r21, hp]); omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r20, r80, r81, r82, r83, r21, hp, lfV]
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
