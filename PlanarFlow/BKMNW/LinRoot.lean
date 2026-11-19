module

public import PlanarFlow.BKMNW.LinFlow

/-!
# Writing the root frame of the max-flow driver from index arrays, on the machine

The driver (`PlanarFlow/BKMNW/MfDrvFrame.lean`) starts from the root frame at `d = Hb + 5`
(layout `PlanarFlow/BKMNW/MfFrame.lean`: header `m | 0 | tg | Z`, then `GID | RV | SG | CP | KR |
HL | FL`) and the driver's registers `3000 = 0`, `3001 = 1`, `3002 = Hb`, `3003 = eF` and cells
`Hb ↦ 0`, `Hb + 1 ↦ 0`, `Hb + 2 ↦ eF` (`eF = d + 4 + 7 m`). `rfProg` writes all of it from four
index arrays of length `m` below `Hb` (`REV`, `SIG`, `CAP`, `KR`) and the registers
`6700 = m`, `6701 = REVb`, `6702 = SIGb`, `6703 = CAPb`, `6704 = KRb`, `6705 = tg`, `6706 = Z`,
`6707 = Hb`; the global numbering of the root is the index (`GID[i] = i`) and there are no holes
(`HL[i] = 0`).

* `lidProg` (identity fill `OUT[i] := i`; registers `6730 = m`, `6731 = OUTb`; scratch
  `6732 … 6734`), `lidProg_exec` (`5 m + 4`).
* `rfA` (header and bases), `rfFront`, `rfMid` (four gathers `lgProg` through `GID`),
  `rfBack` (the fill of `HL` and the driver's cells), **`rfProg_exec`** (`46 m + 80` steps).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace PlanarFlow

namespace BKMNW

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

section Exec

variable {P : Input} {W : ℕ}

/-! ### The identity fill -/

/-- `OUT[i] := i`. -/
def lidBody : Stmt := block [.addN 6733 6731 6734, .storeN 6733 6734, .addN 6734 6734 6732]

/-- **The identity fill** `OUT[i] := i`, `i < m`. -/
def lidProg : Stmt :=
  .seq (block [.constN 6732 1, .constN 6734 0]) (.whileLtN 6734 6730 lidBody)

theorem lidBody_exec (c : Config) (hc : WordsBounded W c) {OUTb j : ℕ}
    (r1 : c.nreg 6731 = OUTb) (r2 : c.nreg 6732 = 1) (r4 : c.nreg 6734 = j)
    (w1 : OUTb + j ≤ W) (w4 : j + 1 ≤ W) :
    ∃ c' k, Exec P W lidBody c c' k ∧ k = 3 ∧ c'.nreg 6734 = j + 1 ∧
      c'.nmem = upd c.nmem (OUTb + j) j ∧
      (∀ x, (x < 6733 ∨ 6734 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lidBody
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r4]; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r2, r4]
  · config_simp; simp only [r1, r4]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **The identity fill**: within `5 m + 4` steps `OUT[i] = i` for `i < m`; memory outside
`[OUTb, OUTb + m)`, registers outside `6732 … 6734`, reals and output kept. -/
theorem lidProg_exec (c : Config) (hc : WordsBounded W c) {m OUTb : ℕ}
    (r0 : c.nreg 6730 = m) (r1 : c.nreg 6731 = OUTb) (w1 : OUTb + m ≤ W) (w4 : m + 1 ≤ W) :
    ∃ c' k, Exec P W lidProg c c' k ∧ k ≤ 5 * m + 4 ∧
      (∀ j < m, c'.nmem (OUTb + j) = j) ∧
      (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6732 ∨ 6734 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lidProg
  obtain ⟨c₁, k₁, e₁, hk₁, g2, g4, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 6732 1, .constN 6734 0]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 6732 = 1 ∧ c₁.nreg 6734 = 0 ∧
      (∀ x, x ≠ 6732 → x ≠ 6734 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 6732 → x ≠ 6734 → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 6733 ∨ 6734 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ j < i, c'.nmem (OUTb + j) = j) ∧
    (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + i) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h74, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 6734)
    (b := 6730) (body := lidBody) J (B := 3) c₁ hw₁ g4 (by rw [q _ (by omega) (by omega), r0])
    (Nat.zero_le m) ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega),
      fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h74 h70 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 6733 ∨ 6734 < x) → c'.nreg x = c₁.nreg x := j1
      obtain ⟨c'', t, ex, ht, h74', hm', hn', hr', hrm', ho'⟩ := lidBody_exec (P := P) c' hw
        (by rw [f _ (by omega), q _ (by omega) (by omega), r1])
        (by rw [f _ (by omega), g2]) h74 (by omega) (by omega)
      refine ⟨c'', t, ex, ht.le, h74', by rw [hn' _ (by omega)]; exact h70,
        fun x hx => by rw [hn' x hx, f x hx], fun j hj => ?_, fun a ha => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j2 j hj
        · rw [upd_same]
      · rw [hm', upd_other _ _ _ (fun h => ha ⟨by omega, by omega⟩)]
        exact j3 a (fun h => ha ⟨h.1, by omega⟩))
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3, fun x hx => ?_, by rw [j4, gr₁],
    by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x (by omega), q x (by omega) (by omega)]

/-! ### The root frame -/

/-- The header of the root frame and the bases of its arrays. -/
def rfA : Stmt := block [.constN 6710 5, .addN 6711 6707 6710, .storeN 6711 6700,
  .constN 6710 1, .constN 6713 0, .addN 6712 6711 6710, .storeN 6712 6713,
  .addN 6712 6712 6710, .storeN 6712 6705, .addN 6712 6712 6710, .storeN 6712 6706,
  .addN 6714 6712 6710, .addN 6715 6714 6700, .addN 6716 6715 6700, .addN 6717 6716 6700,
  .addN 6718 6717 6700, .addN 6719 6718 6700, .addN 6720 6719 6700, .addN 6721 6720 6700]

/-- The registers of the identity fill of `GID`. -/
def rfLi : Stmt := block [.copyN 6730 6700, .copyN 6731 6714]

/-- The header, the bases and `GID`. -/
def rfFront : Stmt := .seq rfA (.seq rfLi lidProg)

/-- The registers of the gather of `REV` into `RV`. -/
def rfG1 : Stmt := block [.copyN 6210 6700, .copyN 6211 6714, .copyN 6212 6701, .copyN 6213 6715]
/-- The registers of the gather of `SIG` into `SG`. -/
def rfG2 : Stmt := block [.copyN 6212 6702, .copyN 6213 6716]
/-- The registers of the gather of `CAP` into `CP`. -/
def rfG3 : Stmt := block [.copyN 6212 6703, .copyN 6213 6717]
/-- The registers of the gather of `KR` into the frame's `KR`. -/
def rfG4 : Stmt := block [.copyN 6212 6704, .copyN 6213 6718]

/-- The gathers of `REV` and `SIG`. -/
def rfMidA : Stmt := .seq (.seq rfG1 lgProg) (.seq rfG2 lgProg)

/-- The gathers of `CAP` and `KR`. -/
def rfMidB : Stmt := .seq (.seq rfG3 lgProg) (.seq rfG4 lgProg)

/-- The four gathers through `GID` (the identity). -/
def rfMid : Stmt := .seq rfMidA rfMidB

/-- The registers of the fill of `HL` with `0`. -/
def rfZ : Stmt := block [.copyN 6260 6700, .copyN 6261 6719, .copyN 6262 6713]

/-- The cells and the registers of the driver. -/
def rfD : Stmt := block [.storeN 6707 6713, .constN 6710 1, .addN 6742 6707 6710,
  .storeN 6742 6713, .addN 6742 6742 6710, .storeN 6742 6721, .constN 3000 0, .constN 3001 1,
  .copyN 3002 6707, .copyN 3003 6721]

/-- The fill of `HL` and the driver's cells. -/
def rfBack : Stmt := .seq rfZ (.seq lzProg rfD)

/-- **The root frame from index arrays.** -/
def rfProg : Stmt := .seq rfFront (.seq rfMid rfBack)

theorem rfA_exec (c : Config) (hc : WordsBounded W c) {m tg Z Hb : ℕ}
    (r0 : c.nreg 6700 = m) (r5 : c.nreg 6705 = tg) (r6 : c.nreg 6706 = Z)
    (r7 : c.nreg 6707 = Hb) (w : Hb + 9 + 7 * m ≤ W) :
    ∃ c' t, Exec P W rfA c c' t ∧ t = 19 ∧ c'.nreg 6713 = 0 ∧ c'.nreg 6714 = Hb + 9 ∧
      c'.nreg 6715 = Hb + 9 + m ∧ c'.nreg 6716 = Hb + 9 + 2 * m ∧
      c'.nreg 6717 = Hb + 9 + 3 * m ∧ c'.nreg 6718 = Hb + 9 + 4 * m ∧
      c'.nreg 6719 = Hb + 9 + 5 * m ∧ c'.nreg 6721 = Hb + 9 + 7 * m ∧
      c'.nmem (Hb + 5) = m ∧ c'.nmem (Hb + 6) = 0 ∧ c'.nmem (Hb + 7) = tg ∧
      c'.nmem (Hb + 8) = Z ∧
      (∀ a, (a < Hb + 5 ∨ Hb + 8 < a) → c'.nmem a = c.nmem a) ∧
      (∀ x, x < 6710 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rfA
  exec_block
  all_goals try omega
  all_goals
    try (config_simp; simp (disch := omega) only [upd_other, upd_same, r0, r5, r6, r7] <;> omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, fun x hx => ?_,
    rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r0, r5, r6, r7])
    try omega

theorem rfFront_exec (c : Config) (hc : WordsBounded W c) {m tg Z Hb : ℕ}
    (r0 : c.nreg 6700 = m) (r5 : c.nreg 6705 = tg) (r6 : c.nreg 6706 = Z)
    (r7 : c.nreg 6707 = Hb) (w : Hb + 9 + 7 * m ≤ W) :
    ∃ c' t, Exec P W rfFront c c' t ∧ t ≤ 5 * m + 25 ∧ c'.nreg 6713 = 0 ∧
      c'.nreg 6714 = Hb + 9 ∧
      c'.nreg 6715 = Hb + 9 + m ∧ c'.nreg 6716 = Hb + 9 + 2 * m ∧
      c'.nreg 6717 = Hb + 9 + 3 * m ∧ c'.nreg 6718 = Hb + 9 + 4 * m ∧
      c'.nreg 6719 = Hb + 9 + 5 * m ∧ c'.nreg 6721 = Hb + 9 + 7 * m ∧
      c'.nmem (Hb + 5) = m ∧ c'.nmem (Hb + 6) = 0 ∧ c'.nmem (Hb + 7) = tg ∧
      c'.nmem (Hb + 8) = Z ∧ (∀ j < m, c'.nmem (Hb + 9 + j) = j) ∧
      (∀ a, (a < Hb + 5 ∨ Hb + 9 + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, x < 6710 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rfFront
  obtain ⟨c₁, k₁, e₁, hk₁, a13, a14, a15, a16, a17, a18, a19, a21, m5, m6, m7, m8, mk₁, rk₁,
    gr₁, grm₁, go₁⟩ := rfA_exec (P := P) c hc r0 r5 r6 r7 w
  obtain ⟨c₂, k₂, e₂, hk₂, s0, s1, gn₂, gm₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
      Exec P W rfLi c₁ c₂ k₂ ∧ k₂ = 2 ∧ c₂.nreg 6730 = m ∧ c₂.nreg 6731 = Hb + 9 ∧
      (∀ x, x ≠ 6730 → x ≠ 6731 → c₂.nreg x = c₁.nreg x) ∧
      c₂.nmem = c₁.nmem ∧ c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    have hw₁ := e₁.wb_right
    have b0 : c₁.nreg 6700 = m := by rw [rk₁ _ (by omega), r0]
    unfold rfLi
    exec_block
    refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [b0, a14])
    simp only [upd_apply]; split_ifs <;> omega
  obtain ⟨c₃, k₃, e₃, hk₃, l1, l2, l3, l4, l5, l6⟩ := lidProg_exec (P := P) c₂ e₂.wb_right s0 s1
    (by omega) (by omega)
  have q : ∀ x, (x < 6730 ∨ 6734 < x) → c₃.nreg x = c₁.nreg x := fun x hx => by
    rw [l3 x (by omega), gn₂ x (by omega) (by omega)]
  have mm : ∀ a, (a < Hb + 9 ∨ Hb + 9 + m ≤ a) → c₃.nmem a = c₁.nmem a := fun a ha => by
    rw [l2 a (by omega), gm₂]
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, by rw [q _ (by omega), a13],
    by rw [q _ (by omega), a14], by rw [q _ (by omega), a15], by rw [q _ (by omega), a16],
    by rw [q _ (by omega), a17], by rw [q _ (by omega), a18], by rw [q _ (by omega), a19],
    by rw [q _ (by omega), a21], by rw [mm _ (by omega), m5], by rw [mm _ (by omega), m6],
    by rw [mm _ (by omega), m7], by rw [mm _ (by omega), m8], l1, fun a ha => ?_,
    fun x hx => by rw [q _ (by omega), rk₁ x hx], by rw [l4, gr₂, gr₁],
    by rw [l5, grm₂, grm₁], by rw [l6, go₂, go₁]⟩
  rw [mm a (by omega), mk₁ a (by omega)]

/-- Running a gather of an input array `A` (below `lo`) through the identity array `GID`. -/
theorem rfGather (c : Config) (hc : WordsBounded W c) {m GIDb Ab OUTb : ℕ}
    (r0 : c.nreg 6210 = m) (r1 : c.nreg 6211 = GIDb) (r2 : c.nreg 6212 = Ab)
    (r3 : c.nreg 6213 = OUTb) (hid : ∀ j < m, c.nmem (GIDb + j) = j)
    (l1 : Ab + m ≤ OUTb) (l2 : GIDb + m ≤ OUTb) (l3 : OUTb + m ≤ W) (l4 : m + 1 ≤ W) :
    ∃ c' k, Exec P W lgProg c c' k ∧ k ≤ 9 * m + 4 ∧
      (∀ j < m, c'.nmem (OUTb + j) = c.nmem (Ab + j)) ∧
      (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6214 ∨ 6217 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', k, ex, hk, h1, h2, h3, h4, h5, h6⟩ := lgProg_exec (P := P) c hc r0 r1 r2 r3
    (by omega) (by omega) (by omega) (fun j hj => by rw [hid j hj]; omega)
    (fun j hj => by omega) (fun j hj => by rw [hid j hj]; omega)
  exact ⟨c', k, ex, hk, fun j hj => by rw [h1 j hj, hid j hj], h2, h3, h4, h5, h6⟩


theorem rfG1_exec (c : Config) (hc : WordsBounded W c) {m Hb A : ℕ}
    (r0 : c.nreg 6700 = m) (r1 : c.nreg 6701 = A) (r14 : c.nreg 6714 = Hb + 9)
    (r15 : c.nreg 6715 = Hb + 9 + m) :
    ∃ c₁ k₁, Exec P W rfG1 c c₁ k₁ ∧ k₁ = 4 ∧ c₁.nreg 6210 = m ∧ c₁.nreg 6211 = Hb + 9 ∧
      c₁.nreg 6212 = A ∧ c₁.nreg 6213 = Hb + 9 + m ∧
      (∀ x, (x < 6210 ∨ 6213 < x) → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
  unfold rfG1
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r0, r1, r14, r15])
  simp only [upd_apply]; split_ifs <;> omega

theorem rfG2_exec (c : Config) (hc : WordsBounded W c) {A B : ℕ}
    (r1 : c.nreg 6702 = A) (r2 : c.nreg 6716 = B) :
    ∃ c₁ k₁, Exec P W rfG2 c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 6212 = A ∧ c₁.nreg 6213 = B ∧
      (∀ x, (x < 6212 ∨ 6213 < x) → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
  unfold rfG2
  exec_block
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r1, r2])
  simp only [upd_apply]; split_ifs <;> omega

theorem rfG3_exec (c : Config) (hc : WordsBounded W c) {A B : ℕ}
    (r1 : c.nreg 6703 = A) (r2 : c.nreg 6717 = B) :
    ∃ c₁ k₁, Exec P W rfG3 c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 6212 = A ∧ c₁.nreg 6213 = B ∧
      (∀ x, (x < 6212 ∨ 6213 < x) → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
  unfold rfG3
  exec_block
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r1, r2])
  simp only [upd_apply]; split_ifs <;> omega

theorem rfG4_exec (c : Config) (hc : WordsBounded W c) {A B : ℕ}
    (r1 : c.nreg 6704 = A) (r2 : c.nreg 6718 = B) :
    ∃ c₁ k₁, Exec P W rfG4 c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 6212 = A ∧ c₁.nreg 6213 = B ∧
      (∀ x, (x < 6212 ∨ 6213 < x) → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
  unfold rfG4
  exec_block
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r1, r2])
  simp only [upd_apply]; split_ifs <;> omega

/-- One later gather stage: the copy block (`rfG2`, `rfG3` or `rfG4`, given by its result), then
the gather. -/
theorem rfStage (c₀ c : Config) {s : Stmt} {k₁ m Hb A OUTb : ℕ} (e₁ : Exec P W s c₀ c k₁)
    (r0 : c.nreg 6210 = m) (r1 : c.nreg 6211 = Hb + 9) (r2 : c.nreg 6212 = A)
    (r3 : c.nreg 6213 = OUTb) (hid : ∀ j < m, c.nmem (Hb + 9 + j) = j)
    (l1 : A + m ≤ OUTb) (l2 : Hb + 9 + m ≤ OUTb) (l3 : OUTb + m ≤ W) :
    ∃ c' k, Exec P W (.seq s lgProg) c₀ c' (k₁ + k) ∧ k ≤ 9 * m + 4 ∧
      (∀ j < m, c'.nmem (OUTb + j) = c.nmem (A + j)) ∧
      (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6214 ∨ 6217 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', k, ex, hk, h1, h2, h3, h4, h5, h6⟩ := rfGather (P := P) c e₁.wb_right r0 r1 r2 r3
    hid l1 l2 l3 (by omega)
  exact ⟨c', k, .seq e₁ ex, hk, h1, h2, h3, h4, h5, h6⟩


theorem rfMidA_exec (c : Config) (hc : WordsBounded W c) {m Hb REVb SIGb : ℕ}
    (r0 : c.nreg 6700 = m) (r1 : c.nreg 6701 = REVb) (r2 : c.nreg 6702 = SIGb)
    (r14 : c.nreg 6714 = Hb + 9) (r15 : c.nreg 6715 = Hb + 9 + m)
    (r16 : c.nreg 6716 = Hb + 9 + 2 * m)
    (hid : ∀ j < m, c.nmem (Hb + 9 + j) = j) (i1 : REVb + m ≤ Hb) (i2 : SIGb + m ≤ Hb)
    (w : Hb + 9 + 7 * m ≤ W) :
    ∃ c' t, Exec P W rfMidA c c' t ∧ t ≤ 18 * m + 14 ∧ c'.nreg 6210 = m ∧
      c'.nreg 6211 = Hb + 9 ∧
      (∀ j < m, c'.nmem (Hb + 9 + m + j) = c.nmem (REVb + j)) ∧
      (∀ j < m, c'.nmem (Hb + 9 + 2 * m + j) = c.nmem (SIGb + j)) ∧
      (∀ a, (a < Hb + 9 + m ∨ Hb + 9 + 3 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6210 ∨ 6217 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rfMidA
  obtain ⟨c₁, k₁, e₁, hk₁, s0, s1, s2, s3, gn₁, gm₁, gr₁, grm₁, go₁⟩ :=
    rfG1_exec (P := P) (m := m) (Hb := Hb) (A := REVb) c hc r0 r1 r14 r15
  obtain ⟨c₂, k₂, e₂, hk₂, v2, m2, n2, rr2, rm2, o2⟩ :=
    rfStage (P := P) (m := m) (Hb := Hb) (A := REVb) (OUTb := Hb + 9 + m) c c₁ e₁ s0 s1 s2 s3
    (fun j hj => by rw [gm₁]; exact hid j hj) (by omega) (by omega) (by omega)
  have q2 : ∀ x, (x < 6210 ∨ 6217 < x) → c₂.nreg x = c.nreg x := fun x hx => by
    rw [n2 x (by omega), gn₁ x (by omega)]
  have k2 : ∀ a, (a < Hb + 9 + m ∨ Hb + 9 + 2 * m ≤ a) → c₂.nmem a = c.nmem a := fun a ha => by
    rw [m2 a (by omega), gm₁]
  clear e₁
  obtain ⟨c₃, k₃, e₃, hk₃, t2, t3, gn₃, gm₃, gr₃, grm₃, go₃⟩ :=
    rfG2_exec (P := P) (A := SIGb) (B := Hb + 9 + 2 * m) c₂ e₂.wb_right
    (by rw [q2 _ (by omega), r2]) (by rw [q2 _ (by omega), r16])
  have u0 : c₃.nreg 6210 = m := by rw [gn₃ _ (by omega), n2 _ (by omega), s0]
  have u1 : c₃.nreg 6211 = Hb + 9 := by rw [gn₃ _ (by omega), n2 _ (by omega), s1]
  obtain ⟨c₄, k₄, e₄, hk₄, v4, m4, n4, rr4, rm4, o4⟩ :=
    rfStage (P := P) (m := m) (Hb := Hb) (A := SIGb) (OUTb := Hb + 9 + 2 * m) c₂ c₃ e₃ u0 u1
    t2 t3 (fun j hj => by rw [gm₃, k2 _ (Or.inl (by omega))]; exact hid j hj) (by omega)
    (by omega) (by omega)
  refine ⟨c₄, (k₁ + k₂) + (k₃ + k₄), .seq e₂ e₄, by omega,
    by rw [n4 _ (by omega), u0], by rw [n4 _ (by omega), u1], fun j hj => ?_, fun j hj => ?_,
    fun a ha => ?_, fun x hx => ?_, by rw [rr4, gr₃, rr2, gr₁], by rw [rm4, grm₃, rm2, grm₁],
    by rw [o4, go₃, o2, go₁]⟩
  · rw [m4 (Hb + 9 + m + j) (by omega), gm₃, v2 j hj, gm₁]
  · rw [v4 j hj, gm₃, k2 (SIGb + j) (Or.inl (by omega))]
  · rw [m4 a (by omega), gm₃, k2 a (ha.imp_right (le_trans (by omega)))]
  · rw [n4 x (by omega), gn₃ x (by omega), q2 x hx]

theorem rfMidB_exec (c : Config) (hc : WordsBounded W c) {m Hb CAPb KRb : ℕ}
    (r0 : c.nreg 6210 = m) (r1 : c.nreg 6211 = Hb + 9) (r3 : c.nreg 6703 = CAPb)
    (r4 : c.nreg 6704 = KRb) (r17 : c.nreg 6717 = Hb + 9 + 3 * m)
    (r18 : c.nreg 6718 = Hb + 9 + 4 * m)
    (hid : ∀ j < m, c.nmem (Hb + 9 + j) = j) (i3 : CAPb + m ≤ Hb) (i4 : KRb + m ≤ Hb)
    (w : Hb + 9 + 7 * m ≤ W) :
    ∃ c' t, Exec P W rfMidB c c' t ∧ t ≤ 18 * m + 12 ∧
      (∀ j < m, c'.nmem (Hb + 9 + 3 * m + j) = c.nmem (CAPb + j)) ∧
      (∀ j < m, c'.nmem (Hb + 9 + 4 * m + j) = c.nmem (KRb + j)) ∧
      (∀ a, (a < Hb + 9 + 3 * m ∨ Hb + 9 + 5 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6210 ∨ 6217 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rfMidB
  obtain ⟨c₁, k₁, e₁, hk₁, s2, s3, gn₁, gm₁, gr₁, grm₁, go₁⟩ :=
    rfG3_exec (P := P) (A := CAPb) (B := Hb + 9 + 3 * m) c hc r3 r17
  have s0 : c₁.nreg 6210 = m := by rw [gn₁ _ (by omega), r0]
  have s1 : c₁.nreg 6211 = Hb + 9 := by rw [gn₁ _ (by omega), r1]
  obtain ⟨c₂, k₂, e₂, hk₂, v2, m2, n2, rr2, rm2, o2⟩ :=
    rfStage (P := P) (m := m) (Hb := Hb) (A := CAPb) (OUTb := Hb + 9 + 3 * m) c c₁ e₁ s0 s1
    s2 s3 (fun j hj => by rw [gm₁]; exact hid j hj) (by omega) (by omega) (by omega)
  have q2 : ∀ x, (x < 6210 ∨ 6217 < x) → c₂.nreg x = c.nreg x := fun x hx => by
    rw [n2 x (by omega), gn₁ x (by omega)]
  have k2 : ∀ a, (a < Hb + 9 + 3 * m ∨ Hb + 9 + 4 * m ≤ a) → c₂.nmem a = c.nmem a :=
    fun a ha => by rw [m2 a (by omega), gm₁]
  clear e₁
  obtain ⟨c₃, k₃, e₃, hk₃, t2, t3, gn₃, gm₃, gr₃, grm₃, go₃⟩ :=
    rfG4_exec (P := P) (A := KRb) (B := Hb + 9 + 4 * m) c₂ e₂.wb_right
    (by rw [q2 _ (by omega), r4]) (by rw [q2 _ (by omega), r18])
  have u0 : c₃.nreg 6210 = m := by rw [gn₃ _ (by omega), n2 _ (by omega), s0]
  have u1 : c₃.nreg 6211 = Hb + 9 := by rw [gn₃ _ (by omega), n2 _ (by omega), s1]
  obtain ⟨c₄, k₄, e₄, hk₄, v4, m4, n4, rr4, rm4, o4⟩ :=
    rfStage (P := P) (m := m) (Hb := Hb) (A := KRb) (OUTb := Hb + 9 + 4 * m) c₂ c₃ e₃ u0 u1
    t2 t3 (fun j hj => by rw [gm₃, k2 _ (Or.inl (by omega))]; exact hid j hj) (by omega)
    (by omega) (by omega)
  refine ⟨c₄, (k₁ + k₂) + (k₃ + k₄), .seq e₂ e₄, by omega, fun j hj => ?_, fun j hj => ?_,
    fun a ha => ?_, fun x hx => ?_, by rw [rr4, gr₃, rr2, gr₁], by rw [rm4, grm₃, rm2, grm₁],
    by rw [o4, go₃, o2, go₁]⟩
  · rw [m4 (Hb + 9 + 3 * m + j) (by omega), gm₃, v2 j hj, gm₁]
  · rw [v4 j hj, gm₃, k2 (KRb + j) (Or.inl (by omega))]
  · rw [m4 a (by omega), gm₃, k2 a (ha.imp_right (le_trans (by omega)))]
  · rw [n4 x (by omega), gn₃ x (by omega), q2 x hx]

theorem rfMid_exec (c : Config) (hc : WordsBounded W c) {m Hb REVb SIGb CAPb KRb : ℕ}
    (r0 : c.nreg 6700 = m) (r1 : c.nreg 6701 = REVb) (r2 : c.nreg 6702 = SIGb)
    (r3 : c.nreg 6703 = CAPb) (r4 : c.nreg 6704 = KRb) (r14 : c.nreg 6714 = Hb + 9)
    (r15 : c.nreg 6715 = Hb + 9 + m) (r16 : c.nreg 6716 = Hb + 9 + 2 * m)
    (r17 : c.nreg 6717 = Hb + 9 + 3 * m) (r18 : c.nreg 6718 = Hb + 9 + 4 * m)
    (hid : ∀ j < m, c.nmem (Hb + 9 + j) = j) (i1 : REVb + m ≤ Hb) (i2 : SIGb + m ≤ Hb)
    (i3 : CAPb + m ≤ Hb) (i4 : KRb + m ≤ Hb) (w : Hb + 9 + 7 * m ≤ W) :
    ∃ c' t, Exec P W rfMid c c' t ∧ t ≤ 36 * m + 26 ∧
      (∀ j < m, c'.nmem (Hb + 9 + m + j) = c.nmem (REVb + j)) ∧
      (∀ j < m, c'.nmem (Hb + 9 + 2 * m + j) = c.nmem (SIGb + j)) ∧
      (∀ j < m, c'.nmem (Hb + 9 + 3 * m + j) = c.nmem (CAPb + j)) ∧
      (∀ j < m, c'.nmem (Hb + 9 + 4 * m + j) = c.nmem (KRb + j)) ∧
      (∀ a, (a < Hb + 9 + m ∨ Hb + 9 + 5 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6210 ∨ 6217 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rfMid
  obtain ⟨c₁, k₁, e₁, hk₁, a0, a1, va, vb, ka, na, ra, rma, oa⟩ :=
    rfMidA_exec (P := P) c hc r0 r1 r2 r14 r15 r16 hid i1 i2 w
  obtain ⟨c₂, k₂, e₂, hk₂, vc, vd, kb, nb, rb, rmb, ob⟩ := rfMidB_exec (P := P) c₁ e₁.wb_right
    a0 a1 (by rw [na _ (by omega), r3]) (by rw [na _ (by omega), r4])
    (by rw [na _ (by omega), r17]) (by rw [na _ (by omega), r18])
    (fun j hj => by rw [ka _ (Or.inl (by omega))]; exact hid j hj) i3 i4 w
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, fun j hj => ?_, fun j hj => ?_,
    fun j hj => ?_, fun j hj => ?_, fun a ha => ?_, fun x hx => ?_, by rw [rb, ra],
    by rw [rmb, rma], by rw [ob, oa]⟩
  · rw [kb (Hb + 9 + m + j) (Or.inl (by omega)), va j hj]
  · rw [kb (Hb + 9 + 2 * m + j) (Or.inl (by omega)), vb j hj]
  · rw [vc j hj, ka (CAPb + j) (Or.inl (by omega))]
  · rw [vd j hj, ka (KRb + j) (Or.inl (by omega))]
  · rw [kb a (ha.imp_left (fun h => by omega)), ka a (ha.imp_right (le_trans (by omega)))]
  · rw [nb x hx, na x hx]

theorem rfD_exec (c : Config) (hc : WordsBounded W c) {Hb E : ℕ}
    (r7 : c.nreg 6707 = Hb) (r13 : c.nreg 6713 = 0) (r21 : c.nreg 6721 = E)
    (w : Hb + 2 ≤ W) :
    ∃ c' t, Exec P W rfD c c' t ∧ t = 10 ∧ c'.nmem Hb = 0 ∧ c'.nmem (Hb + 1) = 0 ∧
      c'.nmem (Hb + 2) = E ∧ c'.nreg 3000 = 0 ∧ c'.nreg 3001 = 1 ∧ c'.nreg 3002 = Hb ∧
      c'.nreg 3003 = E ∧ (∀ a, (a < Hb ∨ Hb + 2 < a) → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hE : E ≤ W := r21 ▸ hc.1 6721
  unfold rfD
  exec_block
  all_goals try omega
  all_goals
    try (config_simp; simp (disch := omega) only [upd_other, upd_same, r7, r13, r21] <;> omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r7, r13, r21])
    try omega

theorem rfBack_exec (c : Config) (hc : WordsBounded W c) {m Hb : ℕ}
    (r0 : c.nreg 6700 = m) (r7 : c.nreg 6707 = Hb) (r13 : c.nreg 6713 = 0)
    (r19 : c.nreg 6719 = Hb + 9 + 5 * m) (r21 : c.nreg 6721 = Hb + 9 + 7 * m)
    (w : Hb + 9 + 7 * m ≤ W) :
    ∃ c' t, Exec P W rfBack c c' t ∧ t ≤ 5 * m + 17 ∧ c'.nmem Hb = 0 ∧ c'.nmem (Hb + 1) = 0 ∧
      c'.nmem (Hb + 2) = Hb + 9 + 7 * m ∧ c'.nreg 3000 = 0 ∧ c'.nreg 3001 = 1 ∧
      c'.nreg 3002 = Hb ∧ c'.nreg 3003 = Hb + 9 + 7 * m ∧
      (∀ j < m, c'.nmem (Hb + 9 + 5 * m + j) = 0) ∧
      (∀ a, (a < Hb ∨ (Hb + 2 < a ∧ (a < Hb + 9 + 5 * m ∨ Hb + 9 + 6 * m ≤ a))) →
        c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rfBack
  obtain ⟨c₁, k₁, e₁, hk₁, s0, s1, s2, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W rfZ c c₁ k₁ ∧ k₁ = 3 ∧ c₁.nreg 6260 = m ∧ c₁.nreg 6261 = Hb + 9 + 5 * m ∧
      c₁.nreg 6262 = 0 ∧ (∀ x, (x < 6260 ∨ 6262 < x) → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold rfZ
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r0, r13, r19])
    simp only [upd_apply]; split_ifs <;> omega
  obtain ⟨c₂, k₂, e₂, hk₂, o1, o2, o3, o4, o5, o6⟩ := lzProg_exec (P := P) c₁ e₁.wb_right s0 s1
    s2 (by omega) (by omega)
  obtain ⟨c₃, k₃, e₃, hk₃, d0, d1, d2, d3, d4, d5, d6, dk, dr, drm, dout⟩ :=
    rfD_exec (P := P) (Hb := Hb) (E := Hb + 9 + 7 * m) c₂ e₂.wb_right
    (by rw [o3 _ (by omega), gn₁ _ (by omega), r7]) (by rw [o3 _ (by omega), gn₁ _ (by omega), r13])
    (by rw [o3 _ (by omega), gn₁ _ (by omega), r21]) (by omega)
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, d0, d1, d2, d3, d4, d5, d6,
    fun j hj => ?_, fun a ha => ?_, by rw [dr, o4, gr₁], by rw [drm, o5, grm₁],
    by rw [dout, o6, go₁]⟩
  · rw [dk _ (Or.inr (by omega)), o1 j hj]
  · have h1 : a < Hb ∨ Hb + 2 < a := ha.imp_right fun h => h.1
    have h2 : ¬ (Hb + 9 + 5 * m ≤ a ∧ a < Hb + 9 + 5 * m + m) := by
      rcases ha with h | ⟨-, h | h⟩ <;> omega
    rw [dk a h1, o2 a h2, gm₁]

set_option maxHeartbeats 1000000 in
/-- **The root frame from index arrays** (see the module docstring): within `46 m + 80` steps,
the driver's cells and registers, the header `m | 0 | tg | Z` at `Hb + 5`, and the arrays
`GID[j] = j`, `RV = REV`, `SG = SIG`, `CP = CAP`, `KR = KR`, `HL = 0` from `Hb + 9`; memory below
`Hb`, reals and output kept. -/
theorem rfProg_exec (c : Config) (hc : WordsBounded W c) {m REVb SIGb CAPb KRb tg Z Hb : ℕ}
    (r0 : c.nreg 6700 = m) (r1 : c.nreg 6701 = REVb) (r2 : c.nreg 6702 = SIGb)
    (r3 : c.nreg 6703 = CAPb) (r4 : c.nreg 6704 = KRb) (r5 : c.nreg 6705 = tg)
    (r6 : c.nreg 6706 = Z) (r7 : c.nreg 6707 = Hb) (i1 : REVb + m ≤ Hb) (i2 : SIGb + m ≤ Hb)
    (i3 : CAPb + m ≤ Hb) (i4 : KRb + m ≤ Hb) (w : Hb + 9 + 7 * m ≤ W) :
    ∃ c' t, Exec P W rfProg c c' t ∧ t ≤ 46 * m + 80 ∧ c'.nmem Hb = 0 ∧
      c'.nmem (Hb + 1) = 0 ∧ c'.nmem (Hb + 2) = Hb + 9 + 7 * m ∧ c'.nreg 3000 = 0 ∧
      c'.nreg 3001 = 1 ∧ c'.nreg 3002 = Hb ∧ c'.nreg 3003 = Hb + 9 + 7 * m ∧
      c'.nmem (Hb + 5) = m ∧ c'.nmem (Hb + 5 + 1) = 0 ∧ c'.nmem (Hb + 5 + 2) = tg ∧
      c'.nmem (Hb + 5 + 3) = Z ∧
      (∀ j < m, c'.nmem (Hb + 5 + 4 + j) = j) ∧
      (∀ j < m, c'.nmem (Hb + 5 + 4 + m + j) = c.nmem (REVb + j)) ∧
      (∀ j < m, c'.nmem (Hb + 5 + 4 + 2 * m + j) = c.nmem (SIGb + j)) ∧
      (∀ j < m, c'.nmem (Hb + 5 + 4 + 3 * m + j) = c.nmem (CAPb + j)) ∧
      (∀ j < m, c'.nmem (Hb + 5 + 4 + 4 * m + j) = c.nmem (KRb + j)) ∧
      (∀ j < m, c'.nmem (Hb + 5 + 4 + 5 * m + j) = 0) ∧
      (∀ a, a < Hb → c'.nmem a = c.nmem a) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rfProg
  obtain ⟨c₁, k₁, e₁, hk₁, a13, a14, a15, a16, a17, a18, a19, a21, m5, m6, m7, m8, gid, kf, nf,
    rf, rmf, of⟩ := rfFront_exec (P := P) c hc r0 r5 r6 r7 w
  obtain ⟨c₂, k₂, e₂, hk₂, vrv, vsg, vcp, vkr, km, nm, rm, rmm, om⟩ := rfMid_exec (P := P) c₁
    e₁.wb_right (by rw [nf _ (by omega), r0]) (by rw [nf _ (by omega), r1])
    (by rw [nf _ (by omega), r2]) (by rw [nf _ (by omega), r3]) (by rw [nf _ (by omega), r4])
    a14 a15 a16 a17 a18 gid i1 i2 i3 i4 w
  obtain ⟨c₃, k₃, e₃, hk₃, b0, b1, b2, b3, b4, b5, b6, hl, kb, rb, rmb, ob⟩ := rfBack_exec
    (P := P) (m := m) (Hb := Hb) c₂ e₂.wb_right (by rw [nm _ (by omega), nf _ (by omega), r0])
    (by rw [nm _ (by omega), nf _ (by omega), r7]) (by rw [nm _ (by omega), a13])
    (by rw [nm _ (by omega), a19]) (by rw [nm _ (by omega), a21]) w
  have e14 : ∀ j < m, c₁.nmem (REVb + j) = c.nmem (REVb + j) := fun j hj => kf _ (Or.inl (by omega))
  have e24 : ∀ j < m, c₁.nmem (SIGb + j) = c.nmem (SIGb + j) := fun j hj => kf _ (Or.inl (by omega))
  have e34 : ∀ j < m, c₁.nmem (CAPb + j) = c.nmem (CAPb + j) := fun j hj => kf _ (Or.inl (by omega))
  have e44 : ∀ j < m, c₁.nmem (KRb + j) = c.nmem (KRb + j) := fun j hj => kf _ (Or.inl (by omega))
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, b0, b1, b2, b3, b4, b5, b6,
    ?_, ?_, ?_, ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_,
    fun j hj => ?_, fun j hj => ?_, fun a ha => ?_, by rw [rmb, rmm, rmf], by rw [ob, om, of]⟩
  · rw [kb (Hb + 5) (Or.inr ⟨by omega, Or.inl (by omega)⟩), km _ (Or.inl (by omega)), m5]
  · rw [kb (Hb + 5 + 1) (Or.inr ⟨by omega, Or.inl (by omega)⟩), km _ (Or.inl (by omega)),
      show Hb + 5 + 1 = Hb + 6 by omega, m6]
  · rw [kb (Hb + 5 + 2) (Or.inr ⟨by omega, Or.inl (by omega)⟩), km _ (Or.inl (by omega)),
      show Hb + 5 + 2 = Hb + 7 by omega, m7]
  · rw [kb (Hb + 5 + 3) (Or.inr ⟨by omega, Or.inl (by omega)⟩), km _ (Or.inl (by omega)),
      show Hb + 5 + 3 = Hb + 8 by omega, m8]
  · rw [kb (Hb + 5 + 4 + j) (Or.inr ⟨by omega, Or.inl (by omega)⟩), km _ (Or.inl (by omega)),
      show Hb + 5 + 4 + j = Hb + 9 + j by omega, gid j hj]
  · rw [kb (Hb + 5 + 4 + m + j) (Or.inr ⟨by omega, Or.inl (by omega)⟩),
      show Hb + 5 + 4 + m + j = Hb + 9 + m + j by omega, vrv j hj, e14 j hj]
  · rw [kb (Hb + 5 + 4 + 2 * m + j) (Or.inr ⟨by omega, Or.inl (by omega)⟩),
      show Hb + 5 + 4 + 2 * m + j = Hb + 9 + 2 * m + j by omega, vsg j hj, e24 j hj]
  · rw [kb (Hb + 5 + 4 + 3 * m + j) (Or.inr ⟨by omega, Or.inl (by omega)⟩),
      show Hb + 5 + 4 + 3 * m + j = Hb + 9 + 3 * m + j by omega, vcp j hj, e34 j hj]
  · rw [kb (Hb + 5 + 4 + 4 * m + j) (Or.inr ⟨by omega, Or.inl (by omega)⟩),
      show Hb + 5 + 4 + 4 * m + j = Hb + 9 + 4 * m + j by omega, vkr j hj, e44 j hj]
  · rw [show Hb + 5 + 4 + 5 * m + j = Hb + 9 + 5 * m + j by omega, hl j hj]
  · rw [kb a (Or.inl ha), km a (Or.inl (by omega)), kf a (Or.inl (by omega))]

end Exec

end BKMNW

end PlanarFlow
