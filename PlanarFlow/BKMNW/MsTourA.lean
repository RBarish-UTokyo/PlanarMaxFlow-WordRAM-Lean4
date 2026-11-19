module

public import PlanarFlow.BKMNW.MsRunD

/-!
# The corner order on the machine, part A: set-up, path flags, the tour array

The MSSP call of FixConservationOnPath (`MsCall.MsspCallSpec`) and its encoder need the walk
around the path `P` (`tour M P.darts`, from `P.d 0`) and the corners of the faces along the path
at their first positions around it (`fixCorner`, `exists_fixCornersInj`). This file has the first
stages of the program `fcProg` computing them from the index arrays of the call (`MsCall.MsIn`):

* `ftSet`: the bases of the arrays in the scratch `S` (registers `8158 … 8170`);
* `ftMk` (loop over the path): `LF[x] := 1` for `x = P[j]` and `x = RV[P[j]]`;
* `ftTA` (loop over the darts): `TA[i] := NX[i]` if `LF[i] ≠ 0`, else `RT[i]` (the walk around
  the path on the indices); and `FP'[FL[i]] := 1` if `LF[i] ≠ 0` (the labels of the faces along
  the path).

Layout of the scratch (each array of length `m`): `NX` at `S`, `FL` at `S + m`, `LF` at
`S + 2m`, `FP` at `S + 3m` (indexed by the label `FL ∈ [1, m]` from the base `S + 3m - 1`),
`VIS` at `S + 4m`, `TA` at `S + 5m`, `TR` at `S + 6m`, `CD` at `S + 7m`, `CS` at `S + 8m`,
`CN` at `S + 9m` (indexed by the label from `S + 9m - 1`). Registers of this piece:
`8150 … 8177` (inputs `8150 … 8155` = `m, RVb, RTb, k, Pb, S`; outputs `8156` = the period,
`8157` = the number of corners).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-! ### The set-up -/

/-- The bases: `ONE`, `FLb = S + m`, `LFb = S + 2m`, `FPb' = S + 3m - 1`, `VISb = S + 4m`,
`TAb = S + 5m`, `TRb = S + 6m`, `CDb = S + 7m`, `CSb = S + 8m`, `CNb' = S + 9m - 1`, `4m`,
`TWO`, `ZERO`. -/
def ftSetA : Stmt :=
  block [.constN 8158 1, .addN 8159 8155 8150, .addN 8160 8159 8150, .addN 8171 8160 8150,
    .subN 8161 8171 8158, .addN 8162 8171 8150, .addN 8163 8162 8150, .addN 8164 8163 8150]

def ftSetB : Stmt :=
  block [.addN 8165 8164 8150, .addN 8166 8165 8150, .addN 8171 8166 8150, .subN 8167 8171 8158,
    .addN 8168 8150 8150, .addN 8168 8168 8168, .constN 8169 2, .constN 8170 0]

def ftSet : Stmt := .seq ftSetA ftSetB

/-- The registers after the set-up. -/
structure FtRegs (c : Config) (m RVb RTb k Pb S : ℕ) : Prop where
  r50 : c.nreg 8150 = m
  r51 : c.nreg 8151 = RVb
  r52 : c.nreg 8152 = RTb
  r53 : c.nreg 8153 = k
  r54 : c.nreg 8154 = Pb
  r55 : c.nreg 8155 = S
  r58 : c.nreg 8158 = 1
  r59 : c.nreg 8159 = S + m
  r60 : c.nreg 8160 = S + 2 * m
  r61 : c.nreg 8161 = S + 3 * m - 1
  r62 : c.nreg 8162 = S + 4 * m
  r63 : c.nreg 8163 = S + 5 * m
  r64 : c.nreg 8164 = S + 6 * m
  r65 : c.nreg 8165 = S + 7 * m
  r66 : c.nreg 8166 = S + 8 * m
  r67 : c.nreg 8167 = S + 9 * m - 1
  r68 : c.nreg 8168 = 4 * m
  r69 : c.nreg 8169 = 2
  r70 : c.nreg 8170 = 0

/-- The registers are kept when every register `8150 … 8170` but `8156`, `8157` is. -/
lemma FtRegs.of {c d : Config} {m RVb RTb k Pb S : ℕ} (h : FtRegs c m RVb RTb k Pb S)
    (hr : ∀ r, 8150 ≤ r → r ≤ 8170 → r ≠ 8156 → r ≠ 8157 → d.nreg r = c.nreg r) :
    FtRegs d m RVb RTb k Pb S := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20⟩ := h
  exact ⟨by rw [hr _ (by omega) (by omega) (by omega) (by omega), h0],
    by rw [hr _ (by omega) (by omega) (by omega) (by omega), h1],
    by rw [hr _ (by omega) (by omega) (by omega) (by omega), h2],
    by rw [hr _ (by omega) (by omega) (by omega) (by omega), h3],
    by rw [hr _ (by omega) (by omega) (by omega) (by omega), h4],
    by rw [hr _ (by omega) (by omega) (by omega) (by omega), h5],
    by rw [hr _ (by omega) (by omega) (by omega) (by omega), h8],
    by rw [hr _ (by omega) (by omega) (by omega) (by omega), h9],
    by rw [hr _ (by omega) (by omega) (by omega) (by omega), h10],
    by rw [hr _ (by omega) (by omega) (by omega) (by omega), h11],
    by rw [hr _ (by omega) (by omega) (by omega) (by omega), h12],
    by rw [hr _ (by omega) (by omega) (by omega) (by omega), h13],
    by rw [hr _ (by omega) (by omega) (by omega) (by omega), h14],
    by rw [hr _ (by omega) (by omega) (by omega) (by omega), h15],
    by rw [hr _ (by omega) (by omega) (by omega) (by omega), h16],
    by rw [hr _ (by omega) (by omega) (by omega) (by omega), h17],
    by rw [hr _ (by omega) (by omega) (by omega) (by omega), h18],
    by rw [hr _ (by omega) (by omega) (by omega) (by omega), h19],
    by rw [hr _ (by omega) (by omega) (by omega) (by omega), h20]⟩

theorem ftSetA_exec (c : Config) (hc : WordsBounded W c) {m S : ℕ}
    (r50 : c.nreg 8150 = m) (r55 : c.nreg 8155 = S) (hW : S + 9 * m + 2 ≤ W) :
    ∃ c' t, Exec P W ftSetA c c' t ∧ t = 8 ∧ c'.nreg 8158 = 1 ∧ c'.nreg 8159 = S + m ∧
      c'.nreg 8160 = S + 2 * m ∧ c'.nreg 8161 = S + 3 * m - 1 ∧ c'.nreg 8162 = S + 4 * m ∧
      c'.nreg 8163 = S + 5 * m ∧ c'.nreg 8164 = S + 6 * m ∧
      (∀ r, (r < 8158 ∨ 8171 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ftSetA
  exec_block
  all_goals try ((try config_simp); (try simp only [r50, r55]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [r50, r55]; done)
    | (simp only [r50, r55]; omega)
    | (simp only [upd_apply]; split_ifs <;> omega)

theorem ftSetB_exec (c : Config) (hc : WordsBounded W c) {m S : ℕ}
    (r50 : c.nreg 8150 = m) (r64 : c.nreg 8164 = S + 6 * m) (r58 : c.nreg 8158 = 1)
    (hW : S + 9 * m + 2 ≤ W) :
    ∃ c' t, Exec P W ftSetB c c' t ∧ t = 8 ∧ c'.nreg 8165 = S + 7 * m ∧
      c'.nreg 8166 = S + 8 * m ∧ c'.nreg 8167 = S + 9 * m - 1 ∧ c'.nreg 8168 = 4 * m ∧
      c'.nreg 8169 = 2 ∧ c'.nreg 8170 = 0 ∧
      (∀ r, (r < 8165 ∨ 8171 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ftSetB
  exec_block
  all_goals try ((try config_simp); (try simp only [r50, r64, r58]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [r50, r64, r58]; done)
    | (simp only [r50, r64, r58]; omega)
    | (simp only [upd_apply]; split_ifs <;> omega)

theorem ftSet_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb k Pb S : ℕ}
    (r50 : c.nreg 8150 = m) (r51 : c.nreg 8151 = RVb) (r52 : c.nreg 8152 = RTb)
    (r53 : c.nreg 8153 = k) (r54 : c.nreg 8154 = Pb) (r55 : c.nreg 8155 = S)
    (hW : S + 9 * m + 2 ≤ W) :
    ∃ c' t, Exec P W ftSet c c' t ∧ t = 16 ∧ FtRegs c' m RVb RTb k Pb S ∧
      (∀ r, (r < 8158 ∨ 8171 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a58, a59, a60, a61, a62, a63, a64, aR, am, ar, arm, ao⟩ :=
    ftSetA_exec (P := P) c hc r50 r55 hW
  obtain ⟨c₂, k₂, e₂, hk₂, b65, b66, b67, b68, b69, b70, bR, bm, br, brm, bo⟩ :=
    ftSetB_exec (P := P) c₁ e₁.wb_right (by rw [aR _ (by omega), r50]) a64 a58 hW
  have f : ∀ r, (r < 8158 ∨ 8171 < r) → c₂.nreg r = c.nreg r := fun r hr => by
    rw [bR r (by omega), aR r hr]
  have g : ∀ r, 8158 ≤ r → r < 8165 → c₂.nreg r = c₁.nreg r := fun r h1 h2 => bR r (by omega)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega,
    ⟨by rw [f _ (by omega), r50], by rw [f _ (by omega), r51], by rw [f _ (by omega), r52],
      by rw [f _ (by omega), r53], by rw [f _ (by omega), r54], by rw [f _ (by omega), r55],
      by rw [g _ (by omega) (by omega), a58], by rw [g _ (by omega) (by omega), a59],
      by rw [g _ (by omega) (by omega), a60], by rw [g _ (by omega) (by omega), a61],
      by rw [g _ (by omega) (by omega), a62], by rw [g _ (by omega) (by omega), a63],
      by rw [g _ (by omega) (by omega), a64], b65, b66, b67, b68, b69, b70⟩,
    f, by rw [bm, am], by rw [br, ar], by rw [brm, arm], by rw [bo, ao]⟩

/-! ### The flags of the darts of the path -/

/-- `x := P[j]`, `LF[x] := 1`, `x := RV[x]`, `LF[x] := 1`, `j := j + 1`. -/
def ftMkBody : Stmt :=
  block [.addN 8174 8154 8172, .loadN 8173 8174, .addN 8174 8160 8173, .storeN 8174 8158,
    .addN 8174 8151 8173, .loadN 8173 8174, .addN 8174 8160 8173, .storeN 8174 8158,
    .addN 8172 8172 8158]

/-- **The flags of the path**: `LF[P[j]] := 1`, `LF[RV[P[j]]] := 1` for `j < k`. -/
def ftMk : Stmt := .seq (block [.constN 8172 0]) (.whileLtN 8172 8153 ftMkBody)

theorem ftMkBody_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb k Pb S j p r : ℕ}
    (hR : FtRegs c m RVb RTb k Pb S) (r72 : c.nreg 8172 = j) (hp : c.nmem (Pb + j) = p)
    (hr : c.nmem (RVb + p) = r) (hdis : RVb + p ≠ S + 2 * m + p)
    (w1 : Pb + j ≤ W) (w2 : S + 2 * m + p ≤ W) (w3 : RVb + p ≤ W) (w4 : S + 2 * m + r ≤ W)
    (w5 : j + 1 ≤ W) :
    ∃ c' t, Exec P W ftMkBody c c' t ∧ t = 9 ∧ c'.nreg 8172 = j + 1 ∧
      c'.nmem = upd (upd c.nmem (S + 2 * m + p) 1) (S + 2 * m + r) 1 ∧
      (∀ x, (x < 8172 ∨ 8174 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20⟩ := hR
  have hr' : upd c.nmem (S + 2 * m + p) 1 (RVb + p) = r := by
    rw [upd_other _ _ _ hdis, hr]
  unfold ftMkBody
  exec_block
  all_goals try ((try config_simp); (try simp only [h1, h4, h8, h10, r72, hp, hr']); omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [h8, r72]
  · simp only [h1, h4, h8, h10, r72, hp, hr']
  · simp only [upd_apply]; split_ifs <;> omega

/-- The darts of the first `j` steps of the path, on the indices. -/
def mkSet (pm rv : ℕ → ℕ) (j i : ℕ) : Prop := ∃ j' < j, i = pm j' ∨ i = rv (pm j')

instance (pm rv : ℕ → ℕ) (j i : ℕ) : Decidable (mkSet pm rv j i) := by
  unfold mkSet; infer_instance

lemma mkSet_succ {pm rv : ℕ → ℕ} {j i : ℕ} :
    mkSet pm rv (j + 1) i ↔ mkSet pm rv j i ∨ i = pm j ∨ i = rv (pm j) := by
  unfold mkSet
  constructor
  · rintro ⟨j', hj', h⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
    · exact Or.inl ⟨j', hj', h⟩
    · exact Or.inr h
  · rintro (⟨j', hj', h⟩ | h)
    · exact ⟨j', by omega, h⟩
    · exact ⟨j, by omega, h⟩

/-- **The flags of the path**: from `LF` zero, within `11 k + 3` steps
`LF[i] = 1` iff `i = P[j']` or `i = RV[P[j']]` for some `j' < k`, else `0` (`i < m`); memory
outside `LF` and registers outside `8172 … 8174` kept. -/
theorem ftMk_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb k Pb S : ℕ}
    (hR : FtRegs c m RVb RTb k Pb S) {pm rv : ℕ → ℕ}
    (hpm : ∀ j < k, c.nmem (Pb + j) = pm j ∧ pm j < m)
    (hrv : ∀ i < m, c.nmem (RVb + i) = rv i ∧ rv i < m)
    (dRV : RVb + m ≤ S + 2 * m ∨ S + 3 * m ≤ RVb)
    (dP : Pb + k ≤ S + 2 * m ∨ S + 3 * m ≤ Pb)
    (hz : ∀ i < m, c.nmem (S + 2 * m + i) = 0)
    (w1 : Pb + k ≤ W) (w2 : S + 3 * m ≤ W) (w3 : RVb + m ≤ W) (w5 : k + 1 ≤ W) :
    ∃ c' t, Exec P W ftMk c c' t ∧ t ≤ 11 * k + 3 ∧
      (∀ i < m, c'.nmem (S + 2 * m + i) = if mkSet pm rv k i then 1 else 0) ∧
      (∀ a, (a < S + 2 * m ∨ S + 3 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 8172 ∨ 8174 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ftMk
  obtain ⟨c₁, k₁, e₁, hk₁, g2, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 8172 0]) c c₁ k₁ ∧ k₁ = 1 ∧ c₁.nreg 8172 = 0 ∧
      (∀ x, x ≠ 8172 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 8172 → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun j c' =>
    (∀ x, (x < 8172 ∨ 8174 < x) → c'.nreg x = c.nreg x) ∧
    (∀ i < m, c'.nmem (S + 2 * m + i) = if mkSet pm rv j i then 1 else 0) ∧
    (∀ a, (a < S + 2 * m ∨ S + 3 * m ≤ a) → c'.nmem a = m₀ a) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h72, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 8172)
    (b := 8153) (body := ftMkBody) J (B := 9) c₁ hw₁ g2
    (by rw [q _ (by omega), hR.r53]) (Nat.zero_le k)
    ⟨fun x hx => q x (by omega), fun i hi => by
      rw [gm₁, hz i hi]; simp [mkSet], fun a _ => by rw [gm₁], gr₁, grm₁, go₁⟩
    (fun j c' hlo hhi hw h72 h53 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have hR' : FtRegs c' m RVb RTb k Pb S :=
        hR.of fun r h1 h2 _ _ => j1 r (by omega)
      obtain ⟨ep, hpl⟩ := hpm j hhi
      obtain ⟨er, hrl⟩ := hrv (pm j) hpl
      have e1 : c'.nmem (Pb + j) = pm j := by
        rw [j3 _ (by omega), ep]
      have e2 : c'.nmem (RVb + pm j) = rv (pm j) := by
        rw [j3 _ (by omega), er]
      obtain ⟨c'', t, ex, ht, h72', hm', hn', hr', hrm', ho'⟩ := ftMkBody_exec (P := P) c' hw
        hR' h72 e1 e2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      refine ⟨c'', t, ex, ht.le, h72', by rw [hn' _ (by omega)]; exact h53,
        fun x hx => by rw [hn' x hx, j1 x hx], fun i hi => ?_, fun a ha => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm']
        by_cases h1 : i = rv (pm j)
        · subst h1
          rw [upd_same]
          simp [mkSet_succ]
        · rw [upd_other _ _ _ (by omega)]
          by_cases h2 : i = pm j
          · subst h2
            rw [upd_same]
            simp [mkSet_succ]
          · rw [upd_other _ _ _ (by omega), j2 i hi]
            have : mkSet pm rv (j + 1) i ↔ mkSet pm rv j i := by
              rw [mkSet_succ]; tauto
            simp only [this]
      · rw [hm', upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
        exact j3 a ha)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by norm_num at hk₂; omega, j2, j3, fun x hx => j1 x hx,
    j4, j5, j6⟩

/-! ### The tour array and the labels of the faces along the path -/

/-- `TA[i] := LF[i] ≠ 0 ? NX[i] : RT[i]`, and `FP'[FL[i]] := 1` when `LF[i] ≠ 0`. -/
def ftTAThen : Stmt :=
  block [.addN 8174 8155 8172, .loadN 8176 8174, .addN 8174 8159 8172, .loadN 8177 8174,
    .addN 8174 8161 8177, .storeN 8174 8158]

def ftTAElse : Stmt := block [.addN 8174 8152 8172, .loadN 8176 8174]

def ftTABody : Stmt :=
  .seq (block [.addN 8174 8160 8172, .loadN 8175 8174])
    (.seq (.ifLtN 8170 8175 ftTAThen ftTAElse)
      (block [.addN 8174 8163 8172, .storeN 8174 8176, .addN 8172 8172 8158]))

/-- **The tour array** (loop over the darts). -/
def ftTA : Stmt := .seq (block [.constN 8172 0]) (.whileLtN 8172 8150 ftTABody)

theorem ftTABody_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb k Pb S i : ℕ}
    (hR : FtRegs c m RVb RTb k Pb S) (r72 : c.nreg 8172 = i) (hi : i < m)
    (hfl : 1 ≤ c.nmem (S + m + i) ∧ c.nmem (S + m + i) ≤ m)
    (w : S + 9 * m + 2 ≤ W) (wRT : RTb + m ≤ W) :
    ∃ c' t, Exec P W ftTABody c c' t ∧ t ≤ 14 ∧ c'.nreg 8172 = i + 1 ∧
      c'.nmem = (if 0 < c.nmem (S + 2 * m + i) then
        upd (upd c.nmem (S + 3 * m - 1 + c.nmem (S + m + i)) 1) (S + 5 * m + i)
          (c.nmem (S + i))
        else upd c.nmem (S + 5 * m + i) (c.nmem (RTb + i))) ∧
      (∀ x, (x < 8172 ∨ 8177 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20⟩ := hR
  unfold ftTABody
  obtain ⟨c₁, k₁, e₁, hk₁, g5, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.addN 8174 8160 8172, .loadN 8175 8174]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 8175 = c.nmem (S + 2 * m + i) ∧
      (∀ x, x ≠ 8174 → x ≠ 8175 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [h10, r72]); omega)
    refine ⟨rfl, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [h10, r72]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q1 : ∀ x, x ≠ 8174 → x ≠ 8175 → c₁.nreg x = c.nreg x := gn₁
  -- the store and the increment, from a configuration with `r8176 = v`
  have fin : ∀ (d : Config) (v : ℕ), WordsBounded W d → d.nreg 8172 = i → d.nreg 8158 = 1 →
      d.nreg 8163 = S + 5 * m → d.nreg 8176 = v →
      ∃ d' k, Exec P W (block [.addN 8174 8163 8172, .storeN 8174 8176, .addN 8172 8172 8158])
        d d' k ∧ k = 3 ∧ d'.nreg 8172 = i + 1 ∧ d'.nmem = upd d.nmem (S + 5 * m + i) v ∧
        (∀ x, x ≠ 8172 → x ≠ 8174 → d'.nreg x = d.nreg x) ∧ d'.rreg = d.rreg ∧
        d'.rmem = d.rmem ∧ d'.output = d.output := fun d v hd s72 s58 s63 s76 => by
    exec_block
    all_goals try ((try config_simp); (try simp only [s72, s58, s63, s76]); omega)
    refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl⟩
    · config_simp; simp only [s72, s58]
    · config_simp; simp only [s72, s63, s76]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  by_cases hs : 0 < c.nmem (S + 2 * m + i)
  · obtain ⟨c₂, k₂, e₂, hk₂, g76, gn₂, gm₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
        Exec P W ftTAThen c₁ c₂ k₂ ∧ k₂ = 6 ∧ c₂.nreg 8176 = c.nmem (S + i) ∧
        (∀ x, x ≠ 8174 → x ≠ 8176 → x ≠ 8177 → c₂.nreg x = c₁.nreg x) ∧
        c₂.nmem = upd c.nmem (S + 3 * m - 1 + c.nmem (S + m + i)) 1 ∧
        c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
      have s55 : c₁.nreg 8155 = S := by rw [q1 _ (by omega) (by omega), h5]
      have s59 : c₁.nreg 8159 = S + m := by rw [q1 _ (by omega) (by omega), h9]
      have s61 : c₁.nreg 8161 = S + 3 * m - 1 := by rw [q1 _ (by omega) (by omega), h11]
      have s58 : c₁.nreg 8158 = 1 := by rw [q1 _ (by omega) (by omega), h8]
      have s72 : c₁.nreg 8172 = i := by rw [q1 _ (by omega) (by omega), r72]
      unfold ftTAThen
      exec_block
      all_goals try ((try config_simp); (try simp only [s55, s59, s61, s58, s72, gm₁]); omega)
      refine ⟨rfl, ?_, fun x a b d => ?_, ?_, rfl, rfl, rfl⟩
      · config_simp; simp only [s55, s72, gm₁]
      · config_simp; simp only [upd_apply]; split_ifs <;> omega
      · config_simp; simp only [s55, s59, s61, s58, s72, gm₁]
    have t2 : c₁.nreg 8170 < c₁.nreg 8175 := by
      rw [g5, q1 _ (by omega) (by omega), h20]; exact hs
    obtain ⟨c₃, k₃, e₃, hk₃, h72, gm₃, gn₃, gr₃, grm₃, go₃⟩ := fin c₂ _ e₂.wb_right
      (by rw [gn₂ _ (by omega) (by omega) (by omega), q1 _ (by omega) (by omega), r72])
      (by rw [gn₂ _ (by omega) (by omega) (by omega), q1 _ (by omega) (by omega), h8])
      (by rw [gn₂ _ (by omega) (by omega) (by omega), q1 _ (by omega) (by omega), h13]) g76
    refine ⟨c₃, k₁ + (k₂ + 1 + k₃), .seq e₁ (.seq (.ifLtN_true t2 e₂) e₃), by omega, h72,
      by rw [gm₃, gm₂, iteT hs], fun x hx => ?_, by rw [gr₃, gr₂, gr₁],
      by rw [grm₃, grm₂, grm₁], by rw [go₃, go₂, go₁]⟩
    rw [gn₃ x (by omega) (by omega), gn₂ x (by omega) (by omega) (by omega),
      q1 x (by omega) (by omega)]
  · obtain ⟨c₂, k₂, e₂, hk₂, g76, gn₂, gm₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
        Exec P W ftTAElse c₁ c₂ k₂ ∧ k₂ = 2 ∧ c₂.nreg 8176 = c.nmem (RTb + i) ∧
        (∀ x, x ≠ 8174 → x ≠ 8176 → c₂.nreg x = c₁.nreg x) ∧ c₂.nmem = c.nmem ∧
        c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
      have s52 : c₁.nreg 8152 = RTb := by rw [q1 _ (by omega) (by omega), h2]
      have s72 : c₁.nreg 8172 = i := by rw [q1 _ (by omega) (by omega), r72]
      unfold ftTAElse
      exec_block
      all_goals try ((try config_simp); (try simp only [s52, s72, gm₁]); omega)
      refine ⟨rfl, ?_, fun x a b => ?_, ?_, rfl, rfl, rfl⟩
      · config_simp; simp only [s52, s72, gm₁]
      · config_simp; simp only [upd_apply]; split_ifs <;> omega
      · config_simp; simp only [gm₁]
    have t2 : ¬ c₁.nreg 8170 < c₁.nreg 8175 := by
      rw [g5, q1 _ (by omega) (by omega), h20]; exact hs
    obtain ⟨c₃, k₃, e₃, hk₃, h72, gm₃, gn₃, gr₃, grm₃, go₃⟩ := fin c₂ _ e₂.wb_right
      (by rw [gn₂ _ (by omega) (by omega), q1 _ (by omega) (by omega), r72])
      (by rw [gn₂ _ (by omega) (by omega), q1 _ (by omega) (by omega), h8])
      (by rw [gn₂ _ (by omega) (by omega), q1 _ (by omega) (by omega), h13]) g76
    refine ⟨c₃, k₁ + (k₂ + 2 + k₃), .seq e₁ (.seq (.ifLtN_false t2 e₂) e₃), by omega, h72,
      by rw [gm₃, gm₂, iteF hs], fun x hx => ?_, by rw [gr₃, gr₂, gr₁],
      by rw [grm₃, grm₂, grm₁], by rw [go₃, go₂, go₁]⟩
    rw [gn₃ x (by omega) (by omega), gn₂ x (by omega) (by omega), q1 x (by omega) (by omega)]

/-- **The tour array**: from `FP` zero, for arrays `NX = nx`, `FL = fl` (labels in `[1, m]`),
`LF = lf`, `RT = rt`, within `16 m + 3` steps `TA[i] = lf i ≠ 0 ? nx i : rt i` and
`FP'[l] = 1` iff some `i < m` has `lf i ≠ 0` and `fl i = l`, else `0` (`1 ≤ l ≤ m`); memory
outside `FP` and `TA` and registers outside `8172 … 8177` kept. -/
theorem ftTA_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb k Pb S : ℕ}
    (hR : FtRegs c m RVb RTb k Pb S) {nx fl lf rt : ℕ → ℕ}
    (hnx : ∀ i < m, c.nmem (S + i) = nx i) (hfl : ∀ i < m, c.nmem (S + m + i) = fl i)
    (hfl' : ∀ i < m, 1 ≤ fl i ∧ fl i ≤ m)
    (hlf : ∀ i < m, c.nmem (S + 2 * m + i) = lf i) (hrt : ∀ i < m, c.nmem (RTb + i) = rt i)
    (dRT : RTb + m ≤ S + 3 * m ∨ S + 6 * m ≤ RTb)
    (hz : ∀ l, 1 ≤ l → l ≤ m → c.nmem (S + 3 * m - 1 + l) = 0)
    (w : S + 9 * m + 2 ≤ W) (wRT : RTb + m ≤ W) :
    ∃ c' t, Exec P W ftTA c c' t ∧ t ≤ 16 * m + 3 ∧
      (∀ i < m, c'.nmem (S + 5 * m + i) = if 0 < lf i then nx i else rt i) ∧
      (∀ l, 1 ≤ l → l ≤ m → c'.nmem (S + 3 * m - 1 + l) =
        if ∃ i < m, 0 < lf i ∧ fl i = l then 1 else 0) ∧
      (∀ a, (a < S + 3 * m ∨ S + 4 * m ≤ a) → (a < S + 5 * m ∨ S + 6 * m ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 8172 ∨ 8177 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ftTA
  obtain ⟨c₁, k₁, e₁, hk₁, g2, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 8172 0]) c c₁ k₁ ∧ k₁ = 1 ∧ c₁.nreg 8172 = 0 ∧
      (∀ x, x ≠ 8172 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 8172 → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun j c' =>
    (∀ x, (x < 8172 ∨ 8177 < x) → c'.nreg x = c.nreg x) ∧
    (∀ i < j, c'.nmem (S + 5 * m + i) = if 0 < lf i then nx i else rt i) ∧
    (∀ l, 1 ≤ l → l ≤ m → c'.nmem (S + 3 * m - 1 + l) =
      if ∃ i < j, 0 < lf i ∧ fl i = l then 1 else 0) ∧
    (∀ a, (a < S + 3 * m ∨ S + 4 * m ≤ a) → (a < S + 5 * m ∨ S + 5 * m + j ≤ a) →
      c'.nmem a = m₀ a) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h72, j1, j2, j3, j4, j5, j6, j7⟩ := lnRange (P := P) (a := 8172)
    (b := 8150) (body := ftTABody) J (B := 14) c₁ hw₁ g2
    (by rw [q _ (by omega), hR.r50]) (Nat.zero_le m)
    ⟨fun x hx => q x (by omega), fun i hi => absurd hi (by omega), fun l h1 h2 => by
      rw [gm₁, hz l h1 h2]; simp, fun a _ _ => by rw [gm₁], gr₁, grm₁, go₁⟩
    (fun j c' hlo hhi hw h72 h50 ⟨j1, j2, j3, j4, j5, j6, j7⟩ => by
      have hR' : FtRegs c' m RVb RTb k Pb S :=
        hR.of fun r h1 h2 _ _ => j1 r (by omega)
      have e1 : c'.nmem (S + m + j) = fl j := by rw [j4 _ (by omega) (by omega), hfl j hhi]
      have e2 : c'.nmem (S + 2 * m + j) = lf j := by
        rw [j4 _ (by omega) (by omega), hlf j hhi]
      have e3 : c'.nmem (S + j) = nx j := by rw [j4 _ (by omega) (by omega), hnx j hhi]
      have e4 : c'.nmem (RTb + j) = rt j := by
        rw [j4 _ (by omega) (by omega), hrt j hhi]
      have hfj := hfl' j hhi
      obtain ⟨c'', t, ex, ht, h72', hm', hn', hr', hrm', ho'⟩ := ftTABody_exec (P := P) c' hw
        hR' h72 hhi (by rw [e1]; exact hfj) w wRT
      rw [e1, e2, e3, e4] at hm'
      refine ⟨c'', t, ex, ht, h72', by rw [hn' _ (by omega)]; exact h50,
        fun x hx => by rw [hn' x hx, j1 x hx], fun i hi => ?_, fun l h1 h2 => ?_,
        fun a ha ha' => ?_, by rw [hr', j5], by rw [hrm', j6], by rw [ho', j7]⟩
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · split_ifs <;> (repeat rw [upd_other _ _ _ (by omega)]) <;> rw [j2 i hi] <;>
            simp_all
        · split_ifs with hl <;> simp [hl]
      · rw [hm']
        have hiff : (∃ i < j + 1, 0 < lf i ∧ fl i = l) ↔
            (∃ i < j, 0 < lf i ∧ fl i = l) ∨ (0 < lf j ∧ fl j = l) := by
          constructor
          · rintro ⟨i, hi, h⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
            · exact Or.inl ⟨i, hi, h⟩
            · exact Or.inr h
          · rintro (⟨i, hi, h⟩ | h)
            · exact ⟨i, by omega, h⟩
            · exact ⟨j, by omega, h⟩
        by_cases hs : 0 < lf j
        · rw [iteT hs, upd_other _ _ _ (by omega)]
          by_cases hl : fl j = l
          · subst hl
            rw [upd_same]
            simp only [hiff, hs, true_and, or_true, ↓reduceIte]
          · rw [upd_other _ _ _ (by omega), j3 l h1 h2]
            simp only [hiff, hl, and_false, or_false]
        · rw [iteF hs, upd_other _ _ _ (by omega), j3 l h1 h2]
          simp only [hiff, hs, false_and, or_false]
      · rw [hm']
        split_ifs
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
          exact j4 a ha (by omega)
        · rw [upd_other _ _ _ (by omega)]
          exact j4 a ha (by omega))
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by norm_num at hk₂; omega, j2, j3,
    fun a ha ha' => j4 a ha (by omega),
    fun x hx => j1 x hx, j5, j6, j7⟩

end MsEnc

end BKMNW

end PlanarFlow
