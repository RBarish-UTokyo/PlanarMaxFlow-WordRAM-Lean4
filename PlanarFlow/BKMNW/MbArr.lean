module

public import PlanarFlow.BKMNW.MbSep
public import PlanarFlow.BKMNW.LinRot
public import PlanarFlow.BKMNW.KeepProg

/-!
# Miller's base, step 1: the index arrays of the piece map, compacted

For the base case of `scertD` (Miller) the machine must write the index arrays of the piece map
`psep M hσ hB` (darts `N`, rotation the first return `ret τ N`) numbered by `cNe e n N` (the rank
of the index), as `sepC` (`MbSep.lean`) reads them. From the flags `NF` (`NF[i] ≠ 0 ↔ e i ∈ N`),
the rotation array `SG` of `τ` (stable on the enumerated darts `B`), the reverse array `RV` and
the weights `EX`, all indexed by `i < n`:

* `mc1` (one scan): `RK[i] = Σ_{j<i} [NF[j] ≠ 0]` (the rank, `eRk_e`), `NX := SG`,
  `DF[i] = 1 - [NF[i] ≠ 0]`, the count `#N`;
* `lsProg` (`PR[SG[i]] := i`) and `ldProg` (delete the flagged-off darts): `NX` represents
  `ret τ N` (the loops of `LinRet.lean`/`LinRot.lean`, called as they are);
* `mc3` (one scan): for `e i ∈ N`, `CR[RK[i]] := RK[RV[i]]`, `CS[RK[i]] := RK[NX[i]]`,
  `CE[RK[i]] := EX[i]`, the weight sum `Σ_N ex`, the number of darts of `N` whose reverse is not
  in `N` (`0` iff `N` is closed under `rev`).

* **`mcProg`**, **`mcProg_exec`** (`… ≤ 60 n + 40` steps);
* **`mc_encArr`**: the arrays `CR`, `CS`, `CE` are `EncArr (psep M hσ hB) (cNe e n N) ex` when
  the rotation of the piece is `ret τ N` on `N`.
Registers: inputs `5000 = n`, `5001 = NFb`, `5002 = SGb`, `5003 = RVb`, `5004 = Hb`,
`5008 = EXb`; the arrays `RK | NX | DF | PR | CR | CS | CE` at `Hb, Hb + n, …, Hb + 6 n`; written
`5005 … 5029` and the registers of `lsProg` (`6220 … 6228`) and `ldProg` (`6240 … 6250`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The first scan: ranks, a copy of the rotation, deletion flags -/

/-- One index of the first scan (`5010 = 1`, `5011 = i`, `5012 = cnt`; scratch `5013 … 5016`). -/
def mc1Body : Stmt :=
  block [.addN 5013 5001 5011, .loadN 5013 5013, .divN 5013 5013 5013,
    .addN 5014 5002 5011, .loadN 5014 5014,
    .addN 5015 5004 5011, .storeN 5015 5012,
    .addN 5015 5005 5011, .storeN 5015 5014,
    .subN 5016 5010 5013,
    .addN 5015 5006 5011, .storeN 5015 5016,
    .addN 5012 5012 5013, .addN 5011 5011 5010]

/-- **The first scan.** -/
def mc1 : Stmt :=
  .seq (block [.constN 5010 1, .constN 5011 0, .constN 5012 0]) (.whileLtN 5011 5000 mc1Body)

section Exec

variable {P : Input} {W : ℕ}

theorem mc1Body_exec (c : Config) (hc : WordsBounded W c) {NFb SGb RKb NXb DFb i cnt nf sg : ℕ}
    (r1 : c.nreg 5001 = NFb) (r2 : c.nreg 5002 = SGb) (r4 : c.nreg 5004 = RKb)
    (r5 : c.nreg 5005 = NXb) (r6 : c.nreg 5006 = DFb) (r10 : c.nreg 5010 = 1)
    (r11 : c.nreg 5011 = i) (r12 : c.nreg 5012 = cnt) (hnf : c.nmem (NFb + i) = nf)
    (hsg : c.nmem (SGb + i) = sg)
    (w1 : NFb + i ≤ W) (w2 : SGb + i ≤ W) (w4 : RKb + i ≤ W) (w5 : NXb + i ≤ W)
    (w6 : DFb + i ≤ W) (w7 : cnt + 1 ≤ W) (w8 : i + 1 ≤ W) :
    ∃ c' t, Exec P W mc1Body c c' t ∧ t = 14 ∧ c'.nreg 5011 = i + 1 ∧
      c'.nreg 5012 = cnt + nf / nf ∧
      c'.nmem = upd (upd (upd c.nmem (RKb + i) cnt) (NXb + i) sg) (DFb + i) (1 - nf / nf) ∧
      (∀ x, (x < 5011 ∨ 5016 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have h1 : nf / nf ≤ 1 := by rw [sgn_eq]; split_ifs <;> omega
  unfold mc1Body
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r4, r5, r6, r10, r11, r12, hnf, hsg]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r10, r11]
  · config_simp; simp only [r1, r2, r4, r5, r6, r10, r11, r12, hnf, hsg]
  · config_simp; simp only [r1, r2, r4, r5, r6, r10, r11, r12, hnf, hsg]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- The sign of a flag. -/
abbrev mcF (m : ℕ → ℕ) (NFb j : ℕ) : ℕ := m (NFb + j) / m (NFb + j)

lemma mcF_le (m : ℕ → ℕ) (NFb j : ℕ) : mcF m NFb j ≤ 1 := by
  unfold mcF; rw [sgn_eq]; split_ifs <;> omega

lemma sum_mcF_le (m : ℕ → ℕ) (NFb i : ℕ) : ∑ j ∈ range i, mcF m NFb j ≤ i := by
  calc ∑ j ∈ range i, mcF m NFb j ≤ ∑ _j ∈ range i, 1 := sum_le_sum fun j _ => mcF_le m NFb j
    _ = i := by simp

/-- **The first scan**: within `16 n + 5` steps, `RK[j] = Σ_{l<j} [NF[l] ≠ 0]`, `NX[j] = SG[j]`,
`DF[j] = 1 - [NF[j] ≠ 0]` for `j < n`, the count `r5012 = Σ_{j<n} [NF[j] ≠ 0]`; memory outside
the three arrays, registers outside `5010 … 5016`, reals and output kept. -/
theorem mc1_exec (c : Config) (hc : WordsBounded W c) {n NFb SGb RKb NXb DFb : ℕ}
    (r0 : c.nreg 5000 = n) (r1 : c.nreg 5001 = NFb) (r2 : c.nreg 5002 = SGb)
    (r4 : c.nreg 5004 = RKb) (r5 : c.nreg 5005 = NXb) (r6 : c.nreg 5006 = DFb)
    (lay : NFb + n ≤ RKb ∧ SGb + n ≤ RKb ∧ RKb + n ≤ NXb ∧ NXb + n ≤ DFb ∧ DFb + n + 1 ≤ W) :
    ∃ c' t, Exec P W mc1 c c' t ∧ t ≤ 16 * n + 5 ∧ c'.nreg 5010 = 1 ∧
      c'.nreg 5012 = ∑ j ∈ range n, mcF c.nmem NFb j ∧
      (∀ j < n, c'.nmem (RKb + j) = ∑ l ∈ range j, mcF c.nmem NFb l) ∧
      (∀ j < n, c'.nmem (NXb + j) = c.nmem (SGb + j)) ∧
      (∀ j < n, c'.nmem (DFb + j) = 1 - mcF c.nmem NFb j) ∧
      (∀ a, (a < RKb ∨ DFb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 5010 ∨ 5016 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5⟩ := lay
  unfold mc1
  obtain ⟨c₁, k₁, e₁, hk₁, g0, g1, g2, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 5010 1, .constN 5011 0, .constN 5012 0]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 5010 = 1 ∧ c₁.nreg 5011 = 0 ∧ c₁.nreg 5012 = 0 ∧
      (∀ x, (x < 5010 ∨ 5012 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; done)
    obtain ⟨a1, a2, a3⟩ : x ≠ 5010 ∧ x ≠ 5011 ∧ x ≠ 5012 := by omega
    simp only [Config.nreg_mk, upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3]
  have hw₁ := e₁.wb_right
  have q : ∀ x, (x < 5010 ∨ 5012 < x) → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 5011 ∨ 5016 < x) → c'.nreg x = c₁.nreg x) ∧
    c'.nreg 5012 = ∑ j ∈ range i, mcF m₀ NFb j ∧
    (∀ j < i, c'.nmem (RKb + j) = ∑ l ∈ range j, mcF m₀ NFb l) ∧
    (∀ j < i, c'.nmem (NXb + j) = m₀ (SGb + j)) ∧
    (∀ j < i, c'.nmem (DFb + j) = 1 - mcF m₀ NFb j) ∧
    (∀ a, (a < RKb ∨ DFb + n ≤ a) → c'.nmem a = m₀ a) ∧
    (∀ j, i ≤ j → j < n → c'.nmem (NFb + j) = m₀ (NFb + j) ∧ c'.nmem (SGb + j) = m₀ (SGb + j)) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h11, j1, j2, j3, j4, j5, j6, -, j7, j8, j9⟩ := tgRange (P := P)
    (a := 5011) (b := 5000) (body := mc1Body) J (B := 14) c₁ hw₁ g1
    (by rw [q _ (by omega), r0]) (Nat.zero_le n)
    ⟨fun _ _ => rfl, by rw [g2]; rfl, fun j hj => absurd hj (by omega),
      fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
      fun a _ => by rw [gm₁],
      fun j _ _ => ⟨by rw [gm₁], by rw [gm₁]⟩, rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h11 h00 ⟨j1, j2, j3, j4, j5, j6, j7, j8, j9, j10⟩ => by
      have f : ∀ x, (x < 5011 ∨ 5016 < x) → c'.nreg x = c₁.nreg x := j1
      have hcnt := sum_mcF_le m₀ NFb i
      obtain ⟨e1, e2⟩ := j7 i le_rfl hhi
      obtain ⟨c'', t, ex, ht, h11', h12', hm', hn', hr', hrm', ho'⟩ :=
        mc1Body_exec (P := P) c' hw (by rw [f _ (by omega), q _ (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega), r2]) (by rw [f _ (by omega), q _ (by omega), r4])
        (by rw [f _ (by omega), q _ (by omega), r5]) (by rw [f _ (by omega), q _ (by omega), r6])
        (by rw [f _ (by omega), g0]) h11 j2 e1 e2 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
      refine ⟨c'', t, ex, ht.le, h11', by rw [hn' _ (by omega)]; exact h00,
        fun x hx => by rw [hn' x hx, f x hx], ?_, fun j hj => ?_, fun j hj => ?_,
        fun j hj => ?_, fun a ha => ?_, fun j hj1 hj2 => ?_,
        by rw [hr', j8], by rw [hrm', j9], by rw [ho', j10]⟩
      · rw [h12', sum_range_succ]
      · rw [hm', upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j3 j hj
        · rw [upd_same]
      · rw [hm', upd_other _ _ _ (by omega)]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact j4 j hj
        · rw [upd_same]
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
            upd_other _ _ _ (by omega)]; exact j5 j hj
        · rw [upd_same]
      · rw [hm', upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
          upd_other _ _ _ (by omega)]; exact j6 a ha
      · obtain ⟨a1, a2⟩ := j7 j (by omega) hj2
        refine ⟨?_, ?_⟩
        · rw [hm', upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
            upd_other _ _ _ (by omega)]; exact a1
        · rw [hm', upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
            upd_other _ _ _ (by omega)]; exact a2)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, by rw [j1 _ (by omega), g0], j2, j3, j4, j5, j6,
    fun x hx => by rw [j1 x (by omega), q x (by omega)], by rw [j7, gr₁], by rw [j8, grm₁],
    by rw [j9, go₁]⟩

end Exec

/-! ### The third scan: the compacted arrays -/

/-- The loads of the third scan: `f = [NF[i] ≠ 0]`, `k = RK[i]`, `rv = RV[i]`, `RK[rv]`,
`[NF[rv] ≠ 0]`, `EX[i]`. -/
def mc3Load : Stmt :=
  block [.addN 5013 5001 5011, .loadN 5013 5013, .divN 5013 5013 5013,
    .addN 5014 5004 5011, .loadN 5014 5014,
    .addN 5015 5003 5011, .loadN 5015 5015,
    .addN 5016 5004 5015, .loadN 5016 5016,
    .addN 5017 5001 5015, .loadN 5017 5017, .divN 5017 5017 5017,
    .addN 5025 5008 5011, .loadN 5025 5025]

/-- The writes of a dart of `N`: `CR[k] := RK[rv]`, `CS[k] := RK[NX[i]]`, `CE[k] := EX[i]`, the
sum, the count of reverses off `N`. -/
def mc3Put : Stmt :=
  block [.addN 5023 5005 5011, .loadN 5023 5023,
    .addN 5024 5004 5023, .loadN 5024 5024,
    .addN 5026 5009 5014, .storeN 5026 5016,
    .addN 5026 5018 5014, .storeN 5026 5024,
    .addN 5026 5019 5014, .storeN 5026 5025,
    .addN 5021 5021 5025, .subN 5027 5010 5017, .addN 5022 5022 5027]

/-- One index of the third scan (`5020 = 0`). -/
def mc3Body : Stmt :=
  .seq mc3Load (.seq (.ifLtN 5020 5013 mc3Put .skip) (block [.addN 5011 5011 5010]))

/-- **The third scan.** -/
def mc3 : Stmt :=
  .seq (block [.constN 5011 0, .constN 5020 0, .constN 5021 0, .constN 5022 0])
    (.whileLtN 5011 5000 mc3Body)

section Exec3

variable {P : Input} {W : ℕ}

theorem mc3Load_exec (c : Config) (hc : WordsBounded W c) {NFb RVb RKb EXb i rv : ℕ}
    (r1 : c.nreg 5001 = NFb) (r3 : c.nreg 5003 = RVb) (r4 : c.nreg 5004 = RKb)
    (r8 : c.nreg 5008 = EXb) (r11 : c.nreg 5011 = i) (hrv : c.nmem (RVb + i) = rv)
    (w1 : NFb + i ≤ W) (w2 : RKb + i ≤ W) (w3 : RVb + i ≤ W) (w4 : RKb + rv ≤ W)
    (w5 : NFb + rv ≤ W) (w6 : EXb + i ≤ W) :
    ∃ c' t, Exec P W mc3Load c c' t ∧ t = 14 ∧
      c'.nreg 5013 = mcF c.nmem NFb i ∧ c'.nreg 5014 = c.nmem (RKb + i) ∧
      c'.nreg 5015 = rv ∧ c'.nreg 5016 = c.nmem (RKb + rv) ∧
      c'.nreg 5017 = c.nmem (NFb + rv) / c.nmem (NFb + rv) ∧ c'.nreg 5025 = c.nmem (EXb + i) ∧
      c'.nmem = c.nmem ∧
      (∀ x, (x < 5013 ∨ (5017 < x ∧ x < 5025) ∨ 5025 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold mc3Load
  exec_block
  all_goals try (config_simp; simp only [r1, r3, r4, r8, r11, hrv]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals try (config_simp; simp only [r1, r3, r4, r8, r11, hrv]; done)
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem mc3Put_exec (c : Config) (hc : WordsBounded W c) {NXb RKb CRb CSb CEb i k nx S bd : ℕ}
    (r4 : c.nreg 5004 = RKb) (r5 : c.nreg 5005 = NXb) (r9 : c.nreg 5009 = CRb)
    (r18 : c.nreg 5018 = CSb) (r19 : c.nreg 5019 = CEb) (r10 : c.nreg 5010 = 1)
    (r11 : c.nreg 5011 = i) (r14 : c.nreg 5014 = k) (r21 : c.nreg 5021 = S)
    (r22 : c.nreg 5022 = bd) (hnx : c.nmem (NXb + i) = nx)
    (w1 : NXb + i ≤ W) (w2 : RKb + nx ≤ W) (w3 : CRb + k ≤ W) (w4 : CSb + k ≤ W)
    (w5 : CEb + k ≤ W) (w6 : S + c.nreg 5025 ≤ W) (w7 : bd + 1 ≤ W) :
    ∃ c' t, Exec P W mc3Put c c' t ∧ t = 13 ∧
      c'.nreg 5021 = S + c.nreg 5025 ∧ c'.nreg 5022 = bd + (1 - c.nreg 5017) ∧
      c'.nmem = upd (upd (upd c.nmem (CRb + k) (c.nreg 5016)) (CSb + k) (c.nmem (RKb + nx)))
        (CEb + k) (c.nreg 5025) ∧
      (∀ x, (x < 5021 ∨ 5027 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold mc3Put
  exec_block
  all_goals try (config_simp; simp only [r4, r5, r9, r18, r19, r10, r11, r14, r21, r22, hnx]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r21]
  · config_simp; simp only [r22, r10]
  · config_simp; simp only [r4, r5, r9, r18, r19, r10, r11, r14, hnx]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem mc3Body_exec (c : Config) (hc : WordsBounded W c)
    {NFb RVb RKb EXb NXb CRb CSb CEb i rv S bd : ℕ}
    (r1 : c.nreg 5001 = NFb) (r3 : c.nreg 5003 = RVb) (r4 : c.nreg 5004 = RKb)
    (r5 : c.nreg 5005 = NXb) (r8 : c.nreg 5008 = EXb) (r9 : c.nreg 5009 = CRb)
    (r18 : c.nreg 5018 = CSb) (r19 : c.nreg 5019 = CEb) (r10 : c.nreg 5010 = 1)
    (r20 : c.nreg 5020 = 0) (r11 : c.nreg 5011 = i) (r21 : c.nreg 5021 = S)
    (r22 : c.nreg 5022 = bd) (hrv : c.nmem (RVb + i) = rv)
    (w1 : NFb + i ≤ W) (w2 : RKb + i ≤ W) (w3 : RVb + i ≤ W) (w4 : RKb + rv ≤ W)
    (w5 : NFb + rv ≤ W) (w6 : EXb + i ≤ W) (w7 : NXb + i ≤ W)
    (w8 : mcF c.nmem NFb i = 1 → RKb + c.nmem (NXb + i) ≤ W)
    (w9 : CRb + c.nmem (RKb + i) ≤ W) (w10 : CSb + c.nmem (RKb + i) ≤ W)
    (w11 : CEb + c.nmem (RKb + i) ≤ W) (w12 : S + c.nmem (EXb + i) ≤ W) (w13 : bd + 1 ≤ W)
    (w14 : i + 1 ≤ W) :
    ∃ c' t, Exec P W mc3Body c c' t ∧ t ≤ 30 ∧ c'.nreg 5011 = i + 1 ∧
      c'.nreg 5021 = S + mcF c.nmem NFb i * c.nmem (EXb + i) ∧
      c'.nreg 5022 = bd + mcF c.nmem NFb i * (1 - mcF c.nmem NFb rv) ∧
      (c'.nmem = if mcF c.nmem NFb i = 1 then
        upd (upd (upd c.nmem (CRb + c.nmem (RKb + i)) (c.nmem (RKb + rv)))
          (CSb + c.nmem (RKb + i)) (c.nmem (RKb + c.nmem (NXb + i))))
          (CEb + c.nmem (RKb + i)) (c.nmem (EXb + i))
        else c.nmem) ∧
      (∀ x, (x < 5011 ∨ x = 5012 ∨ (5017 < x ∧ x < 5021) ∨ 5027 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hF := mcF_le c.nmem NFb i
  obtain ⟨c₁, t₁, e₁, ht₁, a13, a14, a15, a16, a17, a25, am₁, an₁, ar₁, arm₁, ao₁⟩ :=
    mc3Load_exec (P := P) c hc r1 r3 r4 r8 r11 hrv w1 w2 w3 w4 w5 w6
  have hw₁ := e₁.wb_right
  have k : ∀ x, (x < 5013 ∨ (5017 < x ∧ x < 5025) ∨ 5025 < x) → c₁.nreg x = c.nreg x := an₁
  -- the branch
  obtain ⟨c₂, t₂, e₂, ht₂, b21, b22, bm₂, bn₂, br₂, brm₂, bo₂⟩ : ∃ c₂ t₂,
      Exec P W (.ifLtN 5020 5013 mc3Put .skip) c₁ c₂ t₂ ∧ t₂ ≤ 15 ∧
      c₂.nreg 5021 = S + mcF c.nmem NFb i * c.nmem (EXb + i) ∧
      c₂.nreg 5022 = bd + mcF c.nmem NFb i * (1 - mcF c.nmem NFb rv) ∧
      (c₂.nmem = if mcF c.nmem NFb i = 1 then
        upd (upd (upd c.nmem (CRb + c.nmem (RKb + i)) (c.nmem (RKb + rv)))
          (CSb + c.nmem (RKb + i)) (c.nmem (RKb + c.nmem (NXb + i))))
          (CEb + c.nmem (RKb + i)) (c.nmem (EXb + i))
        else c.nmem) ∧
      (∀ x, (x < 5021 ∨ 5027 < x) → c₂.nreg x = c₁.nreg x) ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hF with h0 | h1
    · refine ⟨c₁, 0 + 2, .ifLtN_false (by rw [k _ (by omega), r20, a13, h0]; omega) (.skip hw₁),
        by omega, ?_, ?_, ?_, fun _ _ => rfl, rfl, rfl, rfl⟩
      · rw [k _ (by omega), r21, h0]; simp
      · rw [k _ (by omega), r22, h0]; simp
      · rw [am₁, h0]; simp
    · have hg := mcF_le c.nmem NFb rv
      obtain ⟨c₂, t₂, e₂, ht₂, p21, p22, pm, pn, pr, prm, po⟩ :=
        mc3Put_exec (P := P) c₁ hw₁ (k := c.nmem (RKb + i)) (nx := c.nmem (NXb + i))
          (S := S) (bd := bd)
          (by rw [k _ (by omega), r4]) (by rw [k _ (by omega), r5])
          (by rw [k _ (by omega), r9]) (by rw [k _ (by omega), r18])
          (by rw [k _ (by omega), r19]) (by rw [k _ (by omega), r10])
          (by rw [k _ (by omega), r11]) a14 (by rw [k _ (by omega), r21])
          (by rw [k _ (by omega), r22]) (by rw [am₁]) w7 (w8 h1) w9 w10 w11
          (by rw [a25]; exact w12) w13
      refine ⟨c₂, t₂ + 1, .ifLtN_true (by rw [k _ (by omega), r20, a13, h1]; omega) e₂,
        by omega, ?_, ?_, ?_, pn, pr, prm, po⟩
      · rw [p21, a25, h1, one_mul]
      · rw [p22, a17, h1, one_mul]
      · rw [pm, a16, a25, am₁, h1]; simp
  have hw₂ := e₂.wb_right
  obtain ⟨c₃, t₃, e₃, ht₃, d11, dn₃, dm₃, dr₃, drm₃, do₃⟩ : ∃ c₃ t₃,
      Exec P W (block [.addN 5011 5011 5010]) c₂ c₃ t₃ ∧ t₃ = 1 ∧ c₃.nreg 5011 = i + 1 ∧
      (∀ x, x ≠ 5011 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have h11 : c₂.nreg 5011 = i := by rw [bn₂ _ (by omega), k _ (by omega), r11]
    have h10 : c₂.nreg 5010 = 1 := by rw [bn₂ _ (by omega), k _ (by omega), r10]
    exec_block
    all_goals try (config_simp; simp only [h11, h10]; omega)
    refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [h11, h10]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, d11, ?_, ?_, ?_, fun x hx => ?_,
    by rw [dr₃, br₂, ar₁], by rw [drm₃, brm₂, arm₁], by rw [do₃, bo₂, ao₁]⟩
  · rw [dn₃ _ (by omega), b21]
  · rw [dn₃ _ (by omega), b22]
  · rw [dm₃, bm₂]
  · rw [dn₃ _ (by omega), bn₂ _ (by omega), k _ (by omega)]

lemma sum_mul_mcF_le (m : ℕ → ℕ) (NFb : ℕ) (x : ℕ → ℕ) (i : ℕ) :
    ∑ j ∈ range i, mcF m NFb j * x j ≤ ∑ j ∈ range i, x j :=
  sum_le_sum fun j _ => by
    have := mcF_le m NFb j
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with h | h <;> rw [h] <;> omega

lemma sum_range_mono' (x : ℕ → ℕ) {i n : ℕ} (h : i ≤ n) :
    ∑ j ∈ range i, x j ≤ ∑ j ∈ range n, x j :=
  sum_le_sum_of_subset (range_subset_range.2 h)

/-- The ranks grow past a dart of `N`. -/
lemma rk_lt_of (m : ℕ → ℕ) (NFb : ℕ) {j i : ℕ} (hji : j < i) (hF : mcF m NFb j = 1) :
    ∑ l ∈ range j, mcF m NFb l < ∑ l ∈ range i, mcF m NFb l := by
  have h1 := sum_range_mono' (mcF m NFb) (show j + 1 ≤ i by omega)
  rw [sum_range_succ, hF] at h1
  omega

/-- **The third scan**: for the darts of `N` (`[NF[j] ≠ 0] = 1`, rank `RK[j]`), within
`32 n + 6` steps `CR[RK[j]] = RK[RV[j]]`, `CS[RK[j]] = RK[NX[j]]`, `CE[RK[j]] = EX[j]`; the sum
`r5021 = Σ_j [NF[j] ≠ 0] EX[j]`, the count `r5022 = Σ_j [NF[j] ≠ 0] (1 - [NF[RV[j]] ≠ 0])`;
memory outside `[CRb, CEb + n)`, registers outside `5011 … 5017`, `5020 … 5027`, reals and
output kept. -/
theorem mc3_exec (c : Config) (hc : WordsBounded W c) {n NFb RVb RKb EXb NXb CRb CSb CEb : ℕ}
    (r0 : c.nreg 5000 = n) (r1 : c.nreg 5001 = NFb) (r3 : c.nreg 5003 = RVb)
    (r4 : c.nreg 5004 = RKb) (r5 : c.nreg 5005 = NXb) (r8 : c.nreg 5008 = EXb)
    (r9 : c.nreg 5009 = CRb) (r18 : c.nreg 5018 = CSb) (r19 : c.nreg 5019 = CEb)
    (r10 : c.nreg 5010 = 1)
    (lay : NFb + n ≤ CRb ∧ RVb + n ≤ CRb ∧ RKb + n ≤ CRb ∧ NXb + n ≤ CRb ∧ EXb + n ≤ CRb ∧
      CRb + n ≤ CSb ∧ CSb + n ≤ CEb ∧ CEb + n + 1 ≤ W)
    (hRK : ∀ j < n, c.nmem (RKb + j) = ∑ l ∈ range j, mcF c.nmem NFb l)
    (hRV : ∀ j < n, c.nmem (RVb + j) < n)
    (hNX : ∀ j < n, mcF c.nmem NFb j = 1 → c.nmem (NXb + j) < n)
    (hS : ∑ j ∈ range n, c.nmem (EXb + j) ≤ W) :
    ∃ c' t, Exec P W mc3 c c' t ∧ t ≤ 32 * n + 6 ∧
      c'.nreg 5021 = ∑ j ∈ range n, mcF c.nmem NFb j * c.nmem (EXb + j) ∧
      c'.nreg 5022 = ∑ j ∈ range n, mcF c.nmem NFb j * (1 - mcF c.nmem NFb (c.nmem (RVb + j))) ∧
      (∀ j < n, mcF c.nmem NFb j = 1 →
        c'.nmem (CRb + c.nmem (RKb + j)) = c.nmem (RKb + c.nmem (RVb + j)) ∧
        c'.nmem (CSb + c.nmem (RKb + j)) = c.nmem (RKb + c.nmem (NXb + j)) ∧
        c'.nmem (CEb + c.nmem (RKb + j)) = c.nmem (EXb + j)) ∧
      (∀ a, (a < CRb ∨ CEb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 5011 ∨ x = 5012 ∨ (5017 < x ∧ x < 5020) ∨ 5027 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := lay
  unfold mc3
  obtain ⟨c₁, k₁, e₁, hk₁, g1, g20, g21, g22, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 5011 0, .constN 5020 0, .constN 5021 0, .constN 5022 0]) c c₁ k₁ ∧
      k₁ = 4 ∧ c₁.nreg 5011 = 0 ∧ c₁.nreg 5020 = 0 ∧ c₁.nreg 5021 = 0 ∧ c₁.nreg 5022 = 0 ∧
      (∀ x, x ≠ 5011 → x ≠ 5020 → x ≠ 5021 → x ≠ 5022 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun x a1 a2 a3 a4 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; done)
    simp only [Config.nreg_mk, upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3,
      upd_other _ _ _ a4]
  have hw₁ := e₁.wb_right
  have q : ∀ x, (x < 5011 ∨ (5011 < x ∧ x < 5020) ∨ 5022 < x) → c₁.nreg x = c.nreg x :=
    fun x hx => gn₁ x (by omega) (by omega) (by omega) (by omega)
  set m₀ := c.nmem with hm₀
  set F : ℕ → ℕ := fun j => mcF m₀ NFb j with hFdef
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 5011 ∨ x = 5012 ∨ (5017 < x ∧ x < 5021) ∨ 5027 < x) → c'.nreg x = c₁.nreg x) ∧
    c'.nreg 5021 = ∑ j ∈ range i, F j * m₀ (EXb + j) ∧
    c'.nreg 5022 = ∑ j ∈ range i, F j * (1 - mcF m₀ NFb (m₀ (RVb + j))) ∧
    (∀ j < i, F j = 1 →
        c'.nmem (CRb + m₀ (RKb + j)) = m₀ (RKb + m₀ (RVb + j)) ∧
        c'.nmem (CSb + m₀ (RKb + j)) = m₀ (RKb + m₀ (NXb + j)) ∧
        c'.nmem (CEb + m₀ (RKb + j)) = m₀ (EXb + j)) ∧
    (∀ a, (a < CRb ∨ CEb + n ≤ a) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h11, j1, j2, j3, j4, j5, j6, j7, j8⟩ := tgRange (P := P)
    (a := 5011) (b := 5000) (body := mc3Body) J (B := 30) c₁ hw₁ g1
    (by rw [q _ (by omega), r0]) (Nat.zero_le n)
    ⟨fun _ _ => rfl, by rw [g21]; rfl, by rw [g22]; rfl, fun j hj => absurd hj (by omega),
      fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h11 h00 ⟨j1, j2, j3, j4, j5, j6, j7, j8⟩ => by
      have f : ∀ x, (x < 5011 ∨ x = 5012 ∨ (5017 < x ∧ x < 5021) ∨ 5027 < x) → c'.nreg x = c₁.nreg x := j1
      have mi : ∀ a, a < CRb → c'.nmem a = m₀ a := fun a ha => j5 a (Or.inl ha)
      have hrv := hRV i hhi
      have hrk : m₀ (RKb + i) ≤ i := by rw [hRK i hhi]; exact sum_mcF_le m₀ NFb i
      have hSi : ∑ j ∈ range i, F j * m₀ (EXb + j) + m₀ (EXb + i) ≤ W := by
        have h1 : ∑ j ∈ range i, F j * m₀ (EXb + j) ≤ ∑ j ∈ range i, m₀ (EXb + j) :=
          sum_mul_mcF_le m₀ NFb (fun j => m₀ (EXb + j)) i
        have h2 := sum_range_mono' (fun j => m₀ (EXb + j)) (show i + 1 ≤ n by omega)
        rw [sum_range_succ] at h2
        omega
      have hbd : ∑ j ∈ range i, F j * (1 - mcF m₀ NFb (m₀ (RVb + j))) ≤ i := by
        have := sum_mul_mcF_le m₀ NFb (fun j => 1 - mcF m₀ NFb (m₀ (RVb + j))) i
        refine this.trans ((sum_le_sum fun j _ => (Nat.sub_le 1 _)).trans (by simp))
      have hF' : mcF c'.nmem NFb i = F i := by
        simp only [hFdef, mcF]; rw [mi _ (by omega)]
      have hFrv : mcF c'.nmem NFb (m₀ (RVb + i)) = mcF m₀ NFb (m₀ (RVb + i)) := by
        simp only [mcF]; rw [mi _ (by omega)]
      obtain ⟨c'', t, ex, ht, h11', h21', h22', hm', hn', hr', hrm', ho'⟩ :=
        mc3Body_exec (P := P) c' hw (rv := m₀ (RVb + i)) (S := c'.nreg 5021)
          (bd := c'.nreg 5022)
          (by rw [f _ (by omega), q _ (by omega), r1]) (by rw [f _ (by omega), q _ (by omega), r3])
          (by rw [f _ (by omega), q _ (by omega), r4]) (by rw [f _ (by omega), q _ (by omega), r5])
          (by rw [f _ (by omega), q _ (by omega), r8]) (by rw [f _ (by omega), q _ (by omega), r9])
          (by rw [f _ (by omega), q _ (by omega), r18])
          (by rw [f _ (by omega), q _ (by omega), r19])
          (by rw [f _ (by omega), q _ (by omega), r10]) (by rw [f _ (by omega), g20]) h11 rfl rfl
          (mi _ (by omega)) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega)
          (fun h => by rw [hF'] at h; rw [mi _ (by omega)]; have := hNX i hhi h; omega)
          (by rw [mi _ (by omega)]; omega) (by rw [mi _ (by omega)]; omega)
          (by rw [mi _ (by omega)]; omega) (by rw [j2, mi _ (by omega)]; exact hSi)
          (by rw [j3]; omega) (by omega)
      have hk' : c'.nmem (RKb + i) = m₀ (RKb + i) := mi _ (by omega)
      rw [hk'] at hm'
      refine ⟨c'', t, ex, ht, h11', by rw [hn' _ (by omega)]; exact h00,
        fun x hx => by rw [hn' x hx, f x hx], ?_, ?_, fun j hj hFj => ?_, fun a ha => ?_,
        by rw [hr', j6], by rw [hrm', j7], by rw [ho', j8]⟩
      · rw [h21', j2, hF', mi _ (by omega), sum_range_succ]
      · rw [h22', j3, hF', hFrv, sum_range_succ]
      · rw [hm', hF']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · have hlt : m₀ (RKb + j) < m₀ (RKb + i) := by
            rw [hRK j (by omega), hRK i hhi]; exact rk_lt_of m₀ NFb hj hFj
          obtain ⟨a1, a2, a3⟩ := j4 j hj hFj
          split_ifs
          · refine ⟨?_, ?_, ?_⟩
            · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
                upd_other _ _ _ (by omega)]; exact a1
            · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
                upd_other _ _ _ (by omega)]; exact a2
            · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
                upd_other _ _ _ (by omega)]; exact a3
          · exact ⟨a1, a2, a3⟩
        · rw [iteT hFj, mi (RKb + m₀ (RVb + j)) (by omega),
            mi (NXb + j) (by omega),
            mi (RKb + m₀ (NXb + j)) (by have := hNX j hhi hFj; omega), mi (EXb + j) (by omega)]
          refine ⟨?_, ?_, ?_⟩
          · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_same]
          · rw [upd_other _ _ _ (by omega), upd_same]
          · rw [upd_same]
      · rw [hm']
        split_ifs
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
            upd_other _ _ _ (by omega)]; exact j5 a ha
        · exact j5 a ha)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3, j4, j5,
    fun x hx => by rw [j1 x (by omega), q x (by omega)], by rw [j6, gr₁], by rw [j7, grm₁],
    by rw [j8, go₁]⟩

end Exec3

/-! ### The scans compute the ranks, the count, the sum -/

section Pure

open Orbit

variable {α : Type*} [DecidableEq α] {e : ℕ → α} {n : ℕ} {N : Finset α}

lemma mcF_eq {m : ℕ → ℕ} {NFb : ℕ} (hNF : ∀ i < n, (m (NFb + i) ≠ 0 ↔ e i ∈ N)) {j : ℕ}
    (hj : j < n) : mcF m NFb j = if e j ∈ N then 1 else 0 := by
  unfold mcF; rw [sgn_eq]
  by_cases h : e j ∈ N
  · rw [iteT h, iteF ((hNF j hj).2 h)]
  · rw [iteF h, iteT (by by_contra h'; exact h ((hNF j hj).1 h'))]

lemma sum_mcF_card {m : ℕ → ℕ} {NFb : ℕ} (hNF : ∀ i < n, (m (NFb + i) ≠ 0 ↔ e i ∈ N)) (i : ℕ)
    (hi : i ≤ n) : ∑ j ∈ range i, mcF m NFb j = #((range i).filter fun j => e j ∈ N) := by
  rw [card_filter]
  exact sum_congr rfl fun j hj => mcF_eq hNF (by rw [mem_range] at hj; omega)

lemma card_filter_e (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j)
    (hsurj : ∀ d ∈ N, ∃ i, i < n ∧ e i = d) : #((range n).filter fun j => e j ∈ N) = #N := by
  refine card_nbij' e (eIdx e n) (fun j hj => ?_) (fun y hy => ?_) (fun j hj => ?_)
    (fun y hy => ?_)
  · simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at hj ⊢; exact hj.2
  · simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at hy ⊢
    exact ⟨(eIdx_spec (hsurj _ hy)).1, by rw [(eIdx_spec (hsurj _ hy)).2]; exact hy⟩
  · simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at hj
    exact eIdx_e hinj hj.1
  · exact (eIdx_spec (hsurj _ hy)).2

lemma sum_filter_e (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j)
    (hsurj : ∀ d ∈ N, ∃ i, i < n ∧ e i = d) (f : α → ℕ) :
    ∑ j ∈ (range n).filter (fun j => e j ∈ N), f (e j) = ∑ d ∈ N, f d := by
  refine sum_nbij' e (eIdx e n) (fun j hj => ?_) (fun y hy => ?_) (fun j hj => ?_)
    (fun y hy => ?_) (fun j _ => rfl)
  · simp only [mem_filter, mem_range] at hj ⊢; exact hj.2
  · simp only [mem_filter, mem_range] at hy ⊢
    exact ⟨(eIdx_spec (hsurj _ hy)).1, by rw [(eIdx_spec (hsurj _ hy)).2]; exact hy⟩
  · simp only [mem_filter, mem_range] at hj
    exact eIdx_e hinj hj.1
  · exact (eIdx_spec (hsurj _ hy)).2

lemma sum_mcF_mul {m : ℕ → ℕ} {NFb : ℕ} (hNF : ∀ i < n, (m (NFb + i) ≠ 0 ↔ e i ∈ N))
    (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j) (hsurj : ∀ d ∈ N, ∃ i, i < n ∧ e i = d)
    (f : α → ℕ) : ∑ j ∈ range n, mcF m NFb j * f (e j) = ∑ d ∈ N, f d := by
  rw [← sum_filter_e hinj hsurj f, sum_filter]
  exact sum_congr rfl fun j hj => by
    rw [mcF_eq hNF (mem_range.1 hj)]; split_ifs <;> simp

lemma sum_mcF_bad {m : ℕ → ℕ} {NFb : ℕ} (hNF : ∀ i < n, (m (NFb + i) ≠ 0 ↔ e i ∈ N))
    (hsurj : ∀ d ∈ N, ∃ i, i < n ∧ e i = d) {ι : α → α} {rv : ℕ → ℕ}
    (hrv : ∀ i < n, rv i < n ∧ e (rv i) = ι (e i)) :
    ∑ j ∈ range n, mcF m NFb j * (1 - mcF m NFb (rv j)) = 0 ↔ ∀ d ∈ N, ι d ∈ N := by
  rw [sum_eq_zero_iff]
  constructor
  · intro h d hd
    obtain ⟨i, hi, rfl⟩ := hsurj d hd
    have := h i (mem_range.2 hi)
    rw [mcF_eq hNF hi, iteT hd, one_mul, mcF_eq hNF (hrv i hi).1, (hrv i hi).2] at this
    by_contra h'
    rw [iteF h'] at this; omega
  · intro h j hj
    rw [mem_range] at hj
    rw [mcF_eq hNF hj, mcF_eq hNF (hrv j hj).1, (hrv j hj).2]
    split_ifs with h1 h2
    · rfl
    · exact absurd (h _ h1) h2
    · simp
    · simp

end Pure


/-! ### The whole preparation -/

/-- The bases of the arrays from `Hb = r5004`: `NX`, `DF`, `PR`, `CR`, `CS`, `CE`. -/
def mcSet : Stmt :=
  block [.addN 5005 5004 5000, .addN 5006 5005 5000, .addN 5007 5006 5000,
    .addN 5009 5007 5000, .addN 5018 5009 5000, .addN 5019 5018 5000]

/-- The registers of `lsProg`: `PR[SG[i]] := i` for all `i < n` (`FL = SG < n = thr`). -/
def mcLs : Stmt :=
  block [.copyN 6220 5000, .copyN 6221 5002, .copyN 6222 5002, .copyN 6223 5000,
    .copyN 6224 5007]

/-- The registers of `ldProg`. -/
def mcLd : Stmt := block [.copyN 6240 5000, .copyN 6241 5006, .copyN 6242 5005, .copyN 6243 5007]

/-- **The compacted index arrays of the piece map.** -/
def mcProg : Stmt :=
  .seq (.seq mcSet mc1) (.seq (.seq mcLs (.seq lsProg (.seq mcLd ldProg))) mc3)

section ExecAll

open Orbit

variable {P : Input} {W : ℕ}

/-- The bases and the first scan. -/
theorem mcA_exec (c : Config) (hc : WordsBounded W c) {n NFb SGb Hb : ℕ}
    (r0 : c.nreg 5000 = n) (r1 : c.nreg 5001 = NFb) (r2 : c.nreg 5002 = SGb)
    (r4 : c.nreg 5004 = Hb)
    (lay : NFb + n ≤ Hb ∧ SGb + n ≤ Hb ∧ Hb + 7 * n + 1 ≤ W) :
    ∃ c' t, Exec P W (.seq mcSet mc1) c c' t ∧ t ≤ 16 * n + 11 ∧
      c'.nreg 5005 = Hb + n ∧ c'.nreg 5006 = Hb + 2 * n ∧
      c'.nreg 5007 = Hb + 3 * n ∧ c'.nreg 5009 = Hb + 4 * n ∧ c'.nreg 5018 = Hb + 5 * n ∧
      c'.nreg 5019 = Hb + 6 * n ∧ c'.nreg 5010 = 1 ∧
      c'.nreg 5012 = ∑ j ∈ range n, mcF c.nmem NFb j ∧
      (∀ j < n, c'.nmem (Hb + j) = ∑ l ∈ range j, mcF c.nmem NFb l) ∧
      (∀ j < n, c'.nmem (Hb + n + j) = c.nmem (SGb + j)) ∧
      (∀ j < n, c'.nmem (Hb + 2 * n + j) = 1 - mcF c.nmem NFb j) ∧
      (∀ a, (a < Hb ∨ Hb + 3 * n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 5005 ∨ x = 5008 ∨ x = 5017 ∨ 5019 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l5⟩ := lay
  obtain ⟨c₁, k₁, e₁, hk₁, a5, a6, a7, a9, a18, a19, an₁, am₁, ar₁, arm₁, ao₁⟩ : ∃ c₁ k₁,
      Exec P W mcSet c c₁ k₁ ∧ k₁ = 6 ∧ c₁.nreg 5005 = Hb + n ∧ c₁.nreg 5006 = Hb + 2 * n ∧
      c₁.nreg 5007 = Hb + 3 * n ∧ c₁.nreg 5009 = Hb + 4 * n ∧ c₁.nreg 5018 = Hb + 5 * n ∧
      c₁.nreg 5019 = Hb + 6 * n ∧
      (∀ x, (x < 5005 ∨ (5007 < x ∧ x < 5009) ∨ (5009 < x ∧ x < 5018) ∨ 5019 < x) →
        c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold mcSet
    exec_block
    all_goals try (config_simp; simp only [r0, r4]; omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => by
      obtain ⟨b1, b2, b3, b4, b5, b6⟩ : x ≠ 5005 ∧ x ≠ 5006 ∧ x ≠ 5007 ∧ x ≠ 5009 ∧ x ≠ 5018 ∧
          x ≠ 5019 := by omega
      simp only [Config.nreg_mk, upd_other _ _ _ b1, upd_other _ _ _ b2, upd_other _ _ _ b3,
        upd_other _ _ _ b4, upd_other _ _ _ b5, upd_other _ _ _ b6], rfl, rfl, rfl, rfl⟩
    all_goals (config_simp; try simp only [r0, r4]; try omega)
  have hw₁ := e₁.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, b10, b12, bRK, bNX, bDF, bm₂, bn₂, br₂, brm₂, bo₂⟩ :=
    mc1_exec (P := P) c₁ hw₁ (n := n) (NFb := NFb) (SGb := SGb) (RKb := Hb) (NXb := Hb + n)
      (DFb := Hb + 2 * n) (by rw [an₁ _ (by omega), r0]) (by rw [an₁ _ (by omega), r1])
      (by rw [an₁ _ (by omega), r2]) (by rw [an₁ _ (by omega), r4]) a5 a6
      ⟨by omega, by omega, by omega, by omega, by omega⟩
  rw [am₁] at bRK bNX bDF bm₂ b12
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, by rw [bn₂ _ (by omega), a5],
    by rw [bn₂ _ (by omega), a6], by rw [bn₂ _ (by omega), a7], by rw [bn₂ _ (by omega), a9],
    by rw [bn₂ _ (by omega), a18], by rw [bn₂ _ (by omega), a19], b10, b12, bRK, bNX, bDF,
    fun a ha => bm₂ a (by omega), fun x hx => by rw [bn₂ _ (by omega), an₁ _ (by omega)],
    by rw [br₂, ar₁], by rw [brm₂, arm₁], by rw [bo₂, ao₁]⟩

/-- The inverse scatter and the deletion: `NX` represents `ret τ N`. -/
theorem mcB_exec {α : Type*} [Fintype α] [DecidableEq α] (c : Config) (hc : WordsBounded W c)
    {n SGb Hb : ℕ} {e : ℕ → α} {B N : Finset α} {τ : Equiv.Perm α}
    (r0 : c.nreg 5000 = n) (r2 : c.nreg 5002 = SGb) (r5 : c.nreg 5005 = Hb + n)
    (r6 : c.nreg 5006 = Hb + 2 * n) (r7 : c.nreg 5007 = Hb + 3 * n)
    (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j) (hBe : ∀ i < n, e i ∈ B)
    (hB : ∀ d ∈ B, ∃ i, i < n ∧ e i = d) (hNB : N ⊆ B) (hτB : Stable τ B)
    (hSG : ∀ i < n, c.nmem (SGb + i) < n ∧ e (c.nmem (SGb + i)) = τ (e i))
    (hNX : ∀ i < n, c.nmem (Hb + n + i) = c.nmem (SGb + i))
    (hDF : ∀ i < n, c.nmem (Hb + 2 * n + i) = if e i ∈ N then 0 else 1)
    (lay : SGb + n ≤ Hb ∧ Hb + 7 * n + 1 ≤ W) :
    ∃ c' t, Exec P W (.seq mcLs (.seq lsProg (.seq mcLd ldProg))) c c' t ∧ t ≤ 25 * n + 18 ∧
      RetRep e n τ N c'.nmem (Hb + n) (Hb + 3 * n) ∧
      (∀ a, (a < Hb + n ∨ (Hb + 2 * n ≤ a ∧ a < Hb + 3 * n) ∨ Hb + 4 * n ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6220 ∨ 6250 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l2, l5⟩ := lay
  obtain ⟨c₃, k₃, e₃, hk₃, s20, s21, s22, s23, s24, sn₃, sm₃, sr₃, srm₃, so₃⟩ : ∃ c₃ k₃,
      Exec P W mcLs c c₃ k₃ ∧ k₃ = 5 ∧ c₃.nreg 6220 = n ∧ c₃.nreg 6221 = SGb ∧
      c₃.nreg 6222 = SGb ∧ c₃.nreg 6223 = n ∧ c₃.nreg 6224 = Hb + 3 * n ∧
      (∀ x, (x < 6220 ∨ 6224 < x) → c₃.nreg x = c.nreg x) ∧ c₃.nmem = c.nmem ∧
      c₃.rreg = c.rreg ∧ c₃.rmem = c.rmem ∧ c₃.output = c.output := by
    unfold mcLs
    exec_block
    all_goals try (config_simp; simp only [r0, r2, r7]; omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; simp only [r0, r2, r7]; done)
    config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₃ := e₃.wb_right
  rw [← sm₃] at hSG hNX hDF
  obtain ⟨c₄, k₄, e₄, hk₄, pPR, pm₄, pn₄, pr₄, prm₄, po₄⟩ :=
    lsProg_exec (P := P) c₃ hw₃ s20 s21 s22 s23 s24 (by omega) (by omega) (by omega)
      (fun j hj _ => by have := (hSG j hj).1; omega)
      (fun i hi j hj _ _ h => by
        have h2 : τ (e i) = τ (e j) := by rw [← (hSG i hi).2, ← (hSG j hj).2, h]
        exact hinj i hi j hj (τ.injective h2))
      (fun i hi _ j hj => by have := (hSG i hi).1; omega)
      (fun i hi _ j hj => by have := (hSG i hi).1; omega)
  have hw₄ := e₄.wb_right
  have hPR : ∀ i < n, c₄.nmem (Hb + 3 * n + c₃.nmem (SGb + i)) = i := fun i hi =>
    pPR i hi (hSG i hi).1
  have m₄ : ∀ a, (a < Hb + 3 * n ∨ Hb + 4 * n ≤ a) → c₄.nmem a = c₃.nmem a := fun a ha =>
    pm₄ a (fun i hi _ => by have := (hSG i hi).1; omega)
  obtain ⟨c₅, k₅, e₅, hk₅, d40, d41, d42, d43, dn₅, dm₅, dr₅, drm₅, do₅⟩ : ∃ c₅ k₅,
      Exec P W mcLd c₄ c₅ k₅ ∧ k₅ = 4 ∧ c₅.nreg 6240 = n ∧ c₅.nreg 6241 = Hb + 2 * n ∧
      c₅.nreg 6242 = Hb + n ∧ c₅.nreg 6243 = Hb + 3 * n ∧
      (∀ x, (x < 6240 ∨ 6243 < x) → c₅.nreg x = c₄.nreg x) ∧ c₅.nmem = c₄.nmem ∧
      c₅.rreg = c₄.rreg ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output := by
    have t0 : c₄.nreg 5000 = n := by rw [pn₄ _ (by omega), sn₃ _ (by omega), r0]
    have t5 : c₄.nreg 5005 = Hb + n := by rw [pn₄ _ (by omega), sn₃ _ (by omega), r5]
    have t6 : c₄.nreg 5006 = Hb + 2 * n := by rw [pn₄ _ (by omega), sn₃ _ (by omega), r6]
    have t7 : c₄.nreg 5007 = Hb + 3 * n := by rw [pn₄ _ (by omega), sn₃ _ (by omega), r7]
    unfold mcLd
    exec_block
    all_goals try (config_simp; simp only [t0, t5, t6, t7]; omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; simp only [t0, t5, t6, t7]; done)
    config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₅ := e₅.wb_right
  have hNX₅ : ∀ i < n, c₅.nmem (Hb + n + i) = c₃.nmem (SGb + i) := fun i hi => by
    rw [dm₅, m₄ _ (by omega), hNX i hi]
  have hrep : RetRep e n τ B c₅.nmem (Hb + n) (Hb + 3 * n) :=
    retRep_init hinj hB hτB (fun i hi _ => by rw [hNX₅ i hi]; exact hSG i hi)
      (fun i hi _ => by rw [hNX₅ i hi, dm₅]; exact hPR i hi)
  have hDF₅ : ∀ j < n, c₅.nmem (Hb + 2 * n + j) = if e j ∈ N then 0 else 1 := fun j hj => by
    rw [dm₅, m₄ _ (by omega), hDF j hj]
  obtain ⟨c₆, k₆, e₆, hk₆, lrep, lm₆, ln₆, lr₆, lrm₆, lo₆⟩ :=
    ldProg_exec (P := P) c₅ hw₅ d40 d41 d42 d43 (by omega) (by omega) (by omega) (by omega)
      (fun j hj k hk => by omega) (fun j hj k hk => by omega) (fun j hj k hk => by omega)
      hinj (fun j hj _ => hBe j hj) hrep
  have hdset : dset e (fun j => c₅.nmem (Hb + 2 * n + j)) B n = N := by
    rw [dset_eq_sdiff (L := B \ N) hB (fun i hi => by
      rw [hDF₅ i hi]
      by_cases h : e i ∈ N
      · rw [iteT h, iteF (fun h' => (mem_sdiff.1 h').2 h)]
      · rw [iteF h, iteT (mem_sdiff.2 ⟨hBe i hi, h⟩)])]
    rw [sdiff_sdiff_right_self, inf_eq_inter, inter_eq_right.2 hNB]
  rw [hdset] at lrep
  refine ⟨c₆, k₃ + (k₄ + (k₅ + k₆)), .seq e₃ (.seq e₄ (.seq e₅ e₆)), by omega, lrep,
    fun a ha => ?_, fun x hx => ?_, by rw [lr₆, dr₅, pr₄, sr₃], by rw [lrm₆, drm₅, prm₄, srm₃],
    by rw [lo₆, do₅, po₄, so₃]⟩
  · rw [lm₆ a (by omega) (by omega), dm₅, m₄ a (by omega), sm₃]
  · rw [ln₆ _ (by omega), dn₅ _ (by omega), pn₄ _ (by omega), sn₃ _ (by omega)]

set_option maxHeartbeats 1600000 in
/-- **The compacted index arrays**: with the enumeration `e` of `B` (injective on `[0, n)`),
`N ⊆ B`, flags `NF[i] ≠ 0 ↔ e i ∈ N`, the rotation array `SG` of `τ` (stable on `B`), the
reverse array `RV` of `ι`, the weights `EX[i] = ex (e i)`, all below `Hb`, within `75 n + 40`
steps: `RK[j] = eRk e n N (e j)` at `Hb` (the rank, i.e. `cNe`), and for every `e i ∈ N`
`CR[RK[i]] = eRk (ι (e i))`, `CS[RK[i]] = eRk (ret τ N (e i))`, `CE[RK[i]] = ex (e i)` (at
`Hb + 4n`, `Hb + 5n`, `Hb + 6n`); `r5012 = #N`, `r5021 = Σ_N ex`, `r5022 = 0 ↔ N` is closed
under `ι`; memory outside `[Hb, Hb + 7n)`, registers outside `5005 … 5029` and
`6220 … 6250`, reals and output kept. -/
theorem mcProg_exec {α : Type*} [Fintype α] [DecidableEq α] (c : Config) (hc : WordsBounded W c)
    {n NFb SGb RVb Hb EXb : ℕ} {e : ℕ → α} {B N : Finset α} {τ : Equiv.Perm α} {ι : α → α}
    {ex : α → ℕ}
    (r0 : c.nreg 5000 = n) (r1 : c.nreg 5001 = NFb) (r2 : c.nreg 5002 = SGb)
    (r3 : c.nreg 5003 = RVb) (r4 : c.nreg 5004 = Hb) (r8 : c.nreg 5008 = EXb)
    (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j) (hBe : ∀ i < n, e i ∈ B)
    (hB : ∀ d ∈ B, ∃ i, i < n ∧ e i = d) (hNB : N ⊆ B) (hτB : Stable τ B)
    (hNF : ∀ i < n, (c.nmem (NFb + i) ≠ 0 ↔ e i ∈ N))
    (hSG : ∀ i < n, c.nmem (SGb + i) < n ∧ e (c.nmem (SGb + i)) = τ (e i))
    (hRV : ∀ i < n, c.nmem (RVb + i) < n ∧ e (c.nmem (RVb + i)) = ι (e i))
    (hEX : ∀ i < n, c.nmem (EXb + i) = ex (e i))
    (lay : NFb + n ≤ Hb ∧ SGb + n ≤ Hb ∧ RVb + n ≤ Hb ∧ EXb + n ≤ Hb ∧ Hb + 7 * n + 1 ≤ W)
    (hS : ∑ j ∈ range n, c.nmem (EXb + j) ≤ W) :
    ∃ c' t, Exec P W mcProg c c' t ∧ t ≤ 75 * n + 40 ∧
      c'.nreg 5012 = #N ∧ c'.nreg 5021 = ∑ d ∈ N, ex d ∧
      (c'.nreg 5022 = 0 ↔ ∀ d ∈ N, ι d ∈ N) ∧
      (∀ j < n, c'.nmem (Hb + j) = eRk e n N (e j)) ∧
      (∀ i < n, e i ∈ N →
        c'.nmem (Hb + 4 * n + eRk e n N (e i)) = eRk e n N (ι (e i)) ∧
        c'.nmem (Hb + 5 * n + eRk e n N (e i)) = eRk e n N (Orbit.ret τ N (e i)) ∧
        c'.nmem (Hb + 6 * n + eRk e n N (e i)) = ex (e i)) ∧
      (∀ a, (a < Hb ∨ Hb + 7 * n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 5005 ∨ (5029 < x ∧ x < 6220) ∨ 6250 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5⟩ := lay
  have hsN : ∀ d ∈ N, ∃ i, i < n ∧ e i = d := fun d hd => hB d (hNB hd)
  set m₀ := c.nmem with hm₀
  obtain ⟨c₂, k₂, e₂, hk₂, a5, a6, a7, a9, a18, a19, b10, b12, bRK, bNX, bDF, bm₂, bn₂, br₂, brm₂,
    bo₂⟩ := mcA_exec (P := P) c hc r0 r1 r2 r4 ⟨l1, l2, l5⟩
  have hw₂ := e₂.wb_right
  obtain ⟨c₆, k₆, e₆, hk₆, lrep, m₆, ln₆, lr₆, lrm₆, lo₆⟩ :=
    mcB_exec (P := P) c₂ hw₂ (SGb := SGb) (e := e) (B := B) (N := N) (τ := τ)
      (by rw [bn₂ _ (by omega), r0]) (by rw [bn₂ _ (by omega), r2]) a5 a6 a7 hinj hBe hB hNB hτB
      (fun i hi => by rw [bm₂ _ (by omega)]; exact hSG i hi)
      (fun i hi => by rw [bNX i hi, bm₂ _ (by omega)])
      (fun i hi => by rw [bDF i hi, mcF_eq hNF hi]; split_ifs <;> rfl) ⟨l2, l5⟩
  have hw₆ := e₆.wb_right
  have m₆' : ∀ a, (a < Hb ∨ Hb + 4 * n ≤ a) → c₆.nmem a = m₀ a := fun a ha => by
    rw [m₆ a (by omega), bm₂ a (by omega)]
  have hF₆ : ∀ j < n, mcF c₆.nmem NFb j = mcF m₀ NFb j := fun j hj => by
    unfold mcF; rw [m₆' _ (Or.inl (by omega))]
  have hRK₆ : ∀ j < n, c₆.nmem (Hb + j) = ∑ l ∈ range j, mcF m₀ NFb l := fun j hj => by
    rw [m₆ _ (by omega), bRK j hj]
  have hRKe : ∀ j < n, c₆.nmem (Hb + j) = eRk e n N (e j) := fun j hj => by
    rw [hRK₆ j hj, sum_mcF_card hNF j (by omega), eRk_e hinj hsN hj]
  have v : ∀ x, 5000 ≤ x → x ≤ 5019 → c₆.nreg x = c₂.nreg x := fun x h1 h2 => ln₆ _ (by omega)
  have hRV₆ : ∀ j < n, c₆.nmem (RVb + j) = m₀ (RVb + j) := fun j hj => m₆' _ (Or.inl (by omega))
  have hEX₆ : ∀ j < n, c₆.nmem (EXb + j) = m₀ (EXb + j) := fun j hj => m₆' _ (Or.inl (by omega))
  obtain ⟨c₇, k₇, e₇, hk₇, f21, f22, fC, fm₇, fn₇, fr₇, frm₇, fo₇⟩ :=
    mc3_exec (P := P) c₆ hw₆ (n := n) (NFb := NFb) (RVb := RVb) (RKb := Hb) (EXb := EXb)
      (NXb := Hb + n) (CRb := Hb + 4 * n) (CSb := Hb + 5 * n) (CEb := Hb + 6 * n)
      (by rw [v _ (by omega) (by omega), bn₂ _ (by omega), r0])
      (by rw [v _ (by omega) (by omega), bn₂ _ (by omega), r1])
      (by rw [v _ (by omega) (by omega), bn₂ _ (by omega), r3])
      (by rw [v _ (by omega) (by omega), bn₂ _ (by omega), r4])
      (by rw [v _ (by omega) (by omega), a5])
      (by rw [v _ (by omega) (by omega), bn₂ _ (by omega), r8])
      (by rw [v _ (by omega) (by omega), a9])
      (by rw [v _ (by omega) (by omega), a18])
      (by rw [v _ (by omega) (by omega), a19])
      (by rw [v _ (by omega) (by omega), b10])
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      (fun j hj => by
        rw [hRK₆ j hj]
        exact sum_congr rfl fun l hl => (hF₆ l (by rw [mem_range] at hl; omega)).symm)
      (fun j hj => by rw [hRV₆ j hj]; exact (hRV j hj).1)
      (fun j hj hF => by
        rw [hF₆ j hj, mcF_eq hNF hj] at hF
        have hjN : e j ∈ N := by by_contra h; rw [iteF h] at hF; omega
        exact (lrep j hj hjN).1)
      (by rw [sum_congr rfl fun j hj => hEX₆ j (mem_range.1 hj)]; exact hS)
  refine ⟨c₇, k₂ + (k₆ + k₇), .seq e₂ (.seq e₆ e₇), by omega, ?_, ?_, ?_,
    fun j hj => ?_, fun i hi hiN => ?_, fun a ha => ?_, fun x hx => ?_, ?_, ?_, ?_⟩
  · rw [fn₇ _ (by omega), v _ (by omega) (by omega), b12, sum_mcF_card hNF n le_rfl,
      card_filter_e hinj hsN]
  · rw [f21, ← sum_mcF_mul (m := m₀) (NFb := NFb) hNF hinj hsN ex]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    rw [hF₆ j hj, hEX₆ j hj, hEX j hj]
  · have hsum : ∑ j ∈ range n, mcF c₆.nmem NFb j * (1 - mcF c₆.nmem NFb (c₆.nmem (RVb + j))) =
        ∑ j ∈ range n, mcF m₀ NFb j * (1 - mcF m₀ NFb (m₀ (RVb + j))) :=
      sum_congr rfl fun j hj => by
        rw [mem_range] at hj
        rw [hF₆ j hj, hRV₆ j hj, hF₆ _ (hRV j hj).1]
    rw [f22, hsum]
    exact sum_mcF_bad (m := m₀) (NFb := NFb) hNF hsN (rv := fun j => m₀ (RVb + j)) hRV
  · rw [fm₇ _ (by omega), hRKe j hj]
  · have hF1 : mcF c₆.nmem NFb i = 1 := by rw [hF₆ i hi, mcF_eq hNF hi, iteT hiN]
    obtain ⟨g1, g2, g3⟩ := fC i hi hF1
    rw [hRKe i hi] at g1 g2 g3
    obtain ⟨x1, -, x2, -⟩ := lrep i hi hiN
    refine ⟨?_, ?_, ?_⟩
    · rw [g1, hRV₆ i hi, hRKe _ (hRV i hi).1, (hRV i hi).2]
    · rw [g2, hRKe _ x1, x2]
    · rw [g3, hEX₆ i hi, hEX i hi]
  · rw [fm₇ _ (by omega), m₆' a (by omega)]
  · rw [fn₇ _ (by omega), ln₆ _ (by omega), bn₂ _ (by omega)]
  · rw [fr₇, lr₆, br₂]
  · rw [frm₇, lrm₆, brm₂]
  · rw [fo₇, lo₆, bo₂]

end ExecAll


/-! ### The arrays are the index arrays of the piece map -/

section Enc

open Function Equiv Orbit CombMap PlanarSeparator

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The compacted arrays are the index arrays of the piece map** `psep M hσ hB` numbered by
`cNe e n N`, when its rotation is the first return `ret τ N` on `N`. -/
theorem mc_encArr {e : ℕ → D} {n : ℕ} {N : Finset D} {τ σ : Perm D} (hσ : Stable σ N)
    (hB : Stable (revPerm M) N) (hsN : ∀ d ∈ N, ∃ i, i < n ∧ e i = d)
    (hret : ∀ x ∈ N, σ x = Orbit.ret τ N x) {ex : D → ℕ} {mem : ℕ → ℕ} {Hb : ℕ}
    (hC : ∀ i < n, e i ∈ N →
        mem (Hb + 4 * n + eRk e n N (e i)) = eRk e n N (M.rev (e i)) ∧
        mem (Hb + 5 * n + eRk e n N (e i)) = eRk e n N (Orbit.ret τ N (e i)) ∧
        mem (Hb + 6 * n + eRk e n N (e i)) = ex (e i)) :
    EncArr (psep M hσ hB) (cNe e n N) (fun x => ex x.1) mem (Hb + 4 * n) (Hb + 5 * n)
      (Hb + 6 * n) := by
  have key : ∀ d : SDart N, ∃ i, i < n ∧ e i = d.1 := fun d => hsN d.1 d.2
  refine ⟨fun d => ?_, fun d => ?_, fun d => ?_⟩
  · obtain ⟨i, hi, he⟩ := key d
    have := (hC i hi (he ▸ d.2)).1
    rw [cNe_apply hsN, cNe_apply hsN, psep_α, ← he]; exact this
  · obtain ⟨i, hi, he⟩ := key d
    have := (hC i hi (he ▸ d.2)).2.1
    rw [cNe_apply hsN, cNe_apply hsN, psep_σ, hret _ d.2, ← he]; exact this
  · obtain ⟨i, hi, he⟩ := key d
    have := (hC i hi (he ▸ d.2)).2.2
    rw [cNe_apply hsN, ← he]; exact this

end Enc

end BKMNW

end PlanarFlow
