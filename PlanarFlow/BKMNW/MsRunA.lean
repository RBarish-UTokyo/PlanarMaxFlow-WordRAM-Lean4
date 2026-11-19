module

public import PlanarFlow.BKMNW.MsStart
public import PlanarFlow.BKMNW.FrCall

/-!
# The MSSP call, part A: the read-back and the clearing

After the in-place run of Klein's fixed program (`KleinFix.kNFM`), the answers of the `q × q`
queries are read back from its natural words:

* **`mrRead`**: for `k < q²` (`i = k / q`, `j = k mod q`), the slot `s = SL[i]` and the target
  `τ = TI[j]`, the word `RB[s t + τ]` (at `r8011 + s t + τ`) and, when it is `1`, the word
  `OUT[s t + τ]` (at `r8012 + s t + τ`) divided by `N₁ = r8013`, else `0`, stored at
  `Ob + k` (`mrRead_exec`, `20 q² + 4` steps; `mrVal` the value read);
* **`mcClr`**: the logged cells cleared (`lgClr`), then the encoder's regions `[0, Z)`
  (`Z = r8016`) and `[β', β' + len)` (`β' = r8017`, `len = r8018`) zeroed (`mzFill`)
  (`mcClr_exec`).

Registers: `r8006 = q`, `r8008 = Ob`, `r8010 = t`, `r8011 = aRB`, `r8012 = aO`, `r8013 = N₁`,
`r8014 = SLb`, `r8015 = TIb`, `r8016 = Z`, `r8017 = β'`, `r8018 = len`, `r8019` the log base,
`r8020` the log pointer, `r8021 = 1`; scratch `8022 … 8032`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MsCall

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP

/-- The value read back for the query pair `k = i q + j`. -/
def mrVal (mem : ℕ → ℕ) (q SLb TIb t aRB aO N1 k : ℕ) : ℕ :=
  if mem (aRB + (mem (SLb + k / q) * t + mem (TIb + k % q))) = 1 then
    mem (aO + (mem (SLb + k / q) * t + mem (TIb + k % q))) / N1
  else 0

/-- The address part of the body. -/
def mrA : Stmt := block [.divN 8022 8030 8006, .modN 8023 8030 8006, .addN 8024 8014 8022,
  .loadN 8024 8024, .addN 8025 8015 8023, .loadN 8025 8025, .mulN 8026 8024 8010,
  .addN 8026 8026 8025, .addN 8027 8011 8026, .loadN 8027 8027, .addN 8028 8012 8026,
  .loadN 8028 8028, .divN 8028 8028 8013, .addN 8029 8008 8030, .constN 8032 0]

/-- The store of the value. -/
def mrS : Stmt := .ifLtN 8027 8021 (.instr (.storeN 8029 8032))
  (.ifLtN 8021 8027 (.instr (.storeN 8029 8032)) (.instr (.storeN 8029 8028)))

/-- The body of the read-back. -/
def mrBody : Stmt := .seq mrA (.seq mrS (block [.addN 8030 8030 8021]))

/-- **The read-back.** -/
def mrRead : Stmt := .seq (block [.constN 8030 0, .mulN 8031 8006 8006])
  (.whileLtN 8030 8031 mrBody)

/-- **The clearing.** -/
def mcClr : Stmt :=
  .seq (.seq (block [.copyN 2924 8019, .copyN 2925 8020, .constN 2926 1]) lgClr)
    (.seq (.seq (block [.copyN 5030 8016, .constN 5031 0]) mzFill)
      (.seq (block [.copyN 5030 8018, .copyN 5031 8017]) mzFill))

section Run

variable {P : Input} {W : ℕ}

theorem mrA_exec (c : Config) (hc : WordsBounded W c) {k q Ob t aRB aO N1 SLb TIb : ℕ}
    (r30 : c.nreg 8030 = k) (r06 : c.nreg 8006 = q) (r08 : c.nreg 8008 = Ob)
    (r10 : c.nreg 8010 = t) (r11 : c.nreg 8011 = aRB) (r12 : c.nreg 8012 = aO)
    (r13 : c.nreg 8013 = N1) (r14 : c.nreg 8014 = SLb) (r15 : c.nreg 8015 = TIb)
    (w1 : SLb + k / q ≤ W) (w2 : TIb + k % q ≤ W)
    (w3 : c.nmem (SLb + k / q) * t + c.nmem (TIb + k % q) ≤ W)
    (w4 : aRB + (c.nmem (SLb + k / q) * t + c.nmem (TIb + k % q)) ≤ W)
    (w5 : aO + (c.nmem (SLb + k / q) * t + c.nmem (TIb + k % q)) ≤ W) (w6 : Ob + k ≤ W) :
    ∃ c' u, Exec P W mrA c c' u ∧ u = 15 ∧
      c'.nreg 8027 = c.nmem (aRB + (c.nmem (SLb + k / q) * t + c.nmem (TIb + k % q))) ∧
      c'.nreg 8028 =
        c.nmem (aO + (c.nmem (SLb + k / q) * t + c.nmem (TIb + k % q))) / N1 ∧
      c'.nreg 8029 = Ob + k ∧ c'.nreg 8032 = 0 ∧
      (∀ r, (r < 8022 ∨ 8029 < r) → r ≠ 8032 → c'.nreg r = c.nreg r) ∧ c'.nreg 8030 = k ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold mrA
  exec_block
  all_goals try first
    | omega
    | (config_simp; omega)
    | (config_simp; simp only [r30, r06, r08, r10, r11, r12, r13, r14, r15]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r h1 h2 => ?_, ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r30, r06, r08, r10, r11, r12, r13, r14, r15])
  repeat rw [upd_other _ _ _ (by omega)]

theorem mrS_exec (c : Config) (hc : WordsBounded W c) {a v : ℕ} (r21 : c.nreg 8021 = 1)
    (r29 : c.nreg 8029 = a) (r32 : c.nreg 8032 = 0) (r28 : c.nreg 8028 = v) :
    ∃ c' u, Exec P W mrS c c' u ∧ u ≤ 5 ∧
      c'.nmem = upd c.nmem a (if c.nreg 8027 = 1 then v else 0) ∧
      c'.nreg = c.nreg ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold mrS
  by_cases h1 : c.nreg 8027 < c.nreg 8021
  · refine ⟨_, _, Exec.ifLtN_true h1 (Exec.storeN hc 8029 8032), by omega, ?_, rfl, rfl, rfl, rfl⟩
    have : c.nreg 8027 ≠ 1 := by omega
    simp [r29, r32, this]
  · by_cases h2 : c.nreg 8021 < c.nreg 8027
    · refine ⟨_, _, Exec.ifLtN_false h1 (Exec.ifLtN_true h2 (Exec.storeN hc 8029 8032)),
        by omega, ?_, rfl, rfl, rfl, rfl⟩
      have : c.nreg 8027 ≠ 1 := by omega
      simp [r29, r32, this]
    · refine ⟨_, _, Exec.ifLtN_false h1 (Exec.ifLtN_false h2 (Exec.storeN hc 8029 8028)),
        by omega, ?_, rfl, rfl, rfl, rfl⟩
      have : c.nreg 8027 = 1 := by omega
      simp [r29, r28, this]

/-- **The read-back**: `Ob + k ↦ mrVal` of the starting memory, for `k < q²`. -/
theorem mrRead_exec (c : Config) (hc : WordsBounded W c) {q Ob t aRB aO N1 SLb TIb : ℕ}
    (r06 : c.nreg 8006 = q) (r08 : c.nreg 8008 = Ob)
    (r10 : c.nreg 8010 = t) (r11 : c.nreg 8011 = aRB) (r12 : c.nreg 8012 = aO)
    (r13 : c.nreg 8013 = N1) (r14 : c.nreg 8014 = SLb) (r15 : c.nreg 8015 = TIb)
    (r21 : c.nreg 8021 = 1)
    (hSL : Ob + q * q ≤ SLb) (hTI : Ob + q * q ≤ TIb) (hSLW : SLb + q ≤ W) (hTIW : TIb + q ≤ W)
    (hrd : ∀ k < q * q,
      c.nmem (SLb + k / q) * t + c.nmem (TIb + k % q) ≤ W ∧
      aRB + (c.nmem (SLb + k / q) * t + c.nmem (TIb + k % q)) < Ob ∧
      aO + (c.nmem (SLb + k / q) * t + c.nmem (TIb + k % q)) < Ob)
    (hOW : Ob + q * q + 1 ≤ W) :
    ∃ c' u, Exec P W mrRead c c' u ∧ u ≤ 23 * (q * q) + 4 ∧
      (∀ k < q * q, c'.nmem (Ob + k) = mrVal c.nmem q SLb TIb t aRB aO N1 k) ∧
      (∀ a, (a < Ob ∨ Ob + q * q ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 8022 ∨ 8032 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hq0 : ∀ k < q * q, 0 < q := fun k hk => by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp at hk
    · exact h
  have hdiv : ∀ k < q * q, k / q < q := fun k hk => by
    rw [Nat.div_lt_iff_lt_mul (hq0 k hk)]; exact hk
  have hmod : ∀ k < q * q, k % q < q := fun k hk => Nat.mod_lt _ (hq0 k hk)
  obtain ⟨c₁, t₁, e₁, ht₁, a30, a31, ak, am, ar, arm, ao⟩ : ∃ c₁ t₁,
      Exec P W (block [.constN 8030 0, .mulN 8031 8006 8006]) c c₁ t₁ ∧ t₁ = 2 ∧
        c₁.nreg 8030 = 0 ∧ c₁.nreg 8031 = q * q ∧
        (∀ r, r ≠ 8030 → r ≠ 8031 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [r06]); omega)
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r06])
    repeat rw [upd_other _ _ _ (by omega)]
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ k < i, c'.nmem (Ob + k) = mrVal c.nmem q SLb TIb t aRB aO N1 k) ∧
      (∀ a, (a < Ob ∨ Ob + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 8022 ∨ 8032 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, t₂, e₂, ht₂, -, g1, g2, g3, g4, g5, g6⟩ :=
    forLoop_exec (P := P) (a := 8030) (bR := 8031) (body := mrBody) J (K := 21) (n := q * q) c₁
      e₁.wb_right a30 a31
      ⟨fun k hk => absurd hk (by omega), fun a _ => by rw [am],
        fun r hr => ak r (by omega) (by omega), ar, arm, ao⟩
      (fun i c' hi hw ha hb hJ => by
        obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hJ
        have hm : ∀ a, a < Ob → c'.nmem a = c.nmem a := fun a h => g2 a (Or.inl h)
        have hSLi : c'.nmem (SLb + i / q) = c.nmem (SLb + i / q) :=
          g2 _ (Or.inr (le_trans (by omega : Ob + i ≤ SLb) (Nat.le_add_right _ _)))
        have hTIi : c'.nmem (TIb + i % q) = c.nmem (TIb + i % q) :=
          g2 _ (Or.inr (le_trans (by omega : Ob + i ≤ TIb) (Nat.le_add_right _ _)))
        obtain ⟨h1, h2, h3⟩ := hrd i hi
        obtain ⟨c'', u, e, hu, b27, b28, b29, b32, bk, b30, bm, br, brm, bo⟩ :=
          mrA_exec (P := P) c' hw ha (by rw [g3 _ (by omega), r06]) (by rw [g3 _ (by omega), r08])
            (by rw [g3 _ (by omega), r10]) (by rw [g3 _ (by omega), r11])
            (by rw [g3 _ (by omega), r12]) (by rw [g3 _ (by omega), r13])
            (by rw [g3 _ (by omega), r14]) (by rw [g3 _ (by omega), r15])
            (by have := hdiv i hi; omega) (by have := hmod i hi; omega)
            (by rw [hSLi, hTIi]; exact h1) (by rw [hSLi, hTIi]; omega)
            (by rw [hSLi, hTIi]; omega) (by omega)
        have hw'' := e.wb_right
        obtain ⟨c₃, u₃, e₃, hu₃, dm, dn, dr, drm, do'⟩ :=
          mrS_exec (P := P) c'' hw'' (by rw [bk _ (by omega) (by omega), g3 _ (by omega), r21]) b29
            b32 b28
        have hw₃ := e₃.wb_right
        obtain ⟨c₄, u₄, e₄, hu₄, f30, fk, fm, fr, frm, fo⟩ : ∃ c₄ u₄,
            Exec P W (block [.addN 8030 8030 8021]) c₃ c₄ u₄ ∧ u₄ = 1 ∧ c₄.nreg 8030 = i + 1 ∧
              (∀ r, r ≠ 8030 → c₄.nreg r = c₃.nreg r) ∧ c₄.nmem = c₃.nmem ∧ c₄.rreg = c₃.rreg ∧
              c₄.rmem = c₃.rmem ∧ c₄.output = c₃.output := by
          exec_block
          · config_simp; rw [dn, b30, bk _ (by omega) (by omega), g3 _ (by omega), r21]; omega
          refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
          · config_simp; rw [dn, b30, bk _ (by omega) (by omega), g3 _ (by omega), r21]
          · config_simp; rw [upd_other _ _ _ hr]
        refine ⟨c₄, _, e.seq (e₃.seq e₄), by omega, f30, by rw [fk _ (by omega), dn,
          bk _ (by omega) (by omega), hb], fun k hk => ?_, fun a ha' => ?_, fun r hr => ?_,
          by rw [fr, dr, br, g4], by rw [frm, drm, brm, g5], by rw [fo, do', bo, g6]⟩
        · rw [fm, dm, bm]
          by_cases hk' : k = i
          · subst hk'
            rw [upd_same, b27, hSLi, hTIi, hm _ h2, hm _ h3]
            rfl
          · rw [upd_other _ _ _ (by omega), g1 k (by omega)]
        · rw [fm, dm, bm, upd_other _ _ _ (by omega), g2 a (by omega)]
        · rw [fk _ (by omega), dn, bk _ (by omega) (by omega), g3 _ hr])
  exact ⟨c₂, _, e₁.seq e₂, by omega, g1, fun a ha => g2 a ha, g3, g4, g5, g6⟩

/-- **The clearing**: the logged cells, `[0, Z)` and `[β', β' + len)` zero, every other cell
kept. -/
theorem mcClr_exec (c : Config) (hc : WordsBounded W c) {p j Ws Z β' len : ℕ}
    (r19 : c.nreg 8019 = p) (r20 : c.nreg 8020 = p + j) (r16 : c.nreg 8016 = Z)
    (r17 : c.nreg 8017 = β') (r18 : c.nreg 8018 = len)
    (hlog : ∀ i < j, c.nmem (p + i) ≤ Ws) (hp : Ws < p) (hZ : Z + 1 ≤ W)
    (hβ : β' + len ≤ W) (hlen : len + 1 ≤ W) :
    ∃ c' u, Exec P W mcClr c c' u ∧ u ≤ 6 * j + 5 * Z + 5 * len + 22 ∧
      (∀ a, (∃ i < j, c.nmem (p + i) = a) ∨ a < Z ∨ (β' ≤ a ∧ a < β' + len) → c'.nmem a = 0) ∧
      (∀ a, (∀ i < j, c.nmem (p + i) ≠ a) → Z ≤ a → (a < β' ∨ β' + len ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2923 ∨ (2929 < r ∧ r < 5030) ∨ 5035 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a24, a25, a26, ak, am, ar, arm, ao⟩ : ∃ c₁ t₁,
      Exec P W (block [.copyN 2924 8019, .copyN 2925 8020, .constN 2926 1]) c c₁ t₁ ∧ t₁ = 3 ∧
        c₁.nreg 2924 = p ∧ c₁.nreg 2925 = p + j ∧ c₁.nreg 2926 = 1 ∧
        (∀ r, (r < 2924 ∨ 2926 < r) → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    · have := hc.1 8019; omega
    refine ⟨rfl, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r19, r20])
    repeat rw [upd_other _ _ _ (by omega)]
  obtain ⟨c₂, t₂, e₂, ht₂, bzero, bkeep, bregs, br, brm, bo⟩ :=
    lgClr_exec (P := P) c₁ e₁.wb_right (p := p) (j := j) (Ws := Ws) a24 a25 a26
      (fun i hi => by rw [am]; exact hlog i hi) hp
  have k2 : ∀ r, r < 2923 ∨ 2929 < r → c₂.nreg r = c.nreg r := fun r hr => by
    rw [bregs r (by omega) (by omega), ak r (by omega)]
  have hw₂ := e₂.wb_right
  obtain ⟨c₃, t₃, e₃, ht₃, c30, c31, ck, cm, cr, crm, co⟩ : ∃ c₃ t₃,
      Exec P W (block [.copyN 5030 8016, .constN 5031 0]) c₂ c₃ t₃ ∧ t₃ = 2 ∧
        c₃.nreg 5030 = Z ∧ c₃.nreg 5031 = 0 ∧
        (∀ r, r ≠ 5030 → r ≠ 5031 → c₃.nreg r = c₂.nreg r) ∧
        c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    · rw [k2 _ (by omega), r16]
    · repeat rw [upd_other _ _ _ (by omega)]
  obtain ⟨c₄, t₄, e₄, ht₄, dzero, dkeep, dregs, dr, drm, do'⟩ :=
    mzFill_exec (P := P) c₃ e₃.wb_right (len := Z) (Zb := 0) c30 c31 (by omega) hZ
  have k4 : ∀ r, r < 2923 ∨ (2929 < r ∧ r < 5030) ∨ 5035 < r → c₄.nreg r = c.nreg r :=
    fun r hr => by rw [dregs r (by omega), ck r (by omega) (by omega), k2 r (by omega)]
  have hw₄ := e₄.wb_right
  obtain ⟨c₅, t₅, e₅, ht₅, f30, f31, fk, fm, fr, frm, fo⟩ : ∃ c₅ t₅,
      Exec P W (block [.copyN 5030 8018, .copyN 5031 8017]) c₄ c₅ t₅ ∧ t₅ = 2 ∧
        c₅.nreg 5030 = len ∧ c₅.nreg 5031 = β' ∧
        (∀ r, r ≠ 5030 → r ≠ 5031 → c₅.nreg r = c₄.nreg r) ∧
        c₅.nmem = c₄.nmem ∧ c₅.rreg = c₄.rreg ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output := by
    exec_block
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    · rw [k4 _ (by omega), r18]
    · rw [k4 _ (by omega), r17]
    · repeat rw [upd_other _ _ _ (by omega)]
  obtain ⟨c₆, t₆, e₆, ht₆, gzero, gkeep, gregs, gr, grm, go⟩ :=
    mzFill_exec (P := P) c₅ e₅.wb_right (len := len) (Zb := β') f30 f31 hβ hlen
  refine ⟨c₆, _, (e₁.seq e₂).seq ((e₃.seq e₄).seq (e₅.seq e₆)), by omega, fun a ha => ?_,
    fun a hl h1 h2 => ?_, fun r hr => ?_, by rw [gr, fr, dr, cr, br, ar],
    by rw [grm, frm, drm, crm, brm, arm], by rw [go, fo, do', co, bo, ao]⟩
  · rcases ha with ⟨i, hi, hia⟩ | ha | ⟨h1, h2⟩
    · by_cases hb : β' ≤ a ∧ a < β' + len
      · have := gzero (a - β') (by omega); rwa [show β' + (a - β') = a by omega] at this
      rw [gkeep a (by omega), fm]
      by_cases hz : a < Z
      · have := dzero a hz; rwa [Nat.zero_add] at this
      rw [dkeep a (by omega), cm]
      exact bzero a ⟨i, hi, by rw [am]; exact hia⟩
    · by_cases hb : β' ≤ a ∧ a < β' + len
      · have := gzero (a - β') (by omega); rwa [show β' + (a - β') = a by omega] at this
      rw [gkeep a (by omega), fm]
      have := dzero a ha; rwa [Nat.zero_add] at this
    · have := gzero (a - β') (by omega); rwa [show β' + (a - β') = a by omega] at this
  · rw [gkeep a h2, fm, dkeep a (by omega), cm, bkeep a (fun i hi => by rw [am]; exact hl i hi),
      am]
  · rw [gregs r (by omega), fk r (by omega) (by omega), k4 r hr]

end Run

end MsCall

end BKMNW

end PlanarFlow
