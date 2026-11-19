module

public import PlanarFlow.BKMNW.NcAr

/-!
# The loops of the pendant frame writer and of the copy-back: the generic store loop

The programs `pfP` (the frame of the map with a pendant edge at every vertex) and `cbP` (the
copy-back of `fixFrozen`) are made of store loops over `t < n` writing one cell `OUT[t]` per
round. They use the registers `9920 … 9999` only (the register band of the pendant frame writer):

* `9920` the index `t`, `9921` the constant `1`;
* the arguments `9923` `X` base, `9924` `Y` base, `9925` `OUT` base, `9926` `K`, `9927` `K₂`,
  `9929` `R` base;
* the scratch of the bodies `9940 … 9945`;
* the bounds and the layout values `9930 … 9939`, `9950 … 9999` (never written by the loops).

* **`pfW bnd body`** (`t := 0`, `1`, `while t < r[bnd]: body`), **`pfW_exec`**: the generic
  store loop (`lnStoreIP` with the registers above), its result **`PfOut`**;
* the bodies (each ends with `t := t + 1`):
  `bAk` (`OUT[t] := X[t] + K ∸ K₂`), `bId` (`OUT[t] := t + K`), `bSx` (`OUT[t] := X[t] + K ∸ Y[t]`),
  `bDf` (`OUT[t] := X[t] ∸ X[t]·Y[t]`), `bQ` (`OUT[t] := s ∸ (s ∸ 1)`, `s = X[t] + X[Y[t]]`),
  `bXm` (`OUT[t] := X[t]·Y[t] + K ∸ K·Y[t]`), `bRf` (`OUT[t] := X[t] ∸ t`),
  `bG` (`OUT[t] := X[Y[t]]·K`), `bSg` (`OUT[t] := s + e·(R[r] + K ∸ s)` with `r = X[t] ∸ 1`,
  `s = Y[t]`, `e = 1 ∸ ((s ∸ r) + (r ∸ s))`), `bMx` (`OUT[t] := Y[t]·X[t] + R[t] ∸ Y[t]·R[t]`);
  their runs `b*_exec` and the loops `l*_exec`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcFz

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- The registers written by the store loops. -/
def PfScr (r : ℕ) : Prop := r = 9920 ∨ r = 9921 ∨ (9940 ≤ r ∧ r ≤ 9945)

/-- **The generic store loop**: `t := 0`, `1`, then the body while `t < r[bnd]`. -/
def pfW (bnd : ℕ) (body : Stmt) : Stmt :=
  .seq (block [.constN 9920 0, .constN 9921 1]) (.whileLtN 9920 bnd body)

/-- **The result of a store loop** writing `OUT[t] = val t` for `t < n`. -/
structure PfOut (c c' : Config) (O n : ℕ) (val : ℕ → ℕ) : Prop where
  val : ∀ t < n, c'.nmem (O + t) = val t
  mem : ∀ a, (a < O ∨ O + n ≤ a) → c'.nmem a = c.nmem a
  reg : ∀ r, ¬ PfScr r → c'.nreg r = c.nreg r
  one : c'.nreg 9921 = 1
  rr : c'.rreg = c.rreg
  rm : c'.rmem = c.rmem
  out : c'.output = c.output

theorem pfI_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c₁ k₁, Exec P W (block [.constN 9920 0, .constN 9921 1]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 9920 = 0 ∧ c₁.nreg 9921 = 1 ∧
      (∀ x, x ≠ 9920 → x ≠ 9921 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

/-- **The generic store loop.** -/
theorem pfW_exec {bnd : ℕ} {body : Stmt} {Ob n B : ℕ} (val : ℕ → ℕ) (c : Config)
    (hc : WordsBounded W c) (hW : 1 ≤ W) (hb : c.nreg bnd = n) (hbnd : ¬ PfScr bnd)
    (hbody : ∀ t (c' : Config), t < n → WordsBounded W c' → c'.nreg 9920 = t →
      c'.nreg 9921 = 1 → (∀ r, ¬ PfScr r → c'.nreg r = c.nreg r) →
      (∀ a, (∀ j < t, a ≠ Ob + j) → c'.nmem a = c.nmem a) →
      ∃ c'' k, Exec P W body c' c'' k ∧ k ≤ B ∧ c''.nreg 9920 = t + 1 ∧
        (∀ r, r ≠ 9920 → ¬ (9940 ≤ r ∧ r ≤ 9945) → c''.nreg r = c'.nreg r) ∧
        c''.nmem = upd c'.nmem (Ob + t) (val t) ∧ c''.rreg = c'.rreg ∧
        c''.rmem = c'.rmem ∧ c''.output = c'.output) :
    ∃ c' k, Exec P W (pfW bnd body) c c' k ∧ k ≤ (B + 2) * n + 4 ∧ PfOut c c' Ob n val := by
  unfold PfScr at hbnd
  obtain ⟨c₁, k₁, e₁, hk₁, g0, g1, gn, gm, gr, grm, go⟩ := pfI_exec (P := P) c hc hW
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, f₂, g₂, a₂, rr₂, rm₂, o₂⟩ := NcStep.lnStoreIP (P := P)
    (a := 9920) (b := bnd) (body := body) (Ob := Ob) (n := n) (B := B) val
    (fun r => r ≠ 9920 ∧ ¬ (9940 ≤ r ∧ r ≤ 9945)) c₁ e₁.wb_right g0
    (by rw [gn bnd (by omega) (by omega), hb]) ⟨by omega, by omega⟩
    (fun t c' ht hw h20 hk hm => by
      obtain ⟨c'', k, ex, hk', h20', hr, hmem, rr, rm, o⟩ := hbody t c' ht hw h20
        (by rw [hk 9921 ⟨by omega, by omega⟩, g1])
        (fun r hr => by
          unfold PfScr at hr
          rw [hk r ⟨by omega, by omega⟩, gn r (by omega) (by omega)])
        (fun a ha => by rw [hm a ha, gm])
      exact ⟨c'', k, ex, hk', h20', fun x hx => hr x hx.1 hx.2, hmem, rr, rm, o⟩)
  refine ⟨c₂, k₁ + k₂, e₁.seq e₂, by omega, ⟨v₂, fun a ha => by rw [f₂ a ha, gm],
    fun r hr => ?_, ?_, by rw [rr₂, gr], by rw [rm₂, grm], by rw [o₂, go]⟩⟩
  · unfold PfScr at hr
    rw [g₂ r ⟨by omega, by omega⟩, gn r (by omega) (by omega)]
  · rw [g₂ 9921 ⟨by omega, by omega⟩, g1]

/-! ### The bodies -/

/-- `OUT[t] := X[t] + K ∸ K₂`. -/
def bAk : Stmt :=
  block [.addN 9940 9923 9920, .loadN 9940 9940, .addN 9940 9940 9926, .subN 9940 9940 9927,
    .addN 9941 9925 9920, .storeN 9941 9940, .addN 9920 9920 9921]

/-- `OUT[t] := t + K`. -/
def bId : Stmt :=
  block [.addN 9940 9920 9926, .addN 9941 9925 9920, .storeN 9941 9940, .addN 9920 9920 9921]

/-- `OUT[t] := X[t] + K ∸ Y[t]`. -/
def bSx : Stmt :=
  block [.addN 9940 9923 9920, .loadN 9940 9940, .addN 9940 9940 9926, .addN 9941 9924 9920,
    .loadN 9941 9941, .subN 9940 9940 9941, .addN 9941 9925 9920, .storeN 9941 9940,
    .addN 9920 9920 9921]

/-- `OUT[t] := X[t] ∸ X[t]·Y[t]`. -/
def bDf : Stmt :=
  block [.addN 9940 9923 9920, .loadN 9940 9940, .addN 9941 9924 9920, .loadN 9941 9941,
    .mulN 9941 9940 9941, .subN 9940 9940 9941, .addN 9941 9925 9920, .storeN 9941 9940,
    .addN 9920 9920 9921]

/-- `OUT[t] := s ∸ (s ∸ 1)` with `s = X[t] + X[Y[t]]`. -/
def bQ : Stmt :=
  block [.addN 9940 9923 9920, .loadN 9940 9940, .addN 9941 9924 9920, .loadN 9941 9941,
    .addN 9941 9923 9941, .loadN 9941 9941, .addN 9940 9940 9941, .subN 9941 9940 9921,
    .subN 9940 9940 9941, .addN 9941 9925 9920, .storeN 9941 9940, .addN 9920 9920 9921]

/-- `OUT[t] := X[t]·Y[t] + K ∸ K·Y[t]`. -/
def bXm : Stmt :=
  block [.addN 9940 9923 9920, .loadN 9940 9940, .addN 9941 9924 9920, .loadN 9941 9941,
    .mulN 9940 9940 9941, .addN 9940 9940 9926, .mulN 9941 9926 9941, .subN 9940 9940 9941,
    .addN 9941 9925 9920, .storeN 9941 9940, .addN 9920 9920 9921]

/-- `OUT[t] := X[t] ∸ t`. -/
def bRf : Stmt :=
  block [.addN 9940 9923 9920, .loadN 9940 9940, .subN 9940 9940 9920, .addN 9941 9925 9920,
    .storeN 9941 9940, .addN 9920 9920 9921]

/-- `OUT[t] := X[Y[t]]·K`. -/
def bG : Stmt :=
  block [.addN 9940 9924 9920, .loadN 9940 9940, .addN 9940 9923 9940, .loadN 9940 9940,
    .mulN 9940 9940 9926, .addN 9941 9925 9920, .storeN 9941 9940, .addN 9920 9920 9921]

/-- `OUT[t] := s + e·(R[r] + K ∸ s)`, `r = X[t] ∸ 1`, `s = Y[t]`, `e = 1 ∸ ((s ∸ r) + (r ∸ s))`. -/
def bSg : Stmt :=
  block [.addN 9940 9923 9920, .loadN 9940 9940, .subN 9940 9940 9921, .addN 9941 9924 9920,
    .loadN 9941 9941, .subN 9942 9941 9940, .subN 9943 9940 9941, .addN 9942 9942 9943,
    .subN 9942 9921 9942, .addN 9943 9929 9940, .loadN 9943 9943, .addN 9943 9943 9926,
    .subN 9943 9943 9941, .mulN 9943 9942 9943, .addN 9943 9941 9943, .addN 9944 9925 9920,
    .storeN 9944 9943, .addN 9920 9920 9921]

/-- `OUT[t] := Y[t]·X[t] + R[t] ∸ Y[t]·R[t]`. -/
def bMx : Stmt :=
  block [.addN 9940 9923 9920, .loadN 9940 9940, .addN 9941 9924 9920, .loadN 9941 9941,
    .addN 9942 9929 9920, .loadN 9942 9942, .mulN 9940 9941 9940, .addN 9940 9940 9942,
    .mulN 9942 9941 9942, .subN 9940 9940 9942, .addN 9941 9925 9920, .storeN 9941 9940,
    .addN 9920 9920 9921]

/-! ### The runs of the bodies -/

theorem bAk_exec (c : Config) (hc : WordsBounded W c) {t X O K K₂ : ℕ}
    (r20 : c.nreg 9920 = t) (r21 : c.nreg 9921 = 1) (r23 : c.nreg 9923 = X)
    (r25 : c.nreg 9925 = O) (r26 : c.nreg 9926 = K) (r27 : c.nreg 9927 = K₂)
    (w1 : X + t ≤ W) (w2 : O + t ≤ W) (w3 : t + 1 ≤ W) (w4 : c.nmem (X + t) + K ≤ W) :
    ∃ c' k, Exec P W bAk c c' k ∧ k = 7 ∧ c'.nreg 9920 = t + 1 ∧
      (∀ r, r ≠ 9920 → ¬ (9940 ≤ r ∧ r ≤ 9945) → c'.nreg r = c.nreg r) ∧
      c'.nmem = upd c.nmem (O + t) (c.nmem (X + t) + K - K₂) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bAk
  exec_block
  all_goals try ((try config_simp); (try simp only [r20, r21, r23, r25, r26, r27]); omega)
  refine ⟨rfl, ?_, fun r h1 h2 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r20, r21]
  · simp only [upd_apply]; split_ifs <;> omega
  · simp only [r20, r23, r25, r26, r27]

theorem bId_exec (c : Config) (hc : WordsBounded W c) {t O K : ℕ}
    (r20 : c.nreg 9920 = t) (r21 : c.nreg 9921 = 1)
    (r25 : c.nreg 9925 = O) (r26 : c.nreg 9926 = K)
    (w2 : O + t ≤ W) (w3 : t + 1 ≤ W) (w4 : t + K ≤ W) :
    ∃ c' k, Exec P W bId c c' k ∧ k = 4 ∧ c'.nreg 9920 = t + 1 ∧
      (∀ r, r ≠ 9920 → ¬ (9940 ≤ r ∧ r ≤ 9945) → c'.nreg r = c.nreg r) ∧
      c'.nmem = upd c.nmem (O + t) (t + K) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bId
  exec_block
  all_goals try ((try config_simp); (try simp only [r20, r21, r25, r26]); omega)
  refine ⟨rfl, ?_, fun r h1 h2 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r20, r21]
  · simp only [upd_apply]; split_ifs <;> omega
  · simp only [r20, r25, r26]

theorem bSx_exec (c : Config) (hc : WordsBounded W c) {t X Y O K : ℕ}
    (r20 : c.nreg 9920 = t) (r21 : c.nreg 9921 = 1) (r23 : c.nreg 9923 = X)
    (r24 : c.nreg 9924 = Y) (r25 : c.nreg 9925 = O) (r26 : c.nreg 9926 = K)
    (w1 : X + t ≤ W) (w1' : Y + t ≤ W) (w2 : O + t ≤ W) (w3 : t + 1 ≤ W)
    (w4 : c.nmem (X + t) + K ≤ W) :
    ∃ c' k, Exec P W bSx c c' k ∧ k = 9 ∧ c'.nreg 9920 = t + 1 ∧
      (∀ r, r ≠ 9920 → ¬ (9940 ≤ r ∧ r ≤ 9945) → c'.nreg r = c.nreg r) ∧
      c'.nmem = upd c.nmem (O + t) (c.nmem (X + t) + K - c.nmem (Y + t)) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bSx
  exec_block
  all_goals try ((try config_simp); (try simp only [r20, r21, r23, r24, r25, r26]); omega)
  refine ⟨rfl, ?_, fun r h1 h2 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r20, r21]
  · simp only [upd_apply]; split_ifs <;> omega
  · simp only [r20, r23, r24, r25, r26]

theorem bDf_exec (c : Config) (hc : WordsBounded W c) {t X Y O : ℕ}
    (r20 : c.nreg 9920 = t) (r21 : c.nreg 9921 = 1) (r23 : c.nreg 9923 = X)
    (r24 : c.nreg 9924 = Y) (r25 : c.nreg 9925 = O)
    (w1 : X + t ≤ W) (w1' : Y + t ≤ W) (w2 : O + t ≤ W) (w3 : t + 1 ≤ W)
    (w4 : c.nmem (X + t) * c.nmem (Y + t) ≤ W) :
    ∃ c' k, Exec P W bDf c c' k ∧ k = 9 ∧ c'.nreg 9920 = t + 1 ∧
      (∀ r, r ≠ 9920 → ¬ (9940 ≤ r ∧ r ≤ 9945) → c'.nreg r = c.nreg r) ∧
      c'.nmem = upd c.nmem (O + t) (c.nmem (X + t) - c.nmem (X + t) * c.nmem (Y + t)) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bDf
  exec_block
  all_goals try ((try config_simp); (try simp only [r20, r21, r23, r24, r25]); omega)
  refine ⟨rfl, ?_, fun r h1 h2 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r20, r21]
  · simp only [upd_apply]; split_ifs <;> omega
  · simp only [r20, r23, r24, r25]

theorem bQ_exec (c : Config) (hc : WordsBounded W c) {t X Y O : ℕ}
    (r20 : c.nreg 9920 = t) (r21 : c.nreg 9921 = 1) (r23 : c.nreg 9923 = X)
    (r24 : c.nreg 9924 = Y) (r25 : c.nreg 9925 = O)
    (w1 : X + t ≤ W) (w1' : Y + t ≤ W) (w1'' : X + c.nmem (Y + t) ≤ W) (w2 : O + t ≤ W)
    (w3 : t + 1 ≤ W) (w4 : c.nmem (X + t) + c.nmem (X + c.nmem (Y + t)) ≤ W) :
    ∃ c' k, Exec P W bQ c c' k ∧ k = 12 ∧ c'.nreg 9920 = t + 1 ∧
      (∀ r, r ≠ 9920 → ¬ (9940 ≤ r ∧ r ≤ 9945) → c'.nreg r = c.nreg r) ∧
      c'.nmem = upd c.nmem (O + t)
        ((c.nmem (X + t) + c.nmem (X + c.nmem (Y + t))) -
          ((c.nmem (X + t) + c.nmem (X + c.nmem (Y + t))) - 1)) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bQ
  exec_block
  all_goals try ((try config_simp); (try simp only [r20, r21, r23, r24, r25]); omega)
  refine ⟨rfl, ?_, fun r h1 h2 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r20, r21]
  · simp only [upd_apply]; split_ifs <;> omega
  · simp only [r20, r21, r23, r24, r25]

theorem bXm_exec (c : Config) (hc : WordsBounded W c) {t X Y O K : ℕ}
    (r20 : c.nreg 9920 = t) (r21 : c.nreg 9921 = 1) (r23 : c.nreg 9923 = X)
    (r24 : c.nreg 9924 = Y) (r25 : c.nreg 9925 = O) (r26 : c.nreg 9926 = K)
    (w1 : X + t ≤ W) (w1' : Y + t ≤ W) (w2 : O + t ≤ W) (w3 : t + 1 ≤ W)
    (w4 : c.nmem (X + t) * c.nmem (Y + t) + K ≤ W) (w5 : K * c.nmem (Y + t) ≤ W) :
    ∃ c' k, Exec P W bXm c c' k ∧ k = 11 ∧ c'.nreg 9920 = t + 1 ∧
      (∀ r, r ≠ 9920 → ¬ (9940 ≤ r ∧ r ≤ 9945) → c'.nreg r = c.nreg r) ∧
      c'.nmem = upd c.nmem (O + t)
        (c.nmem (X + t) * c.nmem (Y + t) + K - K * c.nmem (Y + t)) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bXm
  exec_block
  all_goals try ((try config_simp); (try simp only [r20, r21, r23, r24, r25, r26]); omega)
  refine ⟨rfl, ?_, fun r h1 h2 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r20, r21]
  · simp only [upd_apply]; split_ifs <;> omega
  · simp only [r20, r23, r24, r25, r26]

theorem bRf_exec (c : Config) (hc : WordsBounded W c) {t X O : ℕ}
    (r20 : c.nreg 9920 = t) (r21 : c.nreg 9921 = 1) (r23 : c.nreg 9923 = X)
    (r25 : c.nreg 9925 = O)
    (w1 : X + t ≤ W) (w2 : O + t ≤ W) (w3 : t + 1 ≤ W) :
    ∃ c' k, Exec P W bRf c c' k ∧ k = 6 ∧ c'.nreg 9920 = t + 1 ∧
      (∀ r, r ≠ 9920 → ¬ (9940 ≤ r ∧ r ≤ 9945) → c'.nreg r = c.nreg r) ∧
      c'.nmem = upd c.nmem (O + t) (c.nmem (X + t) - t) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bRf
  exec_block
  all_goals try ((try config_simp); (try simp only [r20, r21, r23, r25]); omega)
  refine ⟨rfl, ?_, fun r h1 h2 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r20, r21]
  · simp only [upd_apply]; split_ifs <;> omega
  · simp only [r20, r23, r25]

theorem bG_exec (c : Config) (hc : WordsBounded W c) {t X Y O K : ℕ}
    (r20 : c.nreg 9920 = t) (r21 : c.nreg 9921 = 1) (r23 : c.nreg 9923 = X)
    (r24 : c.nreg 9924 = Y) (r25 : c.nreg 9925 = O) (r26 : c.nreg 9926 = K)
    (w1 : X + c.nmem (Y + t) ≤ W) (w1' : Y + t ≤ W) (w2 : O + t ≤ W) (w3 : t + 1 ≤ W)
    (w4 : c.nmem (X + c.nmem (Y + t)) * K ≤ W) :
    ∃ c' k, Exec P W bG c c' k ∧ k = 8 ∧ c'.nreg 9920 = t + 1 ∧
      (∀ r, r ≠ 9920 → ¬ (9940 ≤ r ∧ r ≤ 9945) → c'.nreg r = c.nreg r) ∧
      c'.nmem = upd c.nmem (O + t) (c.nmem (X + c.nmem (Y + t)) * K) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bG
  exec_block
  all_goals try ((try config_simp); (try simp only [r20, r21, r23, r24, r25, r26]); omega)
  refine ⟨rfl, ?_, fun r h1 h2 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r20, r21]
  · simp only [upd_apply]; split_ifs <;> omega
  · simp only [r20, r23, r24, r25, r26]

/-- The value written by `bSg`. -/
def sgV (lab s K ci : ℕ) : ℕ :=
  s + (1 - ((s - (lab - 1)) + ((lab - 1) - s))) * (ci + K - s)

theorem bSg_exec (c : Config) (hc : WordsBounded W c) {t X Y O K R : ℕ}
    (r20 : c.nreg 9920 = t) (r21 : c.nreg 9921 = 1) (r23 : c.nreg 9923 = X)
    (r24 : c.nreg 9924 = Y) (r25 : c.nreg 9925 = O) (r26 : c.nreg 9926 = K)
    (r29 : c.nreg 9929 = R)
    (w1 : X + t ≤ W) (w1' : Y + t ≤ W) (w2 : O + t ≤ W) (w3 : t + 1 ≤ W)
    (w4 : R + (c.nmem (X + t) - 1) ≤ W)
    (w5 : c.nmem (R + (c.nmem (X + t) - 1)) + K ≤ W)
    (w6 : sgV (c.nmem (X + t)) (c.nmem (Y + t)) K (c.nmem (R + (c.nmem (X + t) - 1))) ≤ W)
    (w7 : (1 - ((c.nmem (Y + t) - (c.nmem (X + t) - 1)) + ((c.nmem (X + t) - 1) - c.nmem (Y + t))))
      * (c.nmem (R + (c.nmem (X + t) - 1)) + K - c.nmem (Y + t)) ≤ W)
    (w8 : (c.nmem (Y + t) - (c.nmem (X + t) - 1)) + ((c.nmem (X + t) - 1) - c.nmem (Y + t)) ≤ W) :
    ∃ c' k, Exec P W bSg c c' k ∧ k = 18 ∧ c'.nreg 9920 = t + 1 ∧
      (∀ r, r ≠ 9920 → ¬ (9940 ≤ r ∧ r ≤ 9945) → c'.nreg r = c.nreg r) ∧
      c'.nmem = upd c.nmem (O + t)
        (sgV (c.nmem (X + t)) (c.nmem (Y + t)) K (c.nmem (R + (c.nmem (X + t) - 1)))) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold sgV at w6
  unfold bSg
  exec_block
  all_goals try ((try config_simp); (try simp only [r20, r21, r23, r24, r25, r26, r29]); omega)
  refine ⟨rfl, ?_, fun r h1 h2 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r20, r21]
  · simp only [upd_apply]; split_ifs <;> omega
  · simp only [r20, r21, r23, r24, r25, r26, r29, sgV]

theorem bMx_exec (c : Config) (hc : WordsBounded W c) {t X Y O R : ℕ}
    (r20 : c.nreg 9920 = t) (r21 : c.nreg 9921 = 1) (r23 : c.nreg 9923 = X)
    (r24 : c.nreg 9924 = Y) (r25 : c.nreg 9925 = O) (r29 : c.nreg 9929 = R)
    (w1 : X + t ≤ W) (w1' : Y + t ≤ W) (w1'' : R + t ≤ W) (w2 : O + t ≤ W) (w3 : t + 1 ≤ W)
    (w4 : c.nmem (Y + t) * c.nmem (X + t) + c.nmem (R + t) ≤ W)
    (w5 : c.nmem (Y + t) * c.nmem (R + t) ≤ W) :
    ∃ c' k, Exec P W bMx c c' k ∧ k = 13 ∧ c'.nreg 9920 = t + 1 ∧
      (∀ r, r ≠ 9920 → ¬ (9940 ≤ r ∧ r ≤ 9945) → c'.nreg r = c.nreg r) ∧
      c'.nmem = upd c.nmem (O + t) (c.nmem (Y + t) * c.nmem (X + t) + c.nmem (R + t) -
        c.nmem (Y + t) * c.nmem (R + t)) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bMx
  exec_block
  all_goals try ((try config_simp); (try simp only [r20, r21, r23, r24, r25, r29]); omega)
  refine ⟨rfl, ?_, fun r h1 h2 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r20, r21]
  · simp only [upd_apply]; split_ifs <;> omega
  · simp only [r20, r23, r24, r25, r29]

/-! ### The loops -/

theorem lAk_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) {bnd n X O K K₂ : ℕ}
    (hb : c.nreg bnd = n) (hbnd : ¬ PfScr bnd) (r23 : c.nreg 9923 = X) (r25 : c.nreg 9925 = O) (r26 : c.nreg 9926 = K) (r27 : c.nreg 9927 = K₂)
    (wn : n + 1 ≤ W) (wO : O + n ≤ W)
    (wX : X + n ≤ W) (w : ∀ t < n, c.nmem (X + t) + K ≤ W)
    (dX : ∀ t < n, ∀ j < t, X + t ≠ O + j) :
    ∃ c' k, Exec P W (pfW bnd bAk) c c' k ∧ k ≤ 9 * n + 4 ∧
      PfOut c c' O n (fun t => c.nmem (X + t) + K - K₂) :=
  pfW_exec _ c hc hW hb hbnd fun t c' ht hw h20 h21 hr hm => by
    have q : ∀ r, ¬ PfScr r → c'.nreg r = c.nreg r := hr
    have hx : c'.nmem (X + t) = c.nmem (X + t) := hm _ (dX t ht)
    obtain ⟨c'', k, ex, hk, a, b, d, e, f, g⟩ := bAk_exec (P := P) (t := t) (X := X) (O := O) (K := K) (K₂ := K₂) c' hw h20 h21
      (by rw [q _ (by unfold PfScr; omega)]; exact r23)
      (by rw [q _ (by unfold PfScr; omega)]; exact r25)
      (by rw [q _ (by unfold PfScr; omega)]; exact r26)
      (by rw [q _ (by unfold PfScr; omega)]; exact r27)
      (by omega) (by omega) (by omega) (by rw [hx]; exact w t ht)
    exact ⟨c'', k, ex, by omega, a, b, by rw [d, hx], e, f, g⟩

theorem lId_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) {bnd n O K : ℕ}
    (hb : c.nreg bnd = n) (hbnd : ¬ PfScr bnd) (r25 : c.nreg 9925 = O) (r26 : c.nreg 9926 = K)
    (wn : n + 1 ≤ W) (wO : O + n ≤ W)
    (w : n + K ≤ W) :
    ∃ c' k, Exec P W (pfW bnd bId) c c' k ∧ k ≤ 6 * n + 4 ∧
      PfOut c c' O n (fun t => t + K) :=
  pfW_exec _ c hc hW hb hbnd fun t c' ht hw h20 h21 hr hm => by
    have q : ∀ r, ¬ PfScr r → c'.nreg r = c.nreg r := hr

    obtain ⟨c'', k, ex, hk, a, b, d, e, f, g⟩ := bId_exec (P := P) (t := t) (O := O) (K := K) c' hw h20 h21
      (by rw [q _ (by unfold PfScr; omega)]; exact r25)
      (by rw [q _ (by unfold PfScr; omega)]; exact r26)
      (by omega) (by omega) (by omega)
    exact ⟨c'', k, ex, by omega, a, b, by rw [d], e, f, g⟩

theorem lSx_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) {bnd n X Y O K : ℕ}
    (hb : c.nreg bnd = n) (hbnd : ¬ PfScr bnd) (r23 : c.nreg 9923 = X) (r24 : c.nreg 9924 = Y) (r25 : c.nreg 9925 = O) (r26 : c.nreg 9926 = K)
    (wn : n + 1 ≤ W) (wO : O + n ≤ W)
    (wX : X + n ≤ W) (wY : Y + n ≤ W) (w : ∀ t < n, c.nmem (X + t) + K ≤ W)
    (dX : ∀ t < n, ∀ j < t, X + t ≠ O + j) (dY : ∀ t < n, ∀ j < t, Y + t ≠ O + j) :
    ∃ c' k, Exec P W (pfW bnd bSx) c c' k ∧ k ≤ 11 * n + 4 ∧
      PfOut c c' O n (fun t => c.nmem (X + t) + K - c.nmem (Y + t)) :=
  pfW_exec _ c hc hW hb hbnd fun t c' ht hw h20 h21 hr hm => by
    have q : ∀ r, ¬ PfScr r → c'.nreg r = c.nreg r := hr
    have hx : c'.nmem (X + t) = c.nmem (X + t) := hm _ (dX t ht)
    have hy : c'.nmem (Y + t) = c.nmem (Y + t) := hm _ (dY t ht)
    obtain ⟨c'', k, ex, hk, a, b, d, e, f, g⟩ := bSx_exec (P := P) (t := t) (X := X) (Y := Y) (O := O) (K := K) c' hw h20 h21
      (by rw [q _ (by unfold PfScr; omega)]; exact r23)
      (by rw [q _ (by unfold PfScr; omega)]; exact r24)
      (by rw [q _ (by unfold PfScr; omega)]; exact r25)
      (by rw [q _ (by unfold PfScr; omega)]; exact r26)
      (by omega) (by omega) (by omega) (by omega) (by rw [hx]; exact w t ht)
    exact ⟨c'', k, ex, by omega, a, b, by rw [d, hx, hy], e, f, g⟩

theorem lDf_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) {bnd n X Y O : ℕ}
    (hb : c.nreg bnd = n) (hbnd : ¬ PfScr bnd) (r23 : c.nreg 9923 = X) (r24 : c.nreg 9924 = Y) (r25 : c.nreg 9925 = O)
    (wn : n + 1 ≤ W) (wO : O + n ≤ W)
    (wX : X + n ≤ W) (wY : Y + n ≤ W) (w : ∀ t < n, c.nmem (X + t) * c.nmem (Y + t) ≤ W)
    (dX : ∀ t < n, ∀ j < t, X + t ≠ O + j) (dY : ∀ t < n, ∀ j < t, Y + t ≠ O + j) :
    ∃ c' k, Exec P W (pfW bnd bDf) c c' k ∧ k ≤ 11 * n + 4 ∧
      PfOut c c' O n (fun t => c.nmem (X + t) - c.nmem (X + t) * c.nmem (Y + t)) :=
  pfW_exec _ c hc hW hb hbnd fun t c' ht hw h20 h21 hr hm => by
    have q : ∀ r, ¬ PfScr r → c'.nreg r = c.nreg r := hr
    have hx : c'.nmem (X + t) = c.nmem (X + t) := hm _ (dX t ht)
    have hy : c'.nmem (Y + t) = c.nmem (Y + t) := hm _ (dY t ht)
    obtain ⟨c'', k, ex, hk, a, b, d, e, f, g⟩ := bDf_exec (P := P) (t := t) (X := X) (Y := Y) (O := O) c' hw h20 h21
      (by rw [q _ (by unfold PfScr; omega)]; exact r23)
      (by rw [q _ (by unfold PfScr; omega)]; exact r24)
      (by rw [q _ (by unfold PfScr; omega)]; exact r25)
      (by omega) (by omega) (by omega) (by omega) (by rw [hx, hy]; exact w t ht)
    exact ⟨c'', k, ex, by omega, a, b, by rw [d, hx, hy], e, f, g⟩

theorem lQ_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) {bnd n X Y O : ℕ}
    (hb : c.nreg bnd = n) (hbnd : ¬ PfScr bnd) (r23 : c.nreg 9923 = X) (r24 : c.nreg 9924 = Y) (r25 : c.nreg 9925 = O)
    (wn : n + 1 ≤ W) (wO : O + n ≤ W)
    (wX : X + n ≤ W) (wY : Y + n ≤ W) (wXY : ∀ t < n, X + c.nmem (Y + t) ≤ W)
    (w : ∀ t < n, c.nmem (X + t) + c.nmem (X + c.nmem (Y + t)) ≤ W)
    (dX : ∀ t < n, ∀ j < t, X + t ≠ O + j) (dY : ∀ t < n, ∀ j < t, Y + t ≠ O + j)
    (dXY : ∀ t < n, ∀ j < t, X + c.nmem (Y + t) ≠ O + j) :
    ∃ c' k, Exec P W (pfW bnd bQ) c c' k ∧ k ≤ 14 * n + 4 ∧
      PfOut c c' O n (fun t => (c.nmem (X + t) + c.nmem (X + c.nmem (Y + t))) -
        ((c.nmem (X + t) + c.nmem (X + c.nmem (Y + t))) - 1)) :=
  pfW_exec _ c hc hW hb hbnd fun t c' ht hw h20 h21 hr hm => by
    have q : ∀ r, ¬ PfScr r → c'.nreg r = c.nreg r := hr
    have hx : c'.nmem (X + t) = c.nmem (X + t) := hm _ (dX t ht)
    have hy : c'.nmem (Y + t) = c.nmem (Y + t) := hm _ (dY t ht)
    have hxy : c'.nmem (X + c.nmem (Y + t)) = c.nmem (X + c.nmem (Y + t)) := hm _ (dXY t ht)
    obtain ⟨c'', k, ex, hk, a, b, d, e, f, g⟩ := bQ_exec (P := P) (t := t) (X := X) (Y := Y) (O := O) c' hw h20 h21
      (by rw [q _ (by unfold PfScr; omega)]; exact r23)
      (by rw [q _ (by unfold PfScr; omega)]; exact r24)
      (by rw [q _ (by unfold PfScr; omega)]; exact r25)
      (by omega) (by omega) (by rw [hy]; exact wXY t ht) (by omega) (by omega)
      (by rw [hy, hx, hxy]; exact w t ht)
    exact ⟨c'', k, ex, by omega, a, b, by rw [d, hy, hx, hxy], e, f, g⟩

theorem lXm_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) {bnd n X Y O K : ℕ}
    (hb : c.nreg bnd = n) (hbnd : ¬ PfScr bnd) (r23 : c.nreg 9923 = X) (r24 : c.nreg 9924 = Y) (r25 : c.nreg 9925 = O) (r26 : c.nreg 9926 = K)
    (wn : n + 1 ≤ W) (wO : O + n ≤ W)
    (wX : X + n ≤ W) (wY : Y + n ≤ W)
    (w : ∀ t < n, c.nmem (X + t) * c.nmem (Y + t) + K ≤ W) (w' : ∀ t < n, K * c.nmem (Y + t) ≤ W)
    (dX : ∀ t < n, ∀ j < t, X + t ≠ O + j) (dY : ∀ t < n, ∀ j < t, Y + t ≠ O + j) :
    ∃ c' k, Exec P W (pfW bnd bXm) c c' k ∧ k ≤ 13 * n + 4 ∧
      PfOut c c' O n (fun t => c.nmem (X + t) * c.nmem (Y + t) + K - K * c.nmem (Y + t)) :=
  pfW_exec _ c hc hW hb hbnd fun t c' ht hw h20 h21 hr hm => by
    have q : ∀ r, ¬ PfScr r → c'.nreg r = c.nreg r := hr
    have hx : c'.nmem (X + t) = c.nmem (X + t) := hm _ (dX t ht)
    have hy : c'.nmem (Y + t) = c.nmem (Y + t) := hm _ (dY t ht)
    obtain ⟨c'', k, ex, hk, a, b, d, e, f, g⟩ := bXm_exec (P := P) (t := t) (X := X) (Y := Y) (O := O) (K := K) c' hw h20 h21
      (by rw [q _ (by unfold PfScr; omega)]; exact r23)
      (by rw [q _ (by unfold PfScr; omega)]; exact r24)
      (by rw [q _ (by unfold PfScr; omega)]; exact r25)
      (by rw [q _ (by unfold PfScr; omega)]; exact r26)
      (by omega) (by omega) (by omega) (by omega) (by rw [hx, hy]; exact w t ht)
      (by rw [hy]; exact w' t ht)
    exact ⟨c'', k, ex, by omega, a, b, by rw [d, hx, hy], e, f, g⟩

theorem lRf_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) {bnd n X O : ℕ}
    (hb : c.nreg bnd = n) (hbnd : ¬ PfScr bnd) (r23 : c.nreg 9923 = X) (r25 : c.nreg 9925 = O)
    (wn : n + 1 ≤ W) (wO : O + n ≤ W)
    (wX : X + n ≤ W) (dX : ∀ t < n, ∀ j < t, X + t ≠ O + j) :
    ∃ c' k, Exec P W (pfW bnd bRf) c c' k ∧ k ≤ 8 * n + 4 ∧
      PfOut c c' O n (fun t => c.nmem (X + t) - t) :=
  pfW_exec _ c hc hW hb hbnd fun t c' ht hw h20 h21 hr hm => by
    have q : ∀ r, ¬ PfScr r → c'.nreg r = c.nreg r := hr
    have hx : c'.nmem (X + t) = c.nmem (X + t) := hm _ (dX t ht)
    obtain ⟨c'', k, ex, hk, a, b, d, e, f, g⟩ := bRf_exec (P := P) (t := t) (X := X) (O := O) c' hw h20 h21
      (by rw [q _ (by unfold PfScr; omega)]; exact r23)
      (by rw [q _ (by unfold PfScr; omega)]; exact r25)
      (by omega) (by omega) (by omega)
    exact ⟨c'', k, ex, by omega, a, b, by rw [d, hx], e, f, g⟩

theorem lG_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) {bnd n X Y O K : ℕ}
    (hb : c.nreg bnd = n) (hbnd : ¬ PfScr bnd) (r23 : c.nreg 9923 = X) (r24 : c.nreg 9924 = Y) (r25 : c.nreg 9925 = O) (r26 : c.nreg 9926 = K)
    (wn : n + 1 ≤ W) (wO : O + n ≤ W)
    (wY : Y + n ≤ W) (wXY : ∀ t < n, X + c.nmem (Y + t) ≤ W)
    (w : ∀ t < n, c.nmem (X + c.nmem (Y + t)) * K ≤ W)
    (dY : ∀ t < n, ∀ j < t, Y + t ≠ O + j) (dXY : ∀ t < n, ∀ j < t, X + c.nmem (Y + t) ≠ O + j) :
    ∃ c' k, Exec P W (pfW bnd bG) c c' k ∧ k ≤ 10 * n + 4 ∧
      PfOut c c' O n (fun t => c.nmem (X + c.nmem (Y + t)) * K) :=
  pfW_exec _ c hc hW hb hbnd fun t c' ht hw h20 h21 hr hm => by
    have q : ∀ r, ¬ PfScr r → c'.nreg r = c.nreg r := hr
    have hy : c'.nmem (Y + t) = c.nmem (Y + t) := hm _ (dY t ht)
    have hxy : c'.nmem (X + c.nmem (Y + t)) = c.nmem (X + c.nmem (Y + t)) := hm _ (dXY t ht)
    obtain ⟨c'', k, ex, hk, a, b, d, e, f, g⟩ := bG_exec (P := P) (t := t) (X := X) (Y := Y) (O := O) (K := K) c' hw h20 h21
      (by rw [q _ (by unfold PfScr; omega)]; exact r23)
      (by rw [q _ (by unfold PfScr; omega)]; exact r24)
      (by rw [q _ (by unfold PfScr; omega)]; exact r25)
      (by rw [q _ (by unfold PfScr; omega)]; exact r26)
      (by rw [hy]; exact wXY t ht) (by omega) (by omega) (by omega)
      (by rw [hy, hxy]; exact w t ht)
    exact ⟨c'', k, ex, by omega, a, b, by rw [d, hy, hxy], e, f, g⟩

theorem lSg_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) {bnd n X Y O K R : ℕ}
    (hb : c.nreg bnd = n) (hbnd : ¬ PfScr bnd) (r23 : c.nreg 9923 = X) (r24 : c.nreg 9924 = Y) (r25 : c.nreg 9925 = O) (r26 : c.nreg 9926 = K) (r29 : c.nreg 9929 = R)
    (wn : n + 1 ≤ W) (wO : O + n ≤ W)
    (wX : X + n ≤ W) (wY : Y + n ≤ W) (wR : ∀ t < n, R + (c.nmem (X + t) - 1) ≤ W)
    (w5 : ∀ t < n, c.nmem (R + (c.nmem (X + t) - 1)) + K ≤ W)
    (w6 : ∀ t < n, sgV (c.nmem (X + t)) (c.nmem (Y + t)) K (c.nmem (R + (c.nmem (X + t) - 1))) ≤ W)
    (w7 : ∀ t < n, (1 - ((c.nmem (Y + t) - (c.nmem (X + t) - 1)) +
      ((c.nmem (X + t) - 1) - c.nmem (Y + t)))) *
      (c.nmem (R + (c.nmem (X + t) - 1)) + K - c.nmem (Y + t)) ≤ W)
    (w8 : ∀ t < n, (c.nmem (Y + t) - (c.nmem (X + t) - 1)) + ((c.nmem (X + t) - 1) - c.nmem (Y + t)) ≤ W)
    (dX : ∀ t < n, ∀ j < t, X + t ≠ O + j) (dY : ∀ t < n, ∀ j < t, Y + t ≠ O + j)
    (dR : ∀ t < n, ∀ j < t, R + (c.nmem (X + t) - 1) ≠ O + j) :
    ∃ c' k, Exec P W (pfW bnd bSg) c c' k ∧ k ≤ 20 * n + 4 ∧
      PfOut c c' O n (fun t => sgV (c.nmem (X + t)) (c.nmem (Y + t)) K (c.nmem (R + (c.nmem (X + t) - 1)))) :=
  pfW_exec _ c hc hW hb hbnd fun t c' ht hw h20 h21 hr hm => by
    have q : ∀ r, ¬ PfScr r → c'.nreg r = c.nreg r := hr
    have hx : c'.nmem (X + t) = c.nmem (X + t) := hm _ (dX t ht)
    have hy : c'.nmem (Y + t) = c.nmem (Y + t) := hm _ (dY t ht)
    have hr' : c'.nmem (R + (c.nmem (X + t) - 1)) = c.nmem (R + (c.nmem (X + t) - 1)) :=
      hm _ (dR t ht)
    obtain ⟨c'', k, ex, hk, a, b, d, e, f, g⟩ := bSg_exec (P := P) (t := t) (X := X) (Y := Y) (O := O) (K := K) (R := R) c' hw h20 h21
      (by rw [q _ (by unfold PfScr; omega)]; exact r23)
      (by rw [q _ (by unfold PfScr; omega)]; exact r24)
      (by rw [q _ (by unfold PfScr; omega)]; exact r25)
      (by rw [q _ (by unfold PfScr; omega)]; exact r26)
      (by rw [q _ (by unfold PfScr; omega)]; exact r29)
      (by omega) (by omega) (by omega) (by omega) (by rw [hx]; exact wR t ht)
      (by rw [hx, hr']; exact w5 t ht) (by rw [hx, hy, hr']; exact w6 t ht)
      (by rw [hx, hy, hr']; exact w7 t ht) (by rw [hx, hy]; exact w8 t ht)
    exact ⟨c'', k, ex, by omega, a, b, by rw [d, hx, hy, hr'], e, f, g⟩

theorem lMx_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) {bnd n X Y O R : ℕ}
    (hb : c.nreg bnd = n) (hbnd : ¬ PfScr bnd) (r23 : c.nreg 9923 = X) (r24 : c.nreg 9924 = Y) (r25 : c.nreg 9925 = O) (r29 : c.nreg 9929 = R)
    (wn : n + 1 ≤ W) (wO : O + n ≤ W)
    (wX : X + n ≤ W) (wY : Y + n ≤ W) (wR : R + n ≤ W)
    (w : ∀ t < n, c.nmem (Y + t) * c.nmem (X + t) + c.nmem (R + t) ≤ W)
    (w' : ∀ t < n, c.nmem (Y + t) * c.nmem (R + t) ≤ W)
    (dX : ∀ t < n, ∀ j < t, X + t ≠ O + j) (dY : ∀ t < n, ∀ j < t, Y + t ≠ O + j)
    (dR : ∀ t < n, ∀ j < t, R + t ≠ O + j) :
    ∃ c' k, Exec P W (pfW bnd bMx) c c' k ∧ k ≤ 15 * n + 4 ∧
      PfOut c c' O n (fun t => c.nmem (Y + t) * c.nmem (X + t) + c.nmem (R + t) - c.nmem (Y + t) * c.nmem (R + t)) :=
  pfW_exec _ c hc hW hb hbnd fun t c' ht hw h20 h21 hr hm => by
    have q : ∀ r, ¬ PfScr r → c'.nreg r = c.nreg r := hr
    have hx : c'.nmem (X + t) = c.nmem (X + t) := hm _ (dX t ht)
    have hy : c'.nmem (Y + t) = c.nmem (Y + t) := hm _ (dY t ht)
    have hr' : c'.nmem (R + t) = c.nmem (R + t) := hm _ (dR t ht)
    obtain ⟨c'', k, ex, hk, a, b, d, e, f, g⟩ := bMx_exec (P := P) (t := t) (X := X) (Y := Y) (O := O) (R := R) c' hw h20 h21
      (by rw [q _ (by unfold PfScr; omega)]; exact r23)
      (by rw [q _ (by unfold PfScr; omega)]; exact r24)
      (by rw [q _ (by unfold PfScr; omega)]; exact r25)
      (by rw [q _ (by unfold PfScr; omega)]; exact r29)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hx, hy, hr']; exact w t ht) (by rw [hy, hr']; exact w' t ht)
    exact ⟨c'', k, ex, by omega, a, b, by rw [d, hx, hy, hr'], e, f, g⟩

end NcFz

end BKMNW

end PlanarFlow
