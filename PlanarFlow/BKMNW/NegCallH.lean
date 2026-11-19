module

public import PlanarFlow.BKMNW.NegCallZ

/-!
# The in-place call with its heap bounds computed on the machine

`negCallZ_exec` takes the heap base `rtHb n L G` and the heap top `rtH n L G m k` of the call's
root image in the registers `7320`, `7321`. Here they are **computed** from the header of the
`InP` frame at `A = r7325` (`n = mem[A]`, `m = mem[A + 1]`, `k = mem[A + 2]`, `L = mem[A + 3]`)
and the vertex-identifier bound `G` in `r7326`, by the blocks of the setup of `negFix`
(`prepLog`, `prepB0`: `spWs n`; the compiled polynomial `PE.comp 3102 PE.WNbE 3105`: `WNb n L`):

* `nhbA` (`fxA` reading the header at `A`), **`nhbF`** `= nhbA ; prepLog ; prepB0 ; fxB ; PE.comp`,
  `nhbC` (`rtHb = 3 spWs n + G + WNb n L + 4`, `rtH = rtHb + 5 + fsz m k`), **`ncHb`** `= nhbF ; nhbC`;
  `nhbF_exec`, `nhbC_exec`, **`ncHb_exec`** (within `12 n + 4627 + 18` steps, registers only);
* **`negCallH`** `= ncHb ; negCallZ`, **`negCallH_exec`**: `negCallZ_exec` without the register
  hypotheses on `7320`, `7321`, with `r7326 = G` and the word bounds of the setup
  (`spWs n + 205 ≤ W`, `fxWB n L ≤ W`), within
  `9 · negT C C₀ n + 12 · fsz m k + 7 · fin m k + 3291 + (12 n + 4645)` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP
  NegSSSP.Driver NegSSSP.Frame CombMap

universe w

/-! ### The programs -/

/-- `r2966 = 1`, `r2967 = 2`, `r2969 = n`, `r2970 = 3n`, `r2971 = 0`, `r3102 = n`, `r3103 = L`
(the header of the frame at `A = r7325`). -/
def nhbA : Stmt := block [.constN 2966 1, .constN 2967 2, .copyN 2975 7325,
  .loadN 2969 2975, .addN 2970 2969 2969, .addN 2970 2970 2969, .constN 2971 0,
  .constN 2976 3, .addN 2975 2975 2976, .loadN 3103 2975, .copyN 3102 2969]

/-- `r3104 = spWs n`, `r3105 = WNb n L`. -/
def nhbF : Stmt := .seq nhbA (.seq prepLog (.seq prepB0 (.seq fxB (PE.comp 3102 PE.WNbE 3105))))

/-- `r7320 = 3 spWs n + G + WNb n L + 4` (`G = r7326`), `r7321 = r7320 + 5 + (6 + 5k + 5m)`
(`m = mem[A + 1]`, `k = mem[A + 2]`); scratch `7327 … 7329`. -/
def nhbC : Stmt := block [.addN 7327 3104 3104, .addN 7327 7327 3104, .addN 7327 7327 7326,
  .addN 7327 7327 3105, .constN 7328 4, .addN 7320 7327 7328,
  .constN 7328 1, .addN 7329 7325 7328, .loadN 7327 7329, .addN 7329 7329 7328,
  .loadN 7328 7329, .addN 7327 7327 7328, .addN 7328 7327 7327, .addN 7328 7328 7328,
  .addN 7328 7328 7327, .addN 7321 7320 7328, .constN 7327 11, .addN 7321 7321 7327]

/-- **The heap bounds of the call's root image**, computed from the frame at `A`. -/
def ncHb : Stmt := .seq nhbF nhbC

/-- **The in-place call with its heap bounds computed.** -/
def negCallH : Stmt := .seq ncHb negCallZ

theorem wnbComp_facts : (PE.comp 3102 PE.WNbE 3105).regsOK nfU = true ∧
    (PE.comp 3102 PE.WNbE 3105).noInp = true ∧ (PE.comp 3102 PE.WNbE 3105).noRand = true := by
  decide +kernel

/-- A run of a program naming only the registers of `U` (no input, no randomness) keeps every
register outside `U`. -/
theorem keep_of_regsOK {P : Input} {W : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) {U : ℕ → Bool} (hs : s.regsOK U = true) (hn : s.noInp = true)
    (hr : s.noRand = true) : ∀ r, U r = false → c'.nreg r = c.nreg r := by
  obtain ⟨d', e, -, hK, -⟩ := Exec.lift (P' := P) h hs hn hr le_rfl
    ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩ h.wb_left
  have hd : c' = d' := (h.det e).1
  rw [hd]
  exact hK.nreg

section Blocks

variable {P : Input} {W : ℕ}

theorem nhbA_exec (c : Config) (hc : WordsBounded W c) {A n L : ℕ} (r25 : c.nreg 7325 = A)
    (hn : c.nmem A = n) (hL : c.nmem (A + 3) = L) (w1 : A + 3 ≤ W) (w2 : 3 * n ≤ W) :
    ∃ c' t, Exec P W nhbA c c' t ∧ t = 11 ∧ c'.nreg 2966 = 1 ∧ c'.nreg 2967 = 2 ∧
      c'.nreg 2969 = n ∧ c'.nreg 2970 = n + n + n ∧ c'.nreg 2971 = 0 ∧ c'.nreg 3102 = n ∧
      c'.nreg 3103 = L ∧ (∀ r, (r < 2966 ∨ (2976 < r ∧ r < 3102) ∨ 3103 < r) →
        c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hnW : n ≤ W := by omega
  unfold nhbA
  exec_block
  all_goals try ((try config_simp); (try simp only [r25, hn, hL]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r25, hn, hL])
  simp only [upd_apply]; split_ifs <;> omega

/-- **`spWs n` and `WNb n L` from the frame's header**, registers `< 3200` only, the registers
`2979 … 3099` kept. -/
theorem nhbF_exec (c : Config) (hc : WordsBounded W c) {A n L : ℕ} (r25 : c.nreg 7325 = A)
    (hn : c.nmem A = n) (hL : c.nmem (A + 3) = L) (w1 : A + 3 ≤ W)
    (w2 : spWs n + 205 ≤ W) (w3 : fxWB n L ≤ W) :
    ∃ c' t, Exec P W nhbF c c' t ∧ t ≤ 12 * n + 4610 ∧ c'.nreg 3104 = spWs n ∧
      c'.nreg 3105 = WNb n L ∧ (∀ r, 2978 < r → r < 3100 → c'.nreg r = c.nreg r) ∧
      (∀ r, 3200 ≤ r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hsp : 66 * n + 35 ≤ spWs n := by unfold spWs; omega
  obtain ⟨c₁, t₁, e₁, ht₁, a66, a67, a69, a70, a71, a02, a03, ak, am, ar, arm, ao⟩ :=
    nhbA_exec (P := P) c hc r25 hn hL w1 (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, b71, bk, bm, br, brm, bo⟩ :=
    prepLog_exec (P := P) c₁ e₁.wb_right a66 a67 a70 a71 (by omega)
  have b71' : c₂.nreg 2971 = Nat.log 2 (3 * n) := by
    rw [b71, show n + n + n = 3 * n by omega]
  obtain ⟨c₃, t₃, e₃, ht₃, -, d73, -, d78, dk, dm, dr, drm, do'⟩ :=
    prepB0_exec (P := P) (k := n) c₂ e₂.wb_right (by rw [bk _ (by omega) (by omega)]; exact a66)
      (by rw [bk _ (by omega) (by omega)]; exact a67)
      (by rw [bk _ (by omega) (by omega)]; exact a69) b71' w2
  obtain ⟨c₄, t₄, e₄, ht₄, f04, f00, fk, fm, fr, frm, fo⟩ := fxB_exec (P := P) c₃ e₃.wb_right
  have v0 : c₄.nreg 3102 = n := by
    rw [fk _ (by omega) (by omega), dk _ (Or.inr ⟨by omega, by omega⟩),
      bk _ (by omega) (by omega)]; exact a02
  have v1 : c₄.nreg 3103 = L := by
    rw [fk _ (by omega) (by omega), dk _ (Or.inr ⟨by omega, by omega⟩),
      bk _ (by omega) (by omega)]; exact a03
  have v2 : c₄.nreg 3104 = spWs n := by rw [f04, d73]
  have hρ : ∀ i < 3, fxρ n L i = c₄.nreg (3102 + i) := by
    intro i hi
    interval_cases i
    · exact v0.symm
    · exact v1.symm
    · exact v2.symm
  have hvl := PE.varsLt_of_vl PE.WNbE_vl
  have hcg := PE.eval_congr hρ hvl
  obtain ⟨c₅, e₅, g05, gk, gm, gr, grm, go⟩ :=
    PE.comp_exec (P := P) 3102 3 PE.WNbE 3105 hvl le_rfl c₄ e₄.wb_right
      (by rw [← hcg.2]; exact w3)
  have ex : Exec P W nhbF c c₅ _ := Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ e₅)))
  have g5 : ∀ r, 3200 ≤ r → c₅.nreg r = c₄.nreg r := fun r hr =>
    keep_of_regsOK e₅ wnbComp_facts.1 wnbComp_facts.2.1 wnbComp_facts.2.2 r
      (by simp only [nfR, decide_eq_false_iff_not, not_lt]; omega)
  refine ⟨c₅, _, ex, ?_, ?_, ?_, fun r h1 h2 => ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [WNbE_cost]; omega
  · rw [gk _ (by omega), v2]
  · rw [g05, ← hcg.1]
    exact PE.eval_WNbE (fxρ n L) rfl
  · rw [gk _ (by omega), fk _ (by omega) (by omega),
      dk _ (Or.inr ⟨by omega, by omega⟩), bk _ (by omega) (by omega), ak _ (Or.inr (Or.inl
        ⟨by omega, by omega⟩))]
  · rw [g5 r hr, fk _ (by omega) (by omega), dk _ (Or.inr ⟨by omega, by omega⟩),
      bk _ (by omega) (by omega), ak _ (Or.inr (Or.inr (by omega)))]
  · rw [gm, fm, dm, bm, am]
  · rw [gr, fr, dr, br, ar]
  · rw [grm, frm, drm, brm, arm]
  · rw [go, fo, do', bo, ao]

theorem nhbC_exec (c : Config) (hc : WordsBounded W c) {A G S N m k : ℕ}
    (r04 : c.nreg 3104 = S) (r05 : c.nreg 3105 = N) (r25 : c.nreg 7325 = A)
    (r26 : c.nreg 7326 = G) (hm : c.nmem (A + 1) = m) (hk : c.nmem (A + 2) = k)
    (w1 : 3 * S + G + N + 4 + 5 + (6 + 5 * k + 5 * m) ≤ W) (w2 : A + 2 ≤ W) :
    ∃ c' t, Exec P W nhbC c c' t ∧ t = 18 ∧ c'.nreg 7320 = 3 * S + G + N + 4 ∧
      c'.nreg 7321 = 3 * S + G + N + 4 + 5 + (6 + 5 * k + 5 * m) ∧
      (∀ r, r ≠ 7320 → r ≠ 7321 → (r < 7327 ∨ 7329 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold nhbC
  exec_block
  all_goals try ((try config_simp); (try simp only [r04, r05, r25, r26, hm, hk]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r04, r05, r25, r26, hm, hk]; omega)
  simp only [upd_apply]; split_ifs <;> omega

/-- **The heap bounds of the call's root image** from the frame's header and `G = r7326`. -/
theorem ncHb_exec (c : Config) (hc : WordsBounded W c) {A n L G m k : ℕ}
    (r25 : c.nreg 7325 = A) (r26 : c.nreg 7326 = G) (hn : c.nmem A = n)
    (hm : c.nmem (A + 1) = m) (hk : c.nmem (A + 2) = k) (hL : c.nmem (A + 3) = L)
    (w1 : A + 3 ≤ W) (w2 : spWs n + 205 ≤ W) (w3 : fxWB n L ≤ W)
    (w4 : rtH n L G m k ≤ W) :
    ∃ c' t, Exec P W ncHb c c' t ∧ t ≤ 12 * n + 4628 ∧ c'.nreg 7320 = rtHb n L G ∧
      c'.nreg 7321 = rtH n L G m k ∧ (∀ r, 2978 < r → r < 3100 → c'.nreg r = c.nreg r) ∧
      (∀ r, 3200 ≤ r → r ≠ 7320 → r ≠ 7321 → (r < 7327 ∨ 7329 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, s04, s05, k1, k2, m1, r1, rm1, o1⟩ :=
    nhbF_exec (P := P) (A := A) (n := n) (L := L) c hc r25 hn hL w1 w2 w3
  have hH : rtH n L G m k = 3 * spWs n + G + WNb n L + 4 + 5 + (6 + 5 * k + 5 * m) := by
    unfold rtH rtHb Frame.fsz; ring
  obtain ⟨c₂, t₂, e₂, ht₂, h20, h21, k3, m2, r2, rm2, o2⟩ :=
    nhbC_exec (P := P) (A := A) (G := G) (m := m) (k := k) c₁ e₁.wb_right s04 s05 (by rw [k2 _ (by omega)]; exact r25)
      (by rw [k2 _ (by omega)]; exact r26) (by rw [m1]; exact hm) (by rw [m1]; exact hk)
      (by rw [← hH]; exact w4) (by omega)
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, by rw [h20]; rfl, by rw [h21, hH], fun r h1 h2 => ?_,
    fun r h1 h2 h3 h4 => ?_, by rw [m2, m1], by rw [r2, r1], by rw [rm2, rm1], by rw [o2, o1]⟩
  · rw [k3 r (by omega) (by omega) (by omega), k1 r h1 h2]
  · rw [k3 r h2 h3 h4, k2 r h1]

end Blocks

section Call

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-- **The in-place call with its heap bounds computed** (see the module docstring):
`negCallZ_exec` with `rtHb`, `rtH` computed by `ncHb` from the frame at `A` and `G = r7326`. -/
theorem negCallH_exec (C C₀ : ℕ) (hC : 200000 ≤ C) (g : GIds D F) {M : CombMap D V F}
    {ℓ : D → ℤ} (hpre : NegPre M ℓ) (I P' : Input) {W Wz A Ob p : ℕ} (d : Config)
    (hd : WordsBounded W d) (r22 : d.nreg 7322 = Ob) (r24 : d.nreg 7324 = p)
    (r25 : d.nreg 7325 = A) (r26 : d.nreg 7326 = g.G)
    (hz : ∀ a ≤ Wz, d.nmem a = 0)
    (hin : InP g M.dual (minLen M.dual ℓ) (rtL M ℓ) (Fintype.card D) (repsN M.dual g.gd) A
      (A + Frame.fsz (repsN M.dual g.gd).card (ck M.dual (repsN M.dual g.gd))) d)
    (hWz : rtW (Fintype.card D) (rtL M ℓ) g.G ≤ Wz) (hA : Wz < A)
    (hAO : A + Frame.fsz (repsN M.dual g.gd).card (ck M.dual (repsN M.dual g.gd)) ≤ Ob)
    (hOp : Ob + Frame.fsz (repsN M.dual g.gd).card (ck M.dual (repsN M.dual g.gd)) ≤ p)
    (hpW : p + negT C C₀ (Fintype.card D) ≤ W)
    (hw2 : spWs (Fintype.card D) + 205 ≤ W) (hw3 : fxWB (Fintype.card D) (rtL M ℓ) ≤ W) :
    ∃ d' t, Exec P' W negCallH d d' t ∧
      t ≤ 9 * negT C C₀ (Fintype.card D) +
        12 * Frame.fsz (repsN M.dual g.gd).card (ck M.dual (repsN M.dual g.gd)) +
        7 * Frame.fin (repsN M.dual g.gd).card (ck M.dual (repsN M.dual g.gd)) + 3291 +
        (12 * Fintype.card D + 4628) ∧
      (∀ a ≤ Wz, d'.nmem a = 0) ∧
      Res g M.dual (rtL M ℓ) (repsN M.dual g.gd) (negMach g M I ℓ) Ob
        (Ob + Frame.fsz (repsN M.dual g.gd).card (ck M.dual (repsN M.dual g.gd))) d' ∧
      (∀ a, Wz < a →
        (a < Ob ∨ Ob + Frame.fsz (repsN M.dual g.gd).card (ck M.dual (repsN M.dual g.gd)) ≤ a) →
        (a < p ∨ p + negT C C₀ (Fintype.card D) ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r, 3000 ≤ r → r ≤ 3012 → d'.nreg r = d.nreg r) ∧
      (∀ r, ¬ ncScr r → d'.nreg r = d.nreg r) ∧
      d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  have hhW : rtH (Fintype.card D) (rtL M ℓ) g.G (repsN M.dual g.gd).card
      (ck M.dual (repsN M.dual g.gd)) ≤ rtW (Fintype.card D) (rtL M ℓ) g.G :=
    rtH_le_rtW (card_le_n _) (ck_le_n M.dual _)
  have hT : 4610 ≤ negT C C₀ (Fintype.card D) := by unfold negT; omega
  have hfsz : Frame.fsz (repsN M.dual g.gd).card (ck M.dual (repsN M.dual g.gd)) =
      6 + 5 * ck M.dual (repsN M.dual g.gd) + 5 * (repsN M.dual g.gd).card := rfl
  obtain ⟨d₁, t₁, e₁, ht₁, h20, h21, k1, k2, m1, r1, rm1, o1⟩ :=
    ncHb_exec (P := P') d hd r25 r26 hin.rn hin.rm hin.rk hin.rL (by omega) hw2 hw3 (by omega)
  have hin₁ := inP_stab hin (memEq_of_eq m1 rm1 _ _)
  obtain ⟨d', t, ex, ht, hz', hres, hkm, hk1, hk2, hr', hrm', ho'⟩ :=
    negCallZ_exec C C₀ hC g hpre I P' d₁ e₁.wb_right h20 h21
      (by rw [k2 _ (by omega) (by omega) (by omega) (by omega)]; exact r22)
      (by rw [k2 _ (by omega) (by omega) (by omega) (by omega)]; exact r24)
      (by rw [k2 _ (by omega) (by omega) (by omega) (by omega)]; exact r25)
      (fun a ha => by rw [m1]; exact hz a ha) hin₁ hWz hA hAO hOp hpW
  refine ⟨d', t₁ + t, .seq e₁ ex, by omega, hz', hres, fun a h1 h2 h3 => ?_,
    fun r h1 h2 => ?_, fun r hr => ?_, by rw [hr', r1], by rw [hrm', rm1], by rw [ho', o1]⟩
  · rw [hkm a h1 h2 h3, m1]
  · rw [hk1 r h1 h2, k1 r (by omega) (by omega)]
  · have hr3 : 3200 ≤ r := by unfold ncScr at hr; omega
    rw [hk2 r hr, k2 r hr3 (by unfold ncScr at hr; omega) (by unfold ncScr at hr; omega)
      (by unfold ncScr at hr; omega)]

end Call

end MfDrv

end BKMNW

end PlanarFlow
