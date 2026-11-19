module

public import WordRAM.Programs.Tactics

/-!
# The leaf solver of the maximum-flow recursion, on the machine

The leaf solver of Algorithm 1 (`PlanarFlow.BKMNW.leafSolve`) decides the flow dart by dart from
the ranks of the ends of the dart (sources `0`, holes `1`, sinks `2`, other vertices `3`): the
capacity of the dart if it goes up in rank, minus the capacity of its reverse if it goes down,
`0` otherwise. The program `PlanarFlow.LeafFlow.prog` does this on arrays: `n` darts, the tail,
the head and the reverse of the dart `d` in the natural memory at `tb + d`, `hb + d`, `rb + d`, the
rank of the vertex `v` at `kb + v`, the capacity of `d` in the real memory at `ub + d`; it writes
the flow of `d` in the real memory at `fb + d`.

* `prog_exec`: **the program halts within `25 n + 5` steps** and writes `fval` of the ranks and
  capacities at `fb + d` for every dart `d < n`, changing nothing else but scratch registers.

Registers: inputs `r1 = n`, `r3 = tb`, `r4 = hb`, `r5 = rb`, `r6 = kb`, `r8 = ub`, `r9 = fb`; `r7 = 1`
and `r10 = 3` (set by the program); the counter `r20`; scratch `r22`–`r26` and the real registers
`0`–`2`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace LeafFlow

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- The flow of a dart from the ranks `a` of its tail and `b` of its head, its capacity `u` and
the capacity `u'` of its reverse. -/
def fval (a b : ℕ) (u u' : ℤ) : ℤ :=
  if a < 3 ∧ b < 3 then (if a < b then u else if b < a then -u' else 0) else 0

/-- Up in rank: the capacity of the dart `r20`. -/
def up : Stmt := block [.addN 22 8 20, .loadR 0 22]

/-- Down in rank: minus the capacity of the reverse of the dart `r20`. -/
def down : Stmt := block [.addN 22 5 20, .loadN 23 22, .addN 22 8 23, .loadR 1 22, .constR 2 0,
  .subR 0 2 1]

/-- The decision on the ranks `r24` (tail) and `r25` (head). -/
def dec : Stmt := .ifLtN 24 10 (.ifLtN 25 10 (.ifLtN 24 25 up (.ifLtN 25 24 down .skip)) .skip) .skip

/-- The ranks of the ends of the dart `r20`, the address of its flow, and `rreg 0 := 0`. -/
def ranks : Stmt := block [.addN 22 3 20, .loadN 23 22, .addN 22 6 23, .loadN 24 22,
  .addN 22 4 20, .loadN 23 22, .addN 22 6 23, .loadN 25 22, .addN 26 9 20, .constR 0 0]

/-- One dart. -/
def step : Stmt := .seq ranks (.seq dec (block [.storeR 26 0, .addN 20 20 7]))

/-- **The leaf solver.** -/
def prog : Stmt := .seq (block [.constN 7 1, .constN 10 3, .constN 20 0]) (.whileLtN 20 1 step)

/-! ### The hypotheses -/

/-- The sizes and the layout fit the word bound, the capacities lie below the flows, and the ends
and reverses of the darts are in range. -/
structure Hyp (W n nv tb hb rb kb ub fb : ℕ) (TL HD RV : ℕ → ℕ) : Prop where
  tbW : tb + n ≤ W
  hbW : hb + n ≤ W
  rbW : rb + n ≤ W
  kbW : kb + nv ≤ W
  ubW : ub + n ≤ W
  fbW : fb + n ≤ W
  nW : n + 1 ≤ W
  W3 : 3 ≤ W
  disj : ub + n ≤ fb
  TL_lt : ∀ d < n, TL d < nv
  HD_lt : ∀ d < n, HD d < nv
  RV_lt : ∀ d < n, RV d < n

/-- The input in the configuration. -/
structure Inp (n tb hb rb kb ub fb : ℕ) (TL HD RV K : ℕ → ℕ) (U : ℕ → ℤ) (c : Config) : Prop where
  r1 : c.nreg 1 = n
  r3 : c.nreg 3 = tb
  r4 : c.nreg 4 = hb
  r5 : c.nreg 5 = rb
  r6 : c.nreg 6 = kb
  r8 : c.nreg 8 = ub
  r9 : c.nreg 9 = fb
  tl : ∀ d < n, c.nmem (tb + d) = TL d
  hd : ∀ d < n, c.nmem (hb + d) = HD d
  rv : ∀ d < n, c.nmem (rb + d) = RV d
  rk : ∀ v, c.nmem (kb + v) = K v
  cap : ∀ d < n, c.rmem (ub + d) = U d

/-- The input registers. -/
def IsIn (r : ℕ) : Prop := r = 1 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 8 ∨ r = 9

/-- What the program keeps. -/
structure Frame (n fb : ℕ) (c₀ c : Config) : Prop where
  regs : ∀ r, IsIn r → c.nreg r = c₀.nreg r
  nmem : c.nmem = c₀.nmem
  rmem : ∀ a, a < fb ∨ fb + n ≤ a → c.rmem a = c₀.rmem a
  out : c.output = c₀.output

lemma Frame.trans {n fb : ℕ} {c₀ c₁ c₂ : Config} (h₁ : Frame n fb c₀ c₁) (h₂ : Frame n fb c₁ c₂) :
    Frame n fb c₀ c₂ :=
  ⟨fun r h => (h₂.regs r h).trans (h₁.regs r h), h₂.nmem.trans h₁.nmem,
    fun a ha => (h₂.rmem a ha).trans (h₁.rmem a ha), h₂.out.trans h₁.out⟩

variable {W n nv tb hb rb kb ub fb : ℕ} {TL HD RV K : ℕ → ℕ} {U : ℕ → ℤ}

lemma Inp.of_frame (hy : Hyp W n nv tb hb rb kb ub fb TL HD RV) {c₀ c : Config}
    (h₀ : Inp n tb hb rb kb ub fb TL HD RV K U c₀) (hf : Frame n fb c₀ c) :
    Inp n tb hb rb kb ub fb TL HD RV K U c where
  r1 := (hf.regs 1 (by simp [IsIn])).trans h₀.r1
  r3 := (hf.regs 3 (by simp [IsIn])).trans h₀.r3
  r4 := (hf.regs 4 (by simp [IsIn])).trans h₀.r4
  r5 := (hf.regs 5 (by simp [IsIn])).trans h₀.r5
  r6 := (hf.regs 6 (by simp [IsIn])).trans h₀.r6
  r8 := (hf.regs 8 (by simp [IsIn])).trans h₀.r8
  r9 := (hf.regs 9 (by simp [IsIn])).trans h₀.r9
  tl d hd := by rw [hf.nmem]; exact h₀.tl d hd
  hd d hd := by rw [hf.nmem]; exact h₀.hd d hd
  rv d hd := by rw [hf.nmem]; exact h₀.rv d hd
  rk v := by rw [hf.nmem]; exact h₀.rk v
  cap d hd := by rw [hf.rmem _ (Or.inl (by have := hy.disj; omega))]; exact h₀.cap d hd

/-! ### The decision -/

theorem dec_exec {P : Input} (hy : Hyp W n nv tb hb rb kb ub fb TL HD RV) (c : Config)
    (hc : WordsBounded W c) (hI : Inp n tb hb rb kb ub fb TL HD RV K U c) (hd : c.nreg 20 < n)
    (h10 : c.nreg 10 = 3) (h0 : c.rreg 0 = 0) :
    ∃ c' k, Exec P W dec c c' k ∧ k ≤ 11 ∧
      (∀ r, r ≠ 22 → r ≠ 23 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧
      c'.rreg 0 = fval (c.nreg 24) (c.nreg 25) (U (c.nreg 20)) (U (RV (c.nreg 20))) := by
  have hcap := hI.cap _ hd
  have hrv := hI.rv _ hd
  have hrvl := hy.RV_lt _ hd
  have hcap' := hI.cap _ hrvl
  have := hy.ubW; have := hy.rbW
  unfold dec
  by_cases ha : c.nreg 24 < 3
  · refine spec_ifLtN_true (by rw [h10]; exact ha) ?_
    by_cases hb : c.nreg 25 < 3
    · refine spec_ifLtN_true (by rw [h10]; exact hb) ?_
      by_cases hab : c.nreg 24 < c.nreg 25
      · refine spec_ifLtN_true hab ?_
        unfold up
        exec_block
        · rw [hI.r8]; omega
        refine ⟨by omega, fun r h22 h23 => by config_simp; rw [Machine.upd_other _ _ _ h22], rfl,
          rfl, rfl, ?_⟩
        config_simp
        rw [hI.r8, hcap]
        simp [fval, ha, hb, hab]
      · refine spec_ifLtN_false hab ?_
        by_cases hba : c.nreg 25 < c.nreg 24
        · refine spec_ifLtN_true hba ?_
          unfold down
          exec_block
          · rw [hI.r5]; omega
          · config_simp; rw [hI.r8, hI.r5, hrv]; omega
          refine ⟨by omega, fun r h22 h23 => by
            config_simp; simp only [Machine.upd_apply, h22, h23, ↓reduceIte], rfl, rfl, rfl, ?_⟩
          config_simp
          rw [hI.r8, hI.r5, hrv, hcap']
          simp [fval, ha, hb, hab, hba]
        · refine spec_ifLtN_false hba ?_
          refine spec_skip hc ?_
          refine ⟨by omega, fun _ _ _ => rfl, rfl, rfl, rfl, ?_⟩
          rw [h0]; simp [fval, ha, hb, hab, hba]
    · refine spec_ifLtN_false (by rw [h10]; exact hb) ?_
      refine spec_skip hc ?_
      refine ⟨by omega, fun _ _ _ => rfl, rfl, rfl, rfl, ?_⟩
      rw [h0]; simp [fval, hb]
  · refine spec_ifLtN_false (by rw [h10]; exact ha) ?_
    refine spec_skip hc ?_
    refine ⟨by omega, fun _ _ _ => rfl, rfl, rfl, rfl, ?_⟩
    rw [h0]; simp [fval, ha]

/-! ### One dart -/

/-- The state of the loop: the darts `< r20` done. -/
structure IL (hy : Hyp W n nv tb hb rb kb ub fb TL HD RV) (K : ℕ → ℕ) (U : ℕ → ℤ) (c₀ : Config)
    (c : Config) : Prop where
  wb : WordsBounded W c
  fr : Frame n fb c₀ c
  r7 : c.nreg 7 = 1
  r10 : c.nreg 10 = 3
  r20 : c.nreg 20 ≤ n
  done : ∀ d < c.nreg 20, c.rmem (fb + d) = fval (K (TL d)) (K (HD d)) (U d) (U (RV d))

theorem step_exec {P : Input} (hy : Hyp W n nv tb hb rb kb ub fb TL HD RV) {c₀ : Config}
    (h₀ : Inp n tb hb rb kb ub fb TL HD RV K U c₀) (c : Config) (hJ : IL hy K U c₀ c)
    (hlt : c.nreg 20 < c.nreg 1) :
    ∃ c' k, Exec P W step c c' k ∧ IL hy K U c₀ c' ∧
      (n - c'.nreg 20) * 25 + k + 2 ≤ (n - c.nreg 20) * 25 := by
  have hI := Inp.of_frame hy h₀ hJ.fr
  rw [hI.r1] at hlt
  have hc := hJ.wb
  generalize hi : c.nreg 20 = i at hlt
  have htl := hI.tl i hlt
  have hhd := hI.hd i hlt
  have hT := hy.TL_lt i hlt
  have hH := hy.HD_lt i hlt
  have := hy.tbW; have := hy.hbW; have := hy.kbW; have := hy.fbW; have := hy.nW
  -- the ranks
  obtain ⟨c₁, k₁, e₁, hk₁, hR₁, h24₁, h25₁, h26₁, h0₁, hm₁, hr₁, ho₁⟩ : ∃ c₁ k₁,
      Exec P W ranks c c₁ k₁ ∧ k₁ = 10 ∧
      (∀ r, r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → c₁.nreg r = c.nreg r) ∧
      c₁.nreg 24 = K (TL i) ∧ c₁.nreg 25 = K (HD i) ∧ c₁.nreg 26 = fb + i ∧ c₁.rreg 0 = 0 ∧
      c₁.nmem = c.nmem ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold ranks
    exec_block
    · rw [hI.r3, hi]; omega
    · config_simp; rw [hI.r6, hI.r3, hi, htl]; omega
    · config_simp; rw [hI.r4, hi]; omega
    · config_simp; rw [hI.r6, hI.r4, hi, hhd]; omega
    · config_simp; rw [hI.r9, hi]; omega
    refine ⟨rfl, fun r h22 h23 h24 h25 h26 => ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · config_simp; simp only [Machine.upd_apply, h22, h23, h24, h25, h26, ↓reduceIte]
    · config_simp; rw [hI.r6, hI.r3, hi, htl, hI.rk]
    · config_simp; rw [hI.r6, hI.r4, hi, hhd, hI.rk]
    · config_simp; rw [hI.r9, hi]
    · config_simp; simp
  subst hk₁
  have hw₁ := e₁.wb_right
  have hfr₁ : Frame n fb c c₁ := ⟨fun r hr => hR₁ r (by rcases hr with h | h | h | h | h | h | h <;> omega)
    (by rcases hr with h | h | h | h | h | h | h <;> omega)
    (by rcases hr with h | h | h | h | h | h | h <;> omega)
    (by rcases hr with h | h | h | h | h | h | h <;> omega)
    (by rcases hr with h | h | h | h | h | h | h <;> omega), hm₁, fun a _ => by rw [hr₁], ho₁⟩
  have hI₁ := Inp.of_frame hy hI hfr₁
  have h20₁ : c₁.nreg 20 = i := by rw [hR₁ 20 (by omega) (by omega) (by omega) (by omega) (by omega), hi]
  have h10₁ : c₁.nreg 10 = 3 := by
    rw [hR₁ 10 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hJ.r10
  obtain ⟨c₂, k₂, e₂, hk₂, hR₂, hm₂, hr₂, ho₂, h0₂⟩ := dec_exec (P := P) hy c₁ hw₁ hI₁
    (by rw [h20₁]; exact hlt) h10₁ h0₁
  rw [h24₁, h25₁, h20₁] at h0₂
  have hw₂ := e₂.wb_right
  have h26₂ : c₂.nreg 26 = fb + i := by rw [hR₂ 26 (by omega) (by omega), h26₁]
  have h20₂ : c₂.nreg 20 = i := by rw [hR₂ 20 (by omega) (by omega), h20₁]
  have h7₂ : c₂.nreg 7 = 1 := by
    rw [hR₂ 7 (by omega) (by omega), hR₁ 7 (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hJ.r7
  have h10₂ : c₂.nreg 10 = 3 := by
    rw [hR₂ 10 (by omega) (by omega), hR₁ 10 (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hJ.r10
  have hfr₂ : Frame n fb c₁ c₂ := ⟨fun r hr => hR₂ r (by rcases hr with h | h | h | h | h | h | h <;> omega)
    (by rcases hr with h | h | h | h | h | h | h <;> omega), hm₂, fun a _ => by rw [hr₂], ho₂⟩
  have e₃ := Exec.storeR (P := P) hw₂ 26 0
  have hw₃ := e₃.wb_right
  have e₄ := Exec.addN (P := P) hw₃ 20 20 7 (by config_simp; rw [h20₂, h7₂]; omega)
  have hblk : Exec P W (block [.storeR 26 0, .addN 20 20 7]) c₂ _ 2 :=
    Exec.block_cons e₃ (Exec.block_cons e₄ (Exec.block_nil e₄.wb_right))
  refine ⟨_, _, .seq e₁ (.seq e₂ hblk), ⟨e₄.wb_right, hJ.fr.trans (hfr₁.trans (hfr₂.trans
    ⟨fun r hr => ?_, rfl, fun a ha => ?_, rfl⟩)), ?_, ?_, ?_, fun d hd => ?_⟩, ?_⟩
  · have h20 : r ≠ 20 := by rcases hr with h | h | h | h | h | h | h <;> omega
    config_simp; rw [Machine.upd_other _ _ _ h20]
  · config_simp; rw [Machine.upd_other _ _ _ (by rw [h26₂]; omega)]
  · config_simp; exact h7₂
  · config_simp; exact h10₂
  · config_simp; rw [h20₂, h7₂]; omega
  · config_simp at hd
    rw [h20₂, h7₂] at hd
    config_simp
    rw [h26₂, Machine.upd_apply]
    split_ifs with h
    · have : d = i := by omega
      subst this; rw [h0₂]
    · rw [hr₂, hr₁]
      exact hJ.done d (by rw [hi]; omega)
  · config_simp; rw [h20₂, h7₂]
    have : n - i = (n - (i + 1)) + 1 := by omega
    rw [this]; omega

/-! ### The program -/

/-- **The leaf solver on the machine.** From a configuration holding the input, the program
halts within `25 n + 5` steps, keeps the input registers, the natural memory, the real memory
outside the flows and the output, and leaves `fval` of the ranks of the ends and of the
capacities at `fb + d` for every dart `d < n`. -/
theorem prog_exec {P : Input} (hy : Hyp W n nv tb hb rb kb ub fb TL HD RV) (c₀ : Config)
    (hc : WordsBounded W c₀) (h₀ : Inp n tb hb rb kb ub fb TL HD RV K U c₀) :
    ∃ c' k, Exec P W prog c₀ c' k ∧ k ≤ 25 * n + 5 ∧ Frame n fb c₀ c' ∧
      ∀ d < n, c'.rmem (fb + d) = fval (K (TL d)) (K (HD d)) (U d) (U (RV d)) := by
  have := hy.W3
  obtain ⟨c₁, k₁, e₁, hk₁, hc₁⟩ : ∃ c₁ k₁, Exec P W (block [.constN 7 1, .constN 10 3,
      .constN 20 0]) c₀ c₁ k₁ ∧ k₁ = 3 ∧
      c₁ = { c₀ with nreg := upd (upd (upd c₀.nreg 7 1) 10 3) 20 0 } := by
    exec_block
    · omega
    · omega
    · omega
    exact ⟨rfl, rfl⟩
  subst hc₁ hk₁
  have hIL : IL hy K U c₀ { c₀ with nreg := upd (upd (upd c₀.nreg 7 1) 10 3) 20 0 } := by
    refine ⟨e₁.wb_right, ⟨fun r hr => ?_, rfl, fun _ _ => rfl, rfl⟩, by config_simp,
      by config_simp, by config_simp; omega, fun d hd => by config_simp at hd; omega⟩
    have h7 : r ≠ 7 := by rcases hr with h | h | h | h | h | h | h <;> omega
    have h10 : r ≠ 10 := by rcases hr with h | h | h | h | h | h | h <;> omega
    have h20 : r ≠ 20 := by rcases hr with h | h | h | h | h | h | h <;> omega
    config_simp
    rw [Machine.upd_other _ _ _ h20, Machine.upd_other _ _ _ h10, Machine.upd_other _ _ _ h7]
  obtain ⟨c₂, k₂, e₂, hI₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 20)
    (b := 1) (body := step) (IL hy K U c₀) (fun c => (n - c.nreg 20) * 25)
    (fun c h => h.wb) (fun c hc hlt => step_exec hy h₀ c hc hlt) hIL
  have hIn₂ := Inp.of_frame hy h₀ hI₂.fr
  have h20 : c₂.nreg 20 = n := by have := hI₂.r20; rw [hIn₂.r1] at hn₂; omega
  refine ⟨c₂, _, .seq e₁ e₂, ?_, hI₂.fr, fun d hd => hI₂.done d (by rw [h20]; exact hd)⟩
  config_simp at hk₂
  simp only [Nat.sub_zero] at hk₂
  omega

/-! ### A starting configuration -/

/-- The input laid out from address `0`: tails, heads and reverses at `0`, `n`, `2n` and the ranks
at `3n` of the natural memory, the capacities at `0` and the flows at `n` of the real memory. -/
noncomputable def start (n : ℕ) (TL HD RV K : ℕ → ℕ) (U : ℕ → ℤ) : Config where
  pc := 0
  nreg := fun r => if r = 1 ∨ r = 4 ∨ r = 9 then n else if r = 5 then n + n else
    if r = 6 then n + n + n else 0
  rreg := fun _ => 0
  nmem := fun a => if a < n then TL a else if a < n + n then HD (a - n) else
    if a < n + n + n then RV (a - (n + n)) else K (a - (n + n + n))
  rmem := fun a => if a < n then (U a : ℝ) else 0
  output := []

/-- **The layout `start` meets the hypotheses of `prog_exec`**, the ranks being at most `3`. -/
theorem start_spec {n nv : ℕ} {TL HD RV K : ℕ → ℕ} (U : ℕ → ℤ) (hTL : ∀ d < n, TL d < nv)
    (hHD : ∀ d < n, HD d < nv) (hRV : ∀ d < n, RV d < n) (hK : ∀ v, K v ≤ 3) :
    Hyp (3 * n + nv + 4) n nv 0 n (n + n) (n + n + n) 0 n TL HD RV ∧
      WordsBounded (3 * n + nv + 4) (start n TL HD RV K U) ∧
      Inp n 0 n (n + n) (n + n + n) 0 n TL HD RV K U (start n TL HD RV K U) ∧
      (start n TL HD RV K U).output = [] := by
  refine ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, hTL, hHD, hRV⟩, ⟨fun r => ?_, fun a => ?_⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun d hd => ?_, fun d hd => ?_, fun d hd => ?_, fun v => ?_, fun d hd => ?_⟩, rfl⟩
  · simp only [start]; split_ifs <;> omega
  · simp only [start]; split_ifs with h1 h2 h3
    · have := hTL a h1; omega
    · have := hHD (a - n) (by omega); omega
    · have := hRV (a - (n + n)) (by omega); omega
    · have := hK (a - (n + n + n)); omega
  · simp [start, hd]
  · simp only [start]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ n + d < n by omega)),
      ite_eq_left_of_eq_true _ _ (eq_true (show n + d < n + n by omega))]
    congr 1; omega
  · simp only [start]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ n + n + d < n by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false (show ¬ n + n + d < n + n by omega)),
      ite_eq_left_of_eq_true _ _ (eq_true (show n + n + d < n + n + n by omega))]
    congr 1; omega
  · simp only [start]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ n + n + n + v < n by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false (show ¬ n + n + n + v < n + n by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false (show ¬ n + n + n + v < n + n + n by omega))]
    congr 1; omega
  · simp [start, hd]

end LeafFlow

end PlanarFlow
