module

public import PlanarSeparator.Machine.MillerLCA
public import PlanarSeparator.Machine.CycleBridge

/-!
# Miller's separator on the machine: the weights of the strict insides

Part of step 8 of the plan in `PlanarSeparator/Machine/Miller.lean`. The coded triangulation is
held as for the cycle search of Lipton and Tarjan (`PlanarSeparator/Machine/Search.lean`: the
reversals `A x` at `x`, the tree marks at `3 k + x`, the dart `pd F` of every face found by the
search of the dual tree at `8 k + F`), and above `11 k` the arrays of the Miller programs: the
vertices `V x` of the darts at `bV`, the root sums at `bS`, the weights at `bW`, and the depths
and the table of ancestors of `PlanarSeparator/Machine/MillerLCA.lean`.

For a dart `p = pd F` off the tree with triangle `x z y` (`x = V p`, `z = V (A p)`,
`y = V (φ² p)`), the weight of `bset p` is given by root sums and the three lowest common
ancestors `pl`, `q`, `r` of the corners `x z`, `x y`, `y z`
(`PlanarSeparator.Map.SpTree.sum_bset`): `bform`. The program `bpass` stores this weight
`bnum (pd F) F` at `6 k + F` for every face `F ≠ 0` (three queries `lcaq` per face;
`bpass_exec`, within `(75 L + 125) k + 3` steps). Then the pass of Lipton and Tarjan
(`PlanarSeparator.CycleSearch.pass`), run with these numbers in place of the face weights,
computes `J F = bnum (pd F) F + Σ J (children)`, which by the exact recursion of the strict
insides (`PlanarSeparator.Map.SpTree.sum_inC`) is the weight of the strict inside of `pd F`
(`inC_exec`, numeric; `inC_tree`, for a coded plane triangulation: `J F = Σ_{v ∈ inC (pd F)} w v`).

Registers: those of the search (`r0 … r14`), of `lcaq` (`r140`, `r141`, `r161`, `r253`, `r254`,
`r271`, and `r280 … r291`), `r162 = bV`, `r250 = bW`, `r252 = bS`; `bpass` writes
`r300 … r319`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### The numbers -/

/-- The weight of `bset` from the root sums `R`, the weights `w`, the apex `y` and the three
lowest common ancestors (`PlanarSeparator.Map.SpTree.sum_bset`). -/
def bform (R w : ℕ → ℕ) (y pl q r : ℕ) : ℕ :=
  if q = r then R y - R q + ((R pl - w pl) - (R q - w q))
  else if pl = r then R y - R q else R y - R r

/-- The third dart `φ² p` of the face `F` of `p`. -/
def phi2N (p F : ℕ) : ℕ := F * 3 + (p % 3 + 2) % 3

/-- The weight of `bset p` for the dart `p` of face `F`, numerically. -/
def bnum (V A R w : ℕ → ℕ) (Lc : ℕ → ℕ → ℕ) (p F : ℕ) : ℕ :=
  bform R w (V (phi2N p F)) (Lc (V p) (V (A p))) (Lc (V p) (V (phi2N p F)))
    (Lc (V (phi2N p F)) (V (A p)))

theorem phi2N_eq {p F : ℕ} (h : p / 3 = F) : phi2N p F = CycleSearch.phi3 (CycleSearch.phi3 p) := by
  unfold phi2N CycleSearch.phi3
  split_ifs <;> omega

/-! ### The programs -/

/-- **A query between registers**: `rd := lca (ra, rb)`. -/
def qcall (ra rb rd : ℕ) : Stmt :=
  .seq (block [.copyN 280 ra, .copyN 281 rb]) (.seq lcaq (.instr (.copyN rd 282)))

/-- The dart `p = pd F` of the face `F = r300` and the corners `z = r304`, `x = r305`,
`y = r308`. -/
def bcorners : List Instr :=
  [.addN 301 8 300, .loadN 302 301, .loadN 303 302, .addN 301 162 303, .loadN 304 301,
    .addN 301 162 302, .loadN 305 301, .modN 306 302 3, .addN 306 306 2, .modN 306 306 3,
    .mulN 307 300 3, .addN 307 307 306, .addN 301 162 307, .loadN 308 301]

/-- `r312 = R y`, `r313 = R q`, `r314 = R y - R q`. -/
def broot : List Instr :=
  [.addN 301 252 308, .loadN 312 301, .addN 301 252 310, .loadN 313 301, .subN 314 312 313]

/-- `r314 := R y - R r`. -/
def bZ : Stmt := block [.addN 301 252 311, .loadN 319 301, .subN 314 312 319]

/-- `r314 := R y - R q + ((R pl - w pl) - (R q - w q))`. -/
def bY : Stmt :=
  block [.addN 301 252 309, .loadN 315 301, .addN 301 250 309, .loadN 318 301, .subN 315 315 318,
    .addN 301 250 310, .loadN 318 301, .subN 316 313 318, .subN 317 315 316, .addN 314 314 317]

/-- The case analysis of `bform`. -/
def bbranch : Stmt :=
  .ifLtN 310 311 (.ifLtN 309 311 bZ (.ifLtN 311 309 bZ .skip))
    (.ifLtN 311 310 (.ifLtN 309 311 bZ (.ifLtN 311 309 bZ .skip)) bY)

/-- **One face** `r300 = F ≠ 0`: the weight of `bset (pd F)` at `6 k + F`. -/
def bsbody : Stmt :=
  .seq (block bcorners) <| .seq (qcall 305 304 309) <| .seq (qcall 305 308 310) <|
  .seq (qcall 308 304 311) <| .seq (block broot) <| .seq bbranch <|
  block [.addN 301 6 300, .storeN 301 314, .addN 300 300 1]

/-- **The weights of the sets `bset (pd F)`**, for the faces `1 ≤ F < k`. -/
def bpass : Stmt := .seq (.instr (.copyN 300 1)) (.whileLtN 300 4 bsbody)

/-! ### Queries between registers -/

section qcall

variable {W : ℕ} {P : Input} {n r₀ bD bU L : ℕ} {f dep : ℕ → ℕ}

theorem QFix.of {c c' : Config} (h : QFix n r₀ bD bU L W f dep c)
    (hr : ∀ r, r < 280 → c'.nreg r = c.nreg r)
    (hm : ∀ a, (bU ≤ a ∧ a < bU + L * n) ∨ (bD ≤ a ∧ a < bD + n) → c'.nmem a = c.nmem a) :
    QFix n r₀ bD bU L W f dep c' := by
  refine ⟨(hr _ (by omega)).trans h.r140, (hr _ (by omega)).trans h.r141,
    (hr _ (by omega)).trans h.r161, (hr _ (by omega)).trans h.r253,
    (hr _ (by omega)).trans h.r254, (hr _ (by omega)).trans h.r271, h.tree, fun j hj v hv => ?_,
    fun v hv => ?_, h.pow, h.hL, h.hU, h.hD⟩
  · have : j * n + n ≤ L * n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
    rw [hm _ (Or.inl (by omega))]; exact h.tab j hj v hv
  · rw [hm _ (Or.inr (by omega))]; exact h.mdep v hv

/-- **A query between registers.** -/
theorem qcall_exec (c : Config) (hF : QFix n r₀ bD bU L W f dep c) (hc : WordsBounded W c)
    {ra rb rd : ℕ} (hrb : rb ≠ 280) (hrd : 292 ≤ rd)
    (hu : c.nreg ra < n) (hv : c.nreg rb < n) :
    ∃ c' t, Exec P W (qcall ra rb rd) c c' t ∧ t ≤ 25 * L + 29 ∧
      IsLCA f (c.nreg ra) (c.nreg rb) (c'.nreg rd) ∧ c'.nreg rd < n ∧
      (∀ r, r < 280 ∨ 292 ≤ r → r ≠ rd → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, hw₁, g280, g281, hr₁, hm₁, ho₁, rfl⟩ : ∃ c₁ t₁,
      Exec P W (block [.copyN 280 ra, .copyN 281 rb]) c c₁ t₁ ∧ WordsBounded W c₁ ∧
      c₁.nreg 280 = c.nreg ra ∧ c₁.nreg 281 = c.nreg rb ∧
      (∀ r, r ≠ 280 → r ≠ 281 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.output = c.output ∧ t₁ = 2 := by
    exec_block
    refine ⟨‹_›, ?_, ?_, fun r a b => ?_, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals simp only [upd_apply]; split_ifs <;> first | omega | rfl
  have hF₁ : QFix n r₀ bD bU L W f dep c₁ :=
    hF.of (fun r hr => hr₁ r (by omega) (by omega)) (fun a _ => by rw [hm₁])
  obtain ⟨c₂, t₂, e₂, ht₂, hl, hl', hr₂, hm₂, ho₂⟩ := lcaq_exec (P := P) hF₁ hw₁ hu hv g280 g281
  have e₃ := Exec.copyN (P := P) e₂.wb_right rd 282
  refine ⟨_, 2 + (t₂ + 1), .seq e₁ (.seq e₂ e₃), by omega, ?_, ?_, fun r hr hne => ?_, ?_, ?_⟩
  all_goals config_simp
  · exact hl
  · exact hl'
  · rw [upd_other _ _ _ hne, hr₂ r hr]
    exact hr₁ r (by omega) (by omega)
  · rw [hm₂, hm₁]
  · rw [ho₂, ho₁]

end qcall

/-! ### One face -/

section face

variable {W : ℕ} {P : Input}

/-- **The case analysis.** -/
theorem bbranch_exec {R w : ℕ → ℕ} {bS bW y pl q rr : ℕ} (c : Config) (hc : WordsBounded W c)
    (h309 : c.nreg 309 = pl) (h310 : c.nreg 310 = q) (h311 : c.nreg 311 = rr)
    (h312 : c.nreg 312 = R y) (h313 : c.nreg 313 = R q) (h314 : c.nreg 314 = R y - R q)
    (h252 : c.nreg 252 = bS) (h250 : c.nreg 250 = bW)
    (mS : ∀ u, u = pl ∨ u = q ∨ u = rr → c.nmem (bS + u) = R u)
    (mW : ∀ u, u = pl ∨ u = q → c.nmem (bW + u) = w u)
    (hb : ∀ u, u = pl ∨ u = q ∨ u = rr → bS + u ≤ W ∧ bW + u ≤ W)
    (hv : bform R w y pl q rr ≤ W) :
    ∃ c' t, Exec P W bbranch c c' t ∧ t ≤ 14 ∧ c'.nreg 314 = bform R w y pl q rr ∧
      (∀ r, r ≠ 301 → r < 314 ∨ 320 ≤ r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.output = c.output := by
  have mSp := mS pl (Or.inl rfl)
  have mSq := mS q (Or.inr (Or.inl rfl))
  have mSr := mS rr (Or.inr (Or.inr rfl))
  have mWp := mW pl (Or.inl rfl)
  have mWq := mW q (Or.inr rfl)
  have bp := hb pl (Or.inl rfl)
  have bq := hb q (Or.inr (Or.inl rfl))
  have br := hb rr (Or.inr (Or.inr rfl))
  -- `r314 := R y - R r`
  have hZ : ∀ c₁ : Config, WordsBounded W c₁ → (∀ r, r ≠ 314 → c₁.nreg r = c.nreg r) →
      c₁.nmem = c.nmem → c₁.output = c.output →
      ∃ c' t, Exec P W bZ c₁ c' t ∧ t = 3 ∧ c'.nreg 314 = R y - R rr ∧
        (∀ r, r ≠ 301 → r < 314 ∨ 320 ≤ r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
        c'.output = c.output := by
    intro c₁ hc₁ hr₁ hm₁ ho₁
    have g252 := (hr₁ 252 (by omega)).trans h252
    have g311 := (hr₁ 311 (by omega)).trans h311
    have g312 := (hr₁ 312 (by omega)).trans h312
    have hc := hc₁
    unfold bZ
    exec_block
    · config_simp; rw [g252, g311]; omega
    refine ⟨rfl, ?_, fun r a b => ?_, hm₁, ho₁⟩
    all_goals config_simp
    · rw [g252, g311, g312, hm₁, mSr]
    · simp only [upd_apply]; split_ifs <;> first | omega | exact hr₁ r (by omega)
  have hcZ : ∀ r, r ≠ 314 → c.nreg r = c.nreg r := fun _ _ => rfl
  by_cases hqr : q = rr
  · subst hqr
    -- the center is `pl`
    refine spec_ifLtN_false (by rw [h310, h311]; omega) ?_
    refine spec_ifLtN_false (by rw [h310, h311]; omega) ?_
    unfold bY
    exec_block
    all_goals try (config_simp; simp only [h252, h250, h309, h310, h313, h314, mSp, mWp, mWq]; omega)
    · config_simp; simp only [h252, h250, h309, h310, h313, h314, mSp, mWp, mWq]
      unfold bform at hv; simp only [↓reduceIte] at hv; omega
    refine ⟨by omega, ?_, fun r a b => ?_, rfl, rfl⟩
    all_goals config_simp
    · simp only [h252, h250, h309, h310, h313, h314, mSp, mWp, mWq]
      unfold bform; simp only [↓reduceIte]
    · simp only [upd_apply]; split_ifs <;> first | omega | rfl
  · -- the center is `q` or `rr`
    have hX : ∃ c' t, Exec P W (.ifLtN 309 311 bZ (.ifLtN 311 309 bZ .skip)) c c' t ∧ t ≤ 7 ∧
        c'.nreg 314 = bform R w y pl q rr ∧
        (∀ r, r ≠ 301 → r < 314 ∨ 320 ≤ r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
        c'.output = c.output := by
      rcases Nat.lt_trichotomy pl rr with hlt | heq | hgt
      · obtain ⟨c', t, e, rfl, h1, h2, h3, h4⟩ := hZ c hc hcZ rfl rfl
        refine ⟨c', 3 + 1, .ifLtN_true (by rw [h309, h311]; exact hlt) e, by omega, ?_, h2, h3, h4⟩
        rw [h1]; unfold bform; simp only [hqr, ↓reduceIte, show pl ≠ rr by omega]
      · refine ⟨c, 0 + 2 + 2, .ifLtN_false (by rw [h309, h311]; omega)
          (.ifLtN_false (by rw [h309, h311]; omega) (.skip hc)), by omega, ?_,
          fun _ _ _ => rfl, rfl, rfl⟩
        rw [h314]; unfold bform; simp only [hqr, ↓reduceIte, heq]
      · obtain ⟨c', t, e, rfl, h1, h2, h3, h4⟩ := hZ c hc hcZ rfl rfl
        refine ⟨c', 3 + 1 + 2, .ifLtN_false (by rw [h309, h311]; omega)
          (.ifLtN_true (by rw [h309, h311]; exact hgt) e), by omega, ?_, h2, h3, h4⟩
        rw [h1]; unfold bform; simp only [hqr, ↓reduceIte, show pl ≠ rr by omega]
    obtain ⟨c', t, e, ht, h1, h2, h3, h4⟩ := hX
    rcases Nat.lt_or_gt_of_ne hqr with hlt | hgt
    · exact ⟨c', t + 1, .ifLtN_true (by rw [h310, h311]; exact hlt) e, by omega, h1, h2, h3, h4⟩
    · exact ⟨c', t + 1 + 2, .ifLtN_false (by rw [h310, h311]; omega)
        (.ifLtN_true (by rw [h310, h311]; exact hgt) e), by omega, h1, h2, h3, h4⟩

end face

/-! ### The pass over the faces -/

/-- The registers and the memory read by `bpass`, in the configuration `c` it starts from. -/
structure BSFix (k n bV bS bW W : ℕ) (A V R w pdf : ℕ → ℕ) (c : Config) : Prop where
  regs : CycleSearch.CRegs k c
  r162 : c.nreg 162 = bV
  r250 : c.nreg 250 = bW
  r252 : c.nreg 252 = bS
  mA : ∀ x < 3 * k, c.nmem x = A x
  A_lt : ∀ x < 3 * k, A x < 3 * k
  mV : ∀ x < 3 * k, c.nmem (bV + x) = V x
  V_lt : ∀ x < 3 * k, V x < n
  mP : ∀ F, 1 ≤ F → F < k → c.nmem (8 * k + F) = pdf F
  P_ok : ∀ F, 1 ≤ F → F < k → pdf F < 3 * k ∧ pdf F / 3 = F
  mS : ∀ v < n, c.nmem (bS + v) = R v
  mW : ∀ v < n, c.nmem (bW + v) = w v
  lV : 7 * k ≤ bV
  lS : 7 * k ≤ bS
  lW : 7 * k ≤ bW
  hV : bV + 3 * k ≤ W
  hS : bS + n ≤ W
  hW : bW + n ≤ W
  hk : 9 * k ≤ W

/-- The state of `bpass` before the face `F`. -/
structure BI (k W : ℕ) (Bv : ℕ → ℕ) (c₀ : Config) (F : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  r300 : c.nreg 300 = F
  pos : 1 ≤ F
  le : F ≤ k
  regs : ∀ r, r < 280 ∨ (292 ≤ r ∧ r < 300) ∨ 320 ≤ r → c.nreg r = c₀.nreg r
  mem : ∀ a, a < 6 * k ∨ 7 * k ≤ a → c.nmem a = c₀.nmem a
  out : c.output = c₀.output
  done : ∀ G, 1 ≤ G → G < F → c.nmem (6 * k + G) = Bv G

section bpass

variable {W : ℕ} {P : Input} {k n r₀ bD bU L bV bS bW : ℕ} {f dep A V R w pdf : ℕ → ℕ}
  {Lc : ℕ → ℕ → ℕ} {c₀ : Config}
  (hB : BSFix k n bV bS bW W A V R w pdf c₀) (hQ : QFix n r₀ bD bU L W f dep c₀)
  (hlU : 7 * k ≤ bU) (hlD : 7 * k ≤ bD)
  (hLc : ∀ u v, u < n → v < n → IsLCA f u v (Lc u v))
  (hRW : ∀ v < n, R v ≤ W)
  (hBW : ∀ F, 1 ≤ F → F < k → bnum V A R w Lc (pdf F) F ≤ W)
include hB hQ hlU hlD hLc hRW hBW

set_option maxHeartbeats 4000000 in
theorem bsbody_exec (F : ℕ) (c : Config) (hI : BI k W (fun G => bnum V A R w Lc (pdf G) G) c₀ F c)
    (hF : F < k) :
    ∃ c' t, Exec P W bsbody c c' t ∧ BI k W (fun G => bnum V A R w Lc (pdf G) G) c₀ (F + 1) c' ∧
      t ≤ 75 * L + 123 := by
  have hc := hI.wb
  have hT := hQ.tree
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hB.regs
  have g : ∀ r, r < 280 → c.nreg r = c₀.nreg r := fun r hr => hI.regs r (Or.inl hr)
  have g2 := (g 2 (by omega)).trans h2
  have g3 := (g 3 (by omega)).trans h3
  have g6 := (g 6 (by omega)).trans h6
  have g8 := (g 8 (by omega)).trans h8
  have g1 := (g 1 (by omega)).trans h1
  have g162 := (g 162 (by omega)).trans hB.r162
  have g250 := (g 250 (by omega)).trans hB.r250
  have g252 := (g 252 (by omega)).trans hB.r252
  have hF1 := hI.pos
  obtain ⟨hpk, hpF⟩ := hB.P_ok F hF1 hF
  generalize hp : pdf F = p at hpk hpF
  have hAp := hB.A_lt p hpk
  have h2k : phi2N p F < 3 * k := by unfold phi2N; omega
  have mP : c.nmem (8 * k + F) = p := by
    rw [hI.mem _ (Or.inr (by omega)), hB.mP F hF1 hF, hp]
  have mA : c.nmem p = A p := by rw [hI.mem _ (Or.inl (by omega))]; exact hB.mA p hpk
  have mVz : c.nmem (bV + A p) = V (A p) := by
    rw [hI.mem _ (Or.inr (by have := hB.lV; omega))]; exact hB.mV _ hAp
  have mVx : c.nmem (bV + p) = V p := by
    rw [hI.mem _ (Or.inr (by have := hB.lV; omega))]; exact hB.mV _ hpk
  have mVy : c.nmem (bV + phi2N p F) = V (phi2N p F) := by
    rw [hI.mem _ (Or.inr (by have := hB.lV; omega))]; exact hB.mV _ h2k
  have hz := hB.V_lt _ hAp
  have hx := hB.V_lt _ hpk
  have hy := hB.V_lt _ h2k
  have hbV := hB.hV
  have hk9 := hB.hk
  -- the corners
  obtain ⟨c₁, t₁, e₁, hw₁, fr₁, g304, g305, g308, hm₁, ho₁, rfl⟩ : ∃ c₁ t₁,
      Exec P W (block bcorners) c c₁ t₁ ∧ WordsBounded W c₁ ∧
      (∀ r, r < 280 ∨ (292 ≤ r ∧ r < 301) ∨ 309 ≤ r → c₁.nreg r = c.nreg r) ∧
      c₁.nreg 304 = V (A p) ∧ c₁.nreg 305 = V p ∧ c₁.nreg 308 = V (phi2N p F) ∧
      c₁.nmem = c.nmem ∧ c₁.output = c.output ∧ t₁ = 14 := by
    unfold bcorners
    exec_block
    all_goals try (config_simp; simp only [g8, hI.r300, mP, mA, g162, g3, g2]; omega)
    refine ⟨‹_›, fun r hr => ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    all_goals config_simp
    · simp only [upd_apply]; split_ifs <;> first | omega | rfl
    · simp only [g8, hI.r300, mP, mA, g162, mVz]
    · simp only [g8, hI.r300, mP, g162, mVx]
    · simp only [g8, hI.r300, mP, g162, g3, g2]
      rw [show F * 3 + (p % 3 + 2) % 3 = phi2N p F from rfl, mVy]
  -- the queries
  have hQ' : ∀ c' : Config, (∀ r, r < 280 → c'.nreg r = c.nreg r) → c'.nmem = c.nmem →
      QFix n r₀ bD bU L W f dep c' := fun c' hr hm =>
    hQ.of (fun r h => (hr r h).trans (g r h)) (fun a ha => by
      rw [hm, hI.mem a (Or.inr (by have := hQ.hD; omega))])
  obtain ⟨c₂, t₂, e₂, ht₂, hl₂, -, fr₂, hm₂, ho₂⟩ := qcall_exec (P := P) c₁
    (hQ' c₁ (fun r h => fr₁ r (Or.inl h)) hm₁) hw₁ (ra := 305) (rb := 304) (rd := 309)
    (by omega) (by omega) (by rw [g305]; exact hx) (by rw [g304]; exact hz)
  have hw₂ := e₂.wb_right
  rw [g305, g304] at hl₂
  have q₁ := IsLCA.unique hT hx hl₂ (hLc _ _ hx hz)
  obtain ⟨c₃, t₃, e₃, ht₃, hl₃, -, fr₃, hm₃, ho₃⟩ := qcall_exec (P := P) c₂
    (hQ' c₂ (fun r h => (fr₂ r (Or.inl h) (by omega)).trans (fr₁ r (Or.inl h))) (hm₂.trans hm₁))
    hw₂ (ra := 305) (rb := 308) (rd := 310) (by omega) (by omega)
    (by rw [fr₂ 305 (by omega) (by omega), g305]; exact hx)
    (by rw [fr₂ 308 (by omega) (by omega), g308]; exact hy)
  have hw₃ := e₃.wb_right
  rw [fr₂ 305 (by omega) (by omega), g305, fr₂ 308 (by omega) (by omega), g308] at hl₃
  have q₂ := IsLCA.unique hT hx hl₃ (hLc _ _ hx hy)
  obtain ⟨c₄, t₄, e₄, ht₄, hl₄, -, fr₄, hm₄, ho₄⟩ := qcall_exec (P := P) c₃
    (hQ' c₃ (fun r h => ((fr₃ r (Or.inl h) (by omega)).trans (fr₂ r (Or.inl h) (by omega))).trans
      (fr₁ r (Or.inl h))) ((hm₃.trans hm₂).trans hm₁))
    hw₃ (ra := 308) (rb := 304) (rd := 311) (by omega) (by omega)
    (by rw [fr₃ 308 (by omega) (by omega), fr₂ 308 (by omega) (by omega), g308]; exact hy)
    (by rw [fr₃ 304 (by omega) (by omega), fr₂ 304 (by omega) (by omega), g304]; exact hz)
  have hw₄ := e₄.wb_right
  rw [fr₃ 308 (by omega) (by omega), fr₂ 308 (by omega) (by omega), g308,
    fr₃ 304 (by omega) (by omega), fr₂ 304 (by omega) (by omega), g304] at hl₄
  have q₃ := IsLCA.unique hT hy hl₄ (hLc _ _ hy hz)
  -- the registers after the queries
  have lt_of : ∀ u v l, u < n → IsLCA f u v l → l < n := fun u v l hu h => by
    obtain ⟨m, rfl⟩ := h.1; exact hT.iter_lt m hu
  have hpl := lt_of _ _ _ hx (hLc _ _ hx hz)
  have hq := lt_of _ _ _ hx (hLc _ _ hx hy)
  have hrr := lt_of _ _ _ hy (hLc _ _ hy hz)
  set pl := Lc (V p) (V (A p))
  set q := Lc (V p) (V (phi2N p F))
  set rr := Lc (V (phi2N p F)) (V (A p))
  set y := V (phi2N p F)
  have fr : ∀ r, r < 280 ∨ (292 ≤ r ∧ r < 301) ∨ 312 ≤ r → c₄.nreg r = c.nreg r := fun r hr => by
    rw [fr₄ r (by omega) (by omega), fr₃ r (by omega) (by omega), fr₂ r (by omega) (by omega),
      fr₁ r (by omega)]
  have k309 : c₄.nreg 309 = pl := by
    rw [fr₄ 309 (by omega) (by omega), fr₃ 309 (by omega) (by omega)]; exact q₁
  have k310 : c₄.nreg 310 = q := by rw [fr₄ 310 (by omega) (by omega)]; exact q₂
  have k311 : c₄.nreg 311 = rr := q₃
  have k308 : c₄.nreg 308 = y := by
    rw [fr₄ 308 (by omega) (by omega), fr₃ 308 (by omega) (by omega),
      fr₂ 308 (by omega) (by omega), g308]
  have hm4 : c₄.nmem = c.nmem := ((hm₄.trans hm₃).trans hm₂).trans hm₁
  have mS : ∀ u < n, c₄.nmem (bS + u) = R u := fun u hu => by
    rw [hm4, hI.mem _ (Or.inr (by have := hB.lS; omega))]; exact hB.mS u hu
  have mW : ∀ u < n, c₄.nmem (bW + u) = w u := fun u hu => by
    rw [hm4, hI.mem _ (Or.inr (by have := hB.lW; omega))]; exact hB.mW u hu
  have k252 : c₄.nreg 252 = bS := (fr 252 (by omega)).trans g252
  have k250 : c₄.nreg 250 = bW := (fr 250 (by omega)).trans g250
  have hbS := hB.hS
  have hbW := hB.hW
  have mSy := mS y hy
  have mSq := mS q hq
  -- the root sums
  obtain ⟨c₅, t₅, e₅, hw₅, fr₅, k312, k313, k314, hm₅, ho₅, rfl⟩ : ∃ c₅ t₅,
      Exec P W (block broot) c₄ c₅ t₅ ∧ WordsBounded W c₅ ∧
      (∀ r, r ≠ 301 → r < 312 ∨ 315 ≤ r → c₅.nreg r = c₄.nreg r) ∧
      c₅.nreg 312 = R y ∧ c₅.nreg 313 = R q ∧ c₅.nreg 314 = R y - R q ∧
      c₅.nmem = c₄.nmem ∧ c₅.output = c₄.output ∧ t₅ = 5 := by
    have hc := hw₄
    unfold broot
    exec_block
    all_goals try (config_simp; simp only [k252, k308, k310, mSy]; omega)
    refine ⟨‹_›, fun r a b => ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    all_goals config_simp
    · simp only [upd_apply]; split_ifs <;> first | omega | rfl
    · simp only [k252, k308, mSy]
    · simp only [k252, k310, mSq]
    · simp only [k252, k308, k310, mSy, mSq]
  -- the case analysis
  have hval : bform R w y pl q rr = bnum V A R w Lc p F := rfl
  obtain ⟨c₆, t₆, e₆, ht₆, k314', fr₆, hm₆, ho₆⟩ := bbranch_exec (P := P) (R := R) (w := w)
    (bS := bS) (bW := bW) (y := y) (pl := pl) (q := q) (rr := rr) c₅ hw₅
    (by rw [fr₅ 309 (by omega) (by omega)]; exact k309)
    (by rw [fr₅ 310 (by omega) (by omega)]; exact k310)
    (by rw [fr₅ 311 (by omega) (by omega)]; exact k311) k312 k313 k314
    (by rw [fr₅ 252 (by omega) (by omega)]; exact k252)
    (by rw [fr₅ 250 (by omega) (by omega)]; exact k250)
    (fun u hu => by rw [hm₅]; rcases hu with rfl | rfl | rfl <;> exact mS _ ‹_›)
    (fun u hu => by rw [hm₅]; rcases hu with rfl | rfl <;> exact mW _ ‹_›)
    (fun u hu => by rcases hu with rfl | rfl | rfl <;> omega)
    (by rw [hval, ← hp]; exact hBW F hF1 hF)
  have hw₆ := e₆.wb_right
  -- the store
  have k300 : c₆.nreg 300 = F := by
    rw [fr₆ 300 (by omega) (by omega), fr₅ 300 (by omega) (by omega), fr 300 (by omega)]
    exact hI.r300
  have k6 : c₆.nreg 6 = 6 * k := by
    rw [fr₆ 6 (by omega) (by omega), fr₅ 6 (by omega) (by omega), fr 6 (by omega)]; exact g6
  have k1 : c₆.nreg 1 = 1 := by
    rw [fr₆ 1 (by omega) (by omega), fr₅ 1 (by omega) (by omega), fr 1 (by omega)]; exact g1
  have frall : ∀ r, r < 280 ∨ (292 ≤ r ∧ r < 300) ∨ 320 ≤ r → c₆.nreg r = c₀.nreg r :=
    fun r hr => by
      rw [fr₆ r (by omega) (by omega), fr₅ r (by omega) (by omega), fr r (by omega)]
      exact hI.regs r hr
  have hm6 : c₆.nmem = c.nmem := (hm₆.trans hm₅).trans hm4
  have ho6 : c₆.output = c.output := ((((ho₆.trans ho₅).trans ho₄).trans ho₃).trans ho₂).trans ho₁
  obtain ⟨c₇, t₇, e₇, hI₇, rfl⟩ : ∃ c₇ t₇,
      Exec P W (block [.addN 301 6 300, .storeN 301 314, .addN 300 300 1]) c₆ c₇ t₇ ∧
      BI k W (fun G => bnum V A R w Lc (pdf G) G) c₀ (F + 1) c₇ ∧ t₇ = 3 := by
    have hc := hw₆
    exec_block
    · config_simp; rw [k6, k300]; omega
    · config_simp; rw [k300, k1]; omega
    refine ⟨⟨‹_›, ?_, by omega, by omega, fun r hr => ?_, fun a ha => ?_, ho6.trans hI.out,
      fun G hG1 hG => ?_⟩, rfl⟩
    all_goals config_simp
    · rw [k300, k1]
    · simp only [upd_apply]; split_ifs <;> first | omega | exact frall r hr
    · rw [k6, k300, upd_other _ _ _ (by omega), hm6]; exact hI.mem a ha
    · rw [k6, k300]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hG with hG | rfl
      · rw [upd_other _ _ _ (by omega), hm6]; exact hI.done G hG1 hG
      · rw [upd_same, k314', hval, hp]
  refine ⟨c₇, 14 + (t₂ + (t₃ + (t₄ + (5 + (t₆ + 3))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))))), hI₇, by omega⟩

/-- **The weights of the sets `bset`.** For `1 ≤ k`, `bpass` stores `bnum (pd F) F` at
`6 k + F` for every face `1 ≤ F < k`, within `(75 L + 125) k + 3` steps, writing to memory only
in `[6 k, 7 k)`. -/
theorem bpass_exec (hk : 1 ≤ k) (hc₀ : WordsBounded W c₀) :
    ∃ c' t, Exec P W bpass c₀ c' t ∧ t ≤ (75 * L + 125) * k + 3 ∧
      (∀ F, 1 ≤ F → F < k → c'.nmem (6 * k + F) = bnum V A R w Lc (pdf F) F) ∧
      (∀ r, r < 280 ∨ (292 ≤ r ∧ r < 300) ∨ 320 ≤ r → c'.nreg r = c₀.nreg r) ∧
      (∀ a, a < 6 * k ∨ 7 * k ≤ a → c'.nmem a = c₀.nmem a) ∧ c'.output = c₀.output := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hB.regs
  have e₁ := Exec.copyN (P := P) hc₀ 300 1
  have hI₁ : BI k W (fun G => bnum V A R w Lc (pdf G) G) c₀ 1
      { c₀ with nreg := upd c₀.nreg 300 (c₀.nreg 1) } := by
    refine ⟨e₁.wb_right, by config_simp; exact h1, le_rfl, hk, fun r hr => ?_, fun a _ => rfl,
      rfl, fun G h1 h2 => absurd h2 (by omega)⟩
    config_simp; rw [upd_other _ _ _ (by omega)]
  obtain ⟨c', t, e, hI', ht⟩ := Exec.forN (P := P) (W := W) (ri := 300) (rN := 4) (N := k)
    (lo := 1) (B := 75 * L + 123) (body := bsbody)
    (BI k W (fun G => bnum V A R w Lc (pdf G) G) c₀)
    (fun F c' h => ⟨h.wb, h.r300, (h.regs 4 (by omega)).trans h4⟩)
    (fun F c' h hF => bsbody_exec hB hQ hlU hlD hLc hRW hBW F c' h hF) hk hI₁
  refine ⟨c', 1 + t, .seq e₁ e, ?_, hI'.done, hI'.regs, hI'.mem, hI'.out⟩
  have : (75 * L + 123 + 2) * (k - 1) ≤ (75 * L + 125) * k := Nat.mul_le_mul_left _ (by omega)
  omega

end bpass

/-! ### With the pass of Lipton and Tarjan -/

/-- **The weights of the strict insides**: the weights of the sets `bset` in place of the face
weights, then the pass over the dual tree. -/
def inCprog : Stmt := .seq bpass CycleSearch.pass

section inC

open CycleSearch

variable {W : ℕ} {P : Input} {k : ℕ} {A Tm Fw : ℕ → ℕ} {o : List ℕ}

/-- The search: the dart `pd` of every face other than the first lies on it, off the tree. -/
theorem SB.pd_face {c : Config} (hS : SB k A Tm Fw W o c) (hall : c.nreg 11 = k) {F : ℕ}
    (h1 : 1 ≤ F) (hF : F < k) : pd k c.nmem F < 3 * k ∧ pd k c.nmem F / 3 = F ∧
      Tm (pd k c.nmem F) = 0 := by
  obtain ⟨i, hi, hq⟩ := hS.exists_pos hall hF
  have hi1 : 1 ≤ i := by
    by_contra h; obtain rfl : i = 0 := by omega
    rw [hS.q0.2] at hq; omega
  have := hS.pd_ok i hi1 (by omega)
  rw [hq] at this
  exact ⟨this.2.1, this.1, this.2.2.1⟩

/-- The state of the search survives a change of the face weights. -/
theorem SB.of_fw {c c' : Config} (h : SB k A Tm Fw W o c) (hw : WordsBounded W c')
    (hr : ∀ r < 280, c'.nreg r = c.nreg r) (hm : ∀ a, a < 6 * k ∨ 7 * k ≤ a → c'.nmem a = c.nmem a)
    (ho : c'.output = c.output) : SB k A Tm (fun f => c'.nmem (6 * k + f)) W o c' := by
  have eq : mark k c'.nmem = mark k c.nmem ∧ pd k c'.nmem = pd k c.nmem ∧
      qu k c'.nmem = qu k c.nmem := ⟨funext fun f => hm _ (Or.inr (by omega)),
    funext fun f => hm _ (Or.inr (by omega)), funext fun f => hm _ (Or.inr (by omega))⟩
  have r11 := hr 11 (by omega)
  have r12 := hr 12 (by omega)
  refine ⟨hw, cregs_of h.regs fun r hr' => hr r (by omega), ⟨fun x hx => ?_, fun x hx => ?_,
    fun f _ => rfl⟩, ho.trans h.out, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm _ (Or.inl (by omega))]; exact h.hold.1 x hx
  · rw [hm _ (Or.inl (by omega))]; exact h.hold.2.1 x hx
  all_goals simp only [eq.1, eq.2.1, eq.2.2, r11, r12]
  · exact h.head_le
  · exact h.q_lt
  · exact h.q_inj
  · exact h.q0
  · exact h.mk01
  · exact h.mk_iff
  · exact h.pd_ok

variable {n r₀ bD bU L bV bS bW : ℕ} {f dep V R w : ℕ → ℕ} {Lc : ℕ → ℕ → ℕ} {c₀ : Config}

/-- **The weights of the strict insides, numerically.** After the search of the dual tree (with
every face found), `inCprog` stores at `10 k + F`, for every face `F ≠ 0`, the value `Ival F` of
any function satisfying the recurrence of the pass with the weights `bnum (pd F) F` of the sets
`bset` in place of the face weights, within `(75 L + 187) k + 6` steps. -/
theorem inC_exec (ht : Tri k A Tm) (hS : SB k A Tm Fw W o c₀) (hall : c₀.nreg 11 = k)
    (hk : 1 ≤ k) (hB : BSFix k n bV bS bW W A V R w (pd k c₀.nmem) c₀)
    (hQ : QFix n r₀ bD bU L W f dep c₀) (hlU : 7 * k ≤ bU) (hlD : 7 * k ≤ bD)
    (hLc : ∀ u v, u < n → v < n → IsLCA f u v (Lc u v)) (hRW : ∀ v < n, R v ≤ W)
    (hBW : ∀ F, 1 ≤ F → F < k → bnum V A R w Lc (pd k c₀.nmem F) F ≤ W)
    (hco : ChildOk k A Tm (pd k c₀.nmem)) {Ival : ℕ → ℕ} {tot : ℕ}
    (hle : ∀ F < k, Ival F ≤ tot)
    (hrec : RecHolds k A Tm (fun F => bnum V A R w Lc (pd k c₀.nmem F) F) (pd k c₀.nmem) Ival)
    (hW : 11 * k + 3 * tot + 4 ≤ W) :
    ∃ c' t, Exec P W inCprog c₀ c' t ∧ t ≤ (75 * L + 187) * k + 6 ∧
      (∀ F < k, F ≠ 0 → jv k c'.nmem F = Ival F) ∧
      (∀ a, a < 6 * k ∨ 11 * k ≤ a → c'.nmem a = c₀.nmem a) ∧ c'.output = o := by
  obtain ⟨c₁, t₁, e₁, ht₁, hd₁, hr₁, hm₁, ho₁⟩ := bpass_exec (P := P) hB hQ hlU hlD hLc hRW hBW hk
    hS.wb
  have hS₁ := SB.of_fw hS e₁.wb_right (fun r hr => hr₁ r (Or.inl hr)) hm₁ ho₁
  have hpd : pd k c₁.nmem = pd k c₀.nmem := funext fun F => hm₁ _ (Or.inr (by omega))
  have hall₁ : c₁.nreg 11 = k := (hr₁ 11 (Or.inl (by omega))).trans hall
  have hrec₁ : RecHolds k A Tm (fun f => c₁.nmem (6 * k + f)) (pd k c₁.nmem) Ival := by
    intro F hF hF0
    rw [hpd]
    simp only
    rw [hd₁ F (by omega) hF]
    exact hrec F hF hF0
  obtain ⟨c', t, e, -, -, -, hm', ho', hj', ht'⟩ := pass_exec (P := P) ht hS₁ hall₁
    (by rw [hpd]; exact hco) hle hrec₁ hW (by omega)
  refine ⟨c', t₁ + t, .seq e₁ e, ?_, hj', fun a ha => ?_, ho'⟩
  · have : (75 * L + 125) * k + 62 * k ≤ (75 * L + 187) * k := by nlinarith
    omega
  · rw [hm' a (by omega), hm₁ a (by omega)]

end inC

/-! ### Existence of lowest common ancestors -/

/-- **Two vertices of a numeric tree have a lowest common ancestor.** -/
theorem PTree.exists_isLCA {n r₀ : ℕ} {f dep : ℕ → ℕ} (hT : PTree n r₀ f dep) {u v : ℕ}
    (hu : u < n) (hv : v < n) : ∃ l, IsLCA f u v l := by
  classical
  -- the deeper vertex first
  suffices key : ∀ u v, u < n → v < n → dep v ≤ dep u → ∃ l, IsLCA f u v l by
    rcases le_total (dep v) (dep u) with h | h
    · exact key u v hu hv h
    · obtain ⟨l, hl⟩ := key v u hv hu h; exact ⟨l, hl.symm⟩
  intro u v hu hv hle
  have hd : dep (f^[dep u - dep v] u) = dep v := by rw [hT.dep_iter _ hu]; omega
  have hu₁ : f^[dep u - dep v] u < n := hT.iter_lt _ hu
  by_cases he : f^[dep u - dep v] u = v
  · exact ⟨v, hT.isLCA_of_eq he⟩
  · have hex : ∃ m, f^[m] (f^[dep u - dep v] u) = f^[m] v :=
      ⟨dep v, by rw [hT.iter_of_le hu₁ (by omega), hT.iter_of_le hv le_rfl]⟩
    have h0 : Nat.find hex ≠ 0 := fun h0 => he (by have := Nat.find_spec hex; rwa [h0] at this)
    have hne : f^[Nat.find hex - 1] (f^[dep u - dep v] u) ≠ f^[Nat.find hex - 1] v :=
      Nat.find_min hex (by omega)
    have heq : f^[Nat.find hex - 1 + 1] (f^[dep u - dep v] u) = f^[Nat.find hex - 1 + 1] v := by
      rw [Nat.sub_add_cancel (by omega)]; exact Nat.find_spec hex
    exact ⟨_, hT.isLCA_of_lift hu hv hd hne heq⟩

/-! ### The bridge to plane triangulations -/

section Bridge

open Map CycleSearch

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}
  {T : M.SpTree} {k n : ℕ} {cd : D ≃ Fin (3 * k)} {vi : Q ≃ Fin n} {A Tm : ℕ → ℕ}
  {V f R w : ℕ → ℕ} {Lc : ℕ → ℕ → ℕ} (wv : Q → ℕ)

/-- The root sum, in natural numbers. -/
noncomputable def rsT (T : M.SpTree) (wv : Q → ℕ) (v : Q) : ℕ := ∑ u ∈ T.anc v, wv u

theorem rsT_mono {a b : Q} (h : a ∈ T.anc b) : rsT T wv a ≤ rsT T wv b :=
  sum_le_sum_of_subset (T.anc_subset_anc h)

theorem w_le_rsT (a : Q) : wv a ≤ rsT T wv a :=
  single_le_sum (fun _ _ => Nat.zero_le _) (T.mem_anc_self a)

theorem rsT_sub_mono {a b : Q} (h : a ∈ T.anc b) :
    rsT T wv a - wv a ≤ rsT T wv b - wv b := by
  have ea := sum_erase_add _ wv (T.mem_anc_self a)
  have eb := sum_erase_add _ wv (T.mem_anc_self b)
  have hsub : (T.anc a).erase a ⊆ (T.anc b).erase b := by
    intro u hu
    rw [mem_erase] at hu ⊢
    refine ⟨fun e => hu.1 ?_, T.anc_subset_anc h hu.2⟩
    subst e; exact T.eq_of_mem_anc_of_mem_anc hu.2 h
  have := sum_le_sum_of_subset (f := wv) hsub
  unfold rsT
  omega

variable (hf : ∀ x, f (vi x) = vi (T.parent x)) (hR : ∀ x, R (vi x) = rsT T wv x)
  (hw : ∀ x, w (vi x) = wv x)
  (hLc : ∀ u v, u < n → v < n → IsLCA f u v (Lc u v))

include hf hLc in
theorem Lc_dart (δ : D) : Lc (vi (M.vert δ)) (vi (M.vert (M.α δ))) = vi (SpTree.lca T δ) :=
  isLCA_lca vi T hf δ (hLc _ _ (vi _).2 (vi _).2)

include hR hw in
/-- **`bform` is the weight of `bset`.** -/
theorem bform_eq (hM : M.IsPlane) {δ : D} (hδ : M.IsTriangle δ) (hnt : ¬ T.IsTree δ) :
    bform R w (vi (M.vert (M.φ (M.φ δ)))) (vi (SpTree.lca T δ))
      (vi (SpTree.lca T (M.α (M.φ (M.φ δ))))) (vi (SpTree.lca T (M.α (M.φ δ)))) =
      ∑ v ∈ SpTree.bset (T := T) δ, wv v := by
  have hs := SpTree.sum_bset (T := T) hM hδ hnt (fun v => (wv v : ℤ))
  simp only at hs
  set y := M.vert (M.φ (M.φ δ))
  set p := SpTree.lca T δ
  set q := SpTree.lca T (M.α (M.φ (M.φ δ)))
  set r := SpTree.lca T (M.α (M.φ δ))
  have cast : ∀ v, (∑ u ∈ T.anc v, (wv u : ℤ)) = (rsT T wv v : ℤ) := fun v => by
    unfold rsT; push_cast; rfl
  simp only [cast] at hs
  have hS : (∑ v ∈ SpTree.bset (T := T) δ, (wv v : ℤ)) =
      ((∑ v ∈ SpTree.bset (T := T) δ, wv v : ℕ) : ℤ) := by push_cast; rfl
  rw [hS] at hs
  have hqy : q ∈ T.anc y := by
    have := SpTree.lca_mem_anc' (T := T) (M.α (M.φ (M.φ δ))); rwa [M.α_α] at this
  have hry : r ∈ T.anc y := by
    have := SpTree.lca_mem_anc (T := T) (M.α (M.φ δ)); rwa [← M.vert_φ] at this
  have e1 := rsT_mono wv hqy
  have e2 := rsT_mono wv hry
  have w1 := w_le_rsT (T := T) wv p
  have w2 := w_le_rsT (T := T) wv q
  have w3 := w_le_rsT (T := T) wv r
  unfold bform
  simp only [hR, hw, Fin.val_inj, EmbeddingLike.apply_eq_iff_eq]
  apply Nat.cast_injective (R := ℤ)
  rcases hs with ⟨hqr, hqp, hsum⟩ | ⟨hpr, hpq, hsum⟩ | ⟨hpq, hpr, hsum⟩
  · have s1 := rsT_sub_mono wv hqp
    rw [ite_eq_left_of_eq_true _ _ (eq_true hqr), hsum]
    push_cast [Nat.cast_sub e1, Nat.cast_sub s1, Nat.cast_sub w1, Nat.cast_sub w2]
    ring
  · by_cases hqr : q = r
    · have hpq' : p = q := hpr.trans hqr.symm
      rw [ite_eq_left_of_eq_true _ _ (eq_true hqr), hsum, ← hpq']
      have : rsT T wv p ≤ rsT T wv y := by rw [hpq']; exact e1
      simp [Nat.cast_sub this]
    · simp only [hqr, ↓reduceIte]
      rw [ite_eq_left_of_eq_true _ _ (eq_true hpr), hsum]
      push_cast [Nat.cast_sub e1]; ring
  · by_cases hqr : q = r
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hqr), hsum, ← hpq, ← hqr, ← hpq]
      have : rsT T wv p ≤ rsT T wv y := by rw [hpq]; exact e1
      simp [Nat.cast_sub this]
    · have hpr' : p ≠ r := fun h => hqr (hpq.symm.trans h)
      simp only [hqr, hpr', ↓reduceIte]
      rw [hsum]
      push_cast [Nat.cast_sub e2]; ring

variable (hV : ∀ x, V (cd x) = vi (M.vert x))

include hf hR hw hLc hV in
/-- **`bnum` is the weight of `bset`** for a dart of a coded triangulation. -/
theorem bnum_dart (hC : Coded M T k cd A Tm) (hM : M.IsPlane) {δ : D} (hδ : M.IsTriangle δ)
    (hnt : ¬ T.IsTree δ) :
    bnum V A R w Lc (cd δ) ((cd δ : ℕ) / 3) = ∑ v ∈ SpTree.bset (T := T) δ, wv v := by
  have ey : phi2N (cd δ) ((cd δ : ℕ) / 3) = cd (M.φ (M.φ δ)) := by
    rw [phi2N_eq rfl, hC.φ_cd, hC.φ_cd]
  have hx2 : M.vert (M.α (M.φ (M.φ δ))) = M.vert δ := SpTree.vert_a₂ hδ
  have hy1 : M.vert (M.α (M.φ δ)) = M.vert (M.φ (M.φ δ)) := (M.vert_φ _).symm
  have hz1 : M.vert (M.α (M.α (M.φ δ))) = M.vert (M.α δ) := by rw [M.α_α, M.vert_φ]
  have hq := Lc_dart (hf := hf) (hLc := hLc) (M.α (M.φ (M.φ δ)))
  have hr := Lc_dart (hf := hf) (hLc := hLc) (M.α (M.φ δ))
  rw [hx2, M.α_α] at hq
  rw [hy1, hz1] at hr
  unfold bnum
  rw [ey, hC.A_cd, hV, hV, hV, Lc_dart (hf := hf) (hLc := hLc) δ, hq, hr]
  exact bform_eq wv hR hw hM hδ hnt

/-- The weight of the strict inside of the dart `pd f` of face `f`. -/
noncomputable def IvalC {c₀ : Config} (hk : 0 < k) (f : ℕ) : ℕ :=
  ∑ v ∈ T.inC (Coded.dartN (cd := cd) hk (pd k c₀.nmem f)), wv v

variable {Fw : ℕ → ℕ} {W : ℕ} {o : List ℕ} {c₀ : Config} (hC : Coded M T k cd A Tm) (hk : 0 < k)
  (hS : SB k A Tm Fw W o c₀) (hall : c₀.nreg 11 = k)

include hC hS hall in
/-- A dart other than `pd F` of a face `F ≠ 0` contributes the weight of the strict inside of its
reverse. -/
theorem childValC (hM : M.IsPlane) {F x : ℕ} (hx : x < 3 * k) (hxF : x / 3 = F)
    (hne : x ≠ pd k c₀.nmem F) :
    childVal A Tm (IvalC (T := T) (cd := cd) (c₀ := c₀) wv hk) (pd k c₀.nmem F) x =
      ∑ v ∈ T.inC (M.α (Coded.dartN (cd := cd) hk x)), wv v := by
  unfold childVal
  by_cases hT : Tm x = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hne, hT⟩)]
    rcases hC.pdor hk hS hall hM x hx hT with ⟨-, h⟩ | ⟨-, h⟩
    · exact absurd (by rw [hxF] at h; exact h.symm) hne
    · unfold IvalC; rw [h, hC.dartN_A hk hx]
  · rw [ite_eq_right_iff.2 (fun h => absurd h.2 hT)]
    have ht : T.IsTree (Coded.dartN (cd := cd) hk x) := by
      by_contra h; exact hT (by rw [← Coded.cd_dartN (cd := cd) hk hx]; exact (hC.T_cd _).2 h)
    rw [SpTree.inC_eq_empty hM ((T.isTree_α).2 ht), sum_empty]

include hf hR hw hLc hV hC hS hall in
/-- **The recurrence of the strict insides on the machine**: `J F = bnum (pd F) F + Σ children`
for the weights `J F` of the strict insides of the darts `pd F`. -/
theorem recHoldsC (hM : M.IsPlane) (hT3 : ∀ δ, M.IsTriangle δ) :
    RecHolds k A Tm (fun F => bnum V A R w Lc (pd k c₀.nmem F) F) (pd k c₀.nmem)
      (IvalC (T := T) (cd := cd) (c₀ := c₀) wv hk) := by
  intro F hF hF0
  obtain ⟨hpF, hlt, hT0⟩ := hC.pd_spec hk hS hall hF hF0
  set pD := Coded.dartN (cd := cd) hk (pd k c₀.nmem F)
  have e0 : (cd pD : ℕ) = pd k c₀.nmem F := Coded.cd_dartN hk hlt
  have hnt : ¬ T.IsTree pD := (hC.T_cd pD).1 (by rw [e0]; exact hT0)
  have hrec := SpTree.sum_inC (T := T) hM (hT3 pD) hnt wv
  rw [← hC.dartN_phi3 hk hlt, ← hC.dartN_phi3 hk (phi3_lt hlt)] at hrec
  have hφ1 : phi3 (pd k c₀.nmem F) ≠ pd k c₀.nmem F := by unfold phi3; split_ifs <;> omega
  have hφ2 : phi3 (phi3 (pd k c₀.nmem F)) ≠ pd k c₀.nmem F := by unfold phi3; split_ifs <;> omega
  have c1 := childValC wv hC hk hS hall hM (F := F) (phi3_lt hlt) (by rw [phi3_div, hpF]) hφ1
  have c2 := childValC wv hC hk hS hall hM (F := F) (phi3_lt (phi3_lt hlt))
    (by rw [phi3_div, phi3_div, hpF]) hφ2
  have c0 : childVal A Tm (IvalC (T := T) (cd := cd) (c₀ := c₀) wv hk) (pd k c₀.nmem F)
      (pd k c₀.nmem F) = 0 := by simp [childVal]
  have hb : bnum V A R w Lc (pd k c₀.nmem F) F = ∑ v ∈ SpTree.bset (T := T) pD, wv v := by
    have := bnum_dart wv hf hR hw hLc hV hC hM (hT3 pD) hnt
    rwa [e0, hpF] at this
  have hI : IvalC (T := T) (cd := cd) (c₀ := c₀) wv hk F = ∑ v ∈ T.inC pD, wv v := rfl
  simp only
  rw [hI, hrec, hb, ← c1, ← c2]
  have h3 := three_sum (childVal A Tm (IvalC (T := T) (cd := cd) (c₀ := c₀) wv hk)
    (pd k c₀.nmem F)) hpF c0
  omega

end Bridge

/-- **The weights of the strict insides of a coded plane triangulation on the machine.** After
the search of the dual tree has found every face (`SB`, `r11 = k`), with the vertices of the
darts, the root sums and the weights of a spanning tree `T` in memory (`BSFix`), and its table of
ancestors and depths (`QFix`), `inCprog` stores at `10 k + F`, for every face `F ≠ 0`, the
weight of the strict inside of the fundamental cycle of the dart `pd F`, within
`(75 L + 187) k + 6` steps. -/
theorem inC_tree {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]
    {M : Map D Q} {T : M.SpTree} {k n : ℕ} {cd : D ≃ Fin (3 * k)} {vi : Q ≃ Fin n}
    {A Tm V f dep R w Fw : ℕ → ℕ} (wv : Q → ℕ) {W : ℕ} {P : Input} {o : List ℕ} {c₀ : Config}
    {bD bU L bV bS bW : ℕ}
    (hM : M.IsPlane) (hT3 : ∀ δ, M.IsTriangle δ) (hC : CycleSearch.Coded M T k cd A Tm)
    (hk : 0 < k) (hS : CycleSearch.SB k A Tm Fw W o c₀) (hall : c₀.nreg 11 = k)
    (hB : BSFix k n bV bS bW W A V R w (CycleSearch.pd k c₀.nmem) c₀)
    (hQ : QFix n (vi T.root) bD bU L W f dep c₀) (hlU : 7 * k ≤ bU) (hlD : 7 * k ≤ bD)
    (hV : ∀ x, V (cd x) = vi (M.vert x)) (hf : ∀ x, f (vi x) = vi (T.parent x))
    (hR : ∀ x, R (vi x) = ∑ u ∈ T.anc x, wv u) (hw : ∀ x, w (vi x) = wv x)
    (hWt : 11 * k + 3 * ∑ v, wv v + 4 ≤ W) :
    ∃ c' t, Exec P W inCprog c₀ c' t ∧ t ≤ (75 * L + 187) * k + 6 ∧
      (∀ F < k, F ≠ 0 → CycleSearch.jv k c'.nmem F =
        ∑ v ∈ T.inC (CycleSearch.Coded.dartN (cd := cd) hk (CycleSearch.pd k c₀.nmem F)), wv v) ∧
      (∀ a, a < 6 * k ∨ 11 * k ≤ a → c'.nmem a = c₀.nmem a) ∧ c'.output = o := by
  classical
  let Lc : ℕ → ℕ → ℕ := fun u v => Classical.epsilon (IsLCA f u v)
  have hLc : ∀ u v, u < n → v < n → IsLCA f u v (Lc u v) := fun u v hu hv =>
    Classical.epsilon_spec (hQ.tree.exists_isLCA hu hv)
  have hR' : ∀ x, R (vi x) = rsT T wv x := hR
  have htot : ∀ X : Finset Q, ∑ v ∈ X, wv v ≤ W := fun X =>
    (sum_le_sum_of_subset (subset_univ X)).trans (by omega)
  have hRW : ∀ u < n, R u ≤ W := fun u hu => by
    obtain ⟨x, rfl⟩ := exists_vi vi hu
    rw [hR]; exact htot _
  have hBW : ∀ F, 1 ≤ F → F < k → bnum V A R w Lc (CycleSearch.pd k c₀.nmem F) F ≤ W := by
    intro F h1 hF
    obtain ⟨hpF, hlt, hT0⟩ := hC.pd_spec hk hS hall hF (by omega)
    set pD := CycleSearch.Coded.dartN (cd := cd) hk (CycleSearch.pd k c₀.nmem F)
    have e0 : (cd pD : ℕ) = CycleSearch.pd k c₀.nmem F := CycleSearch.Coded.cd_dartN hk hlt
    have hnt : ¬ T.IsTree pD := (hC.T_cd pD).1 (by rw [e0]; exact hT0)
    have := bnum_dart wv hf hR' hw hLc hV hC hM (hT3 pD) hnt
    rw [e0, hpF] at this
    rw [this]; exact htot _
  obtain ⟨c', t, e, ht, hj, hm, ho⟩ := inC_exec (P := P) hC.tri hS hall hk hB hQ hlU hlD hLc
    hRW hBW (hC.childOk hk hS hall hM) (Ival := IvalC (T := T) (cd := cd) (c₀ := c₀) wv hk)
    (tot := ∑ v, wv v) (fun F _ => sum_le_sum_of_subset (subset_univ _))
    (recHoldsC wv hf hR' hw hLc hV hC hk hS hall hM hT3) (by omega)
  exact ⟨c', t, e, ht, hj, hm, ho⟩

end MillerProg

end PlanarSeparator
