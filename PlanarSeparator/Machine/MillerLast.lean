module

public import PlanarSeparator.Machine.MillerTest

/-!
# Miller's separator on the machine: the last heavy level

The heavy levels of a breadth-first tree form an initial segment
(`PlanarSeparator.Map.heavy_mono`) of the levels below `n` (`PlanarSeparator.Map.heavy_lt`).
The program `bsearch` finds the last one by bisection: it keeps `lo < hi` with `lo` heavy (or
`lo = 0`) and `hi` not heavy, starting from `lo = 0`, `hi = n`, and tests the middle level with
the heavy test `hvy` (`PlanarSeparator/Machine/MillerTest.lean`), after clearing the sums of the
labels (`zpass`). It ends with `ls = lo` in `r180` such that `ls = 0` or `ls` is heavy, and no
level above `ls` is heavy (`bsearch_exec`), within
`(106 k + 21 n + 30) ⌈log₂ n⌉ + 5` steps: this is the step of Miller's algorithm that costs
`O(n log n)`.

Registers: those of `hvy`, with `r180 = lo`, `r181 = hi`, `r182` the middle, `r183 … r187`
scratch; `r160` receives the tested level.
-/

@[expose] public section

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset Map CycleSearch

/-! ### The program -/

/-- Clear one sum `r183`. -/
def zbody : Stmt := block [.addN 185 166 183, .storeN 185 140, .addN 183 183 141]

/-- **Clear the sums** at `bSum + x`, `x ≤ k`. -/
def zpass : Stmt := .seq (block [.copyN 183 140, .addN 184 143 141]) (.whileLtN 183 184 zbody)

/-- **One bisection step.** -/
def bbody : Stmt :=
  .seq (block [.addN 186 141 141, .addN 182 180 181, .divN 182 182 186, .copyN 160 182])
    (.seq zpass (.seq hvy (.seq (.ifLtN 169 141 (.instr (.copyN 181 182))
      (.instr (.copyN 180 182))) (.instr (.addN 187 180 141)))))

/-- **The last heavy level** by bisection. -/
def bsearch : Stmt :=
  .seq (block [.copyN 180 140, .copyN 181 161, .addN 187 180 141]) (.whileLtN 187 181 bbody)

theorem clog_half {g : ℕ} (hg : 2 ≤ g) : Nat.clog 2 (g - g / 2) + 1 ≤ Nat.clog 2 g := by
  rw [Nat.clog_of_two_le (by norm_num) hg]
  have := Nat.clog_mono_right 2 (show g - g / 2 ≤ (g + 2 - 1) / 2 by omega)
  omega

section proofs

variable {W : ℕ} {P' : Input} {k bA bL bS bR l n bV bLv bF bw bSum : ℕ}

theorem zpass_exec (hW : bSum + k + 1 ≤ W) (c : Config) (hc : WordsBounded W c)
    (hR : CR k bA bL bS bR c) (hH : HR l n bV bLv bF bw bSum c) :
    ∃ c' t, Exec P' W zpass c c' t ∧ t ≤ 5 * k + 9 ∧ (∀ x ≤ k, c'.nmem (bSum + x) = 0) ∧
      (∀ r, r < 183 ∨ 186 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bSum ∨ bSum + k + 1 ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  obtain ⟨r140, r141, r142, r143, r144, r145, r146, r147⟩ := hR
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 183 = i ∧
    c'.nreg 184 = k + 1 ∧ (∀ x < i, c'.nmem (bSum + x) = 0) ∧
    (∀ r, r < 183 ∨ 186 ≤ r → c'.nreg r = c.nreg r) ∧
    (∀ a, a < bSum ∨ bSum + k + 1 ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output
  obtain ⟨c₁, k₁, e₁, hI₁, rfl⟩ : ∃ c₁ k₁, Exec P' W (block [.copyN 183 140, .addN 184 143 141])
      c c₁ k₁ ∧ I 0 c₁ ∧ k₁ = 2 := by
    exec_block
    · config_simp; rw [r143, r141]; omega
    refine ⟨⟨‹_›, by config_simp; exact r140, by config_simp; rw [r143, r141],
      fun x hx => absurd hx (by omega), fun r hr => by
        config_simp; simp only [upd_apply]; split_ifs <;> omega, fun a _ => rfl, rfl⟩, rfl⟩
  obtain ⟨c', t, e, hI, ht⟩ := Exec.forN (P := P') (W := W) (ri := 183) (rN := 184)
    (N := k + 1) (lo := 0) (B := 3) (body := zbody) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c₂ ⟨hw, h183, h184, hz, hr, hf, ho⟩ hi => by
      have g166 : c₂.nreg 166 = bSum := by rw [hr 166 (by omega)]; exact hH.r166
      have g140 : c₂.nreg 140 = 0 := by rw [hr 140 (by omega)]; exact r140
      have g141 : c₂.nreg 141 = 1 := by rw [hr 141 (by omega)]; exact r141
      unfold zbody
      exec_block
      · rw [g166, h183]; omega
      · config_simp; rw [h183, g141]; omega
      refine ⟨⟨‹_›, by config_simp; rw [h183, g141], by config_simp; exact h184,
        fun x hx => ?_, fun r hr' => by
          config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r hr',
        fun a ha => ?_, by config_simp; exact ho⟩, by omega⟩
      · config_simp; rw [g166, h183, g140]
        by_cases hx' : x = i
        · subst hx'; simp
        · rw [upd_other _ _ _ (by omega)]; exact hz x (by omega)
      · config_simp; rw [g166, h183, upd_other _ _ _ (by omega)]; exact hf a (by omega))
    (by omega) hI₁
  obtain ⟨-, -, -, hz, hr, hf, ho⟩ := hI
  exact ⟨c', 2 + t, .seq e₁ e, by omega, fun x hx => hz x (by omega), hr,
    fun a ha => hf a (by omega), ho⟩

end proofs

/-! ### The bisection -/

section Search

variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] {M : Map D P}
  {T₀ T : M.SpTree} {k n : ℕ} {cd : D ≃ Fin (3 * k)} {A Tm V L fd w : ℕ → ℕ}
  {vi : P ≃ Fin n} {wP : P → ℕ} {fdD : P → D}

variable (M T₀ T k n cd A Tm V L fd w vi wP fdD) in
/-- The data of the heavy test: a coded triangulation, a breadth-first tree, the numberings of
the vertices, the levels, a dart at every vertex and the weights. -/
structure Setup : Prop where
  plane : M.IsPlane
  bfs : IsBFS T
  tri : ∀ d : D, M.φ (M.φ (M.φ d)) = d
  coded : Coded M T₀ k cd A Tm
  hV : ∀ x, V (cd x) = vi (M.vert x)
  hL : ∀ v, L (vi v) = T.height v
  hfdD : ∀ v, M.vert (fdD v) = v
  hfd : ∀ v, fd (vi v) = cd (fdD v)
  hw : ∀ v, w (vi v) = wP v

/-- The memory holds the map, the levels, the darts and the weights. -/
def InMem (k n bR bV bLv bF bw : ℕ) (A V L fd w : ℕ → ℕ) (m : ℕ → ℕ) : Prop :=
  (∀ x < 3 * k, m (bR + x) = A x) ∧ (∀ x < 3 * k, m (bV + x) = V x) ∧
    (∀ v < n, m (bLv + v) = L v) ∧ (∀ v < n, m (bF + v) = fd v) ∧ (∀ v < n, m (bw + v) = w v)

/-- The weights `wP v / Σ wP`. -/
noncomputable def wR (wP : P → ℕ) (v : P) : ℝ := (wP v : ℝ) / ∑ u, (wP u : ℝ)

variable {W : ℕ} {P' : Input} {bA bL bS bR bV bLv bF bw bSum : ℕ}

theorem InMem.of {m m' : ℕ → ℕ} (h : InMem k n bR bV bLv bF bw A V L fd w m)
    (hlay : bR + 3 * k ≤ bA ∧ bV + 3 * k ≤ bA ∧ bLv + n ≤ bA ∧ bF + n ≤ bA ∧ bw + n ≤ bA)
    (e : ∀ a < bA, m' a = m a) : InMem k n bR bV bLv bF bw A V L fd w m' :=
  ⟨fun x hx => (e _ (by omega)).trans (h.1 x hx), fun x hx => (e _ (by omega)).trans (h.2.1 x hx),
    fun v hv => (e _ (by omega)).trans (h.2.2.1 v hv),
    fun v hv => (e _ (by omega)).trans (h.2.2.2.1 v hv),
    fun v hv => (e _ (by omega)).trans (h.2.2.2.2 v hv)⟩

/-- **One bisection step**: the middle level `mid` of `lo < hi` is tested; `lo := mid` if it is
heavy, `hi := mid` otherwise. -/
theorem bbody_exec (hS : Setup M T₀ T k n cd A Tm V L fd w vi wP fdD)
    (hlay : bR + 3 * k ≤ bA ∧ bV + 3 * k ≤ bA ∧ bLv + n ≤ bA ∧ bF + n ≤ bA ∧ bw + n ≤ bA ∧
      bA + k ≤ bL ∧ bL + k ≤ bS ∧ bS + k ≤ bSum)
    (hW : bSum + 3 * k + 4 * n + 1 ≤ W ∧ 3 * ∑ v, wP v ≤ W) {lo hi l₀ : ℕ} (hlh : lo + 1 < hi)
    (hhi : hi ≤ n) (c : Config) (hc : WordsBounded W c) (hR : CR k bA bL bS bR c)
    (hH : HR l₀ n bV bLv bF bw bSum c) (h168 : c.nreg 168 = ∑ v, wP v)
    (hm : InMem k n bR bV bLv bF bw A V L fd w c.nmem) (h180 : c.nreg 180 = lo)
    (h181 : c.nreg 181 = hi) :
    ∃ c' t, Exec P' W bbody c c' t ∧ t ≤ 106 * k + 21 * n + 28 ∧
      (Heavy T (wR wP) ((lo + hi) / 2) → c'.nreg 180 = (lo + hi) / 2 ∧ c'.nreg 181 = hi) ∧
      (¬ Heavy T (wR wP) ((lo + hi) / 2) → c'.nreg 180 = lo ∧ c'.nreg 181 = (lo + hi) / 2) ∧
      c'.nreg 187 = c'.nreg 180 + 1 ∧ CR k bA bL bS bR c' ∧
      HR ((lo + hi) / 2) n bV bLv bF bw bSum c' ∧ c'.nreg 168 = ∑ v, wP v ∧
      InMem k n bR bV bLv bF bw A V L fd w c'.nmem ∧ c'.output = c.output := by
  have hR' := hR
  obtain ⟨r140, r141, r142, r143, r144, r145, r146, r147⟩ := hR
  have hH' := hH
  obtain ⟨r160, r161, r162, r163, r164, r165, r166⟩ := hH
  set mid := (lo + hi) / 2 with hmid
  unfold bbody
  refine spec_seq ?_
  exec_block
  · rw [r141]; omega
  · config_simp; rw [h180, h181]; have := hc.1 180; have := hc.1 181; omega
  rename_i hwb
  simp only [r141, h180, h181] at hwb ⊢
  -- the sums
  refine spec_seq ?_
  refine spec_use (zpass_exec (W := W) (k := k) (bSum := bSum) (l := mid) (n := n) (bV := bV)
    (bLv := bLv) (bF := bF) (bw := bw) (bA := bA) (bL := bL) (bS := bS) (bR := bR) (by omega) _ hwb
    (hR'.of fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> omega)
    ⟨by config_simp; exact hmid.symm, by config_simp; exact r161, by config_simp; exact r162,
      by config_simp; exact r163, by config_simp; exact r164, by config_simp; exact r165,
      by config_simp; exact r166⟩) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨hz₁, hr₁, hf₁, ho₁⟩
  have hR₂ : CR k bA bL bS bR c₁ := hR'.of fun r hr => by
    rw [hr₁ r (Or.inl (by omega))]; config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hH₂ : HR mid n bV bLv bF bw bSum c₁ :=
    ⟨by rw [hr₁ 160 (by omega)]; config_simp; exact hmid.symm,
    by rw [hr₁ 161 (by omega)]; config_simp; exact r161,
    by rw [hr₁ 162 (by omega)]; config_simp; exact r162,
    by rw [hr₁ 163 (by omega)]; config_simp; exact r163,
    by rw [hr₁ 164 (by omega)]; config_simp; exact r164,
    by rw [hr₁ 165 (by omega)]; config_simp; exact r165,
    by rw [hr₁ 166 (by omega)]; config_simp; exact r166⟩
  have hm₁ : InMem k n bR bV bLv bF bw A V L fd w c₁.nmem :=
    hm.of ⟨hlay.1, hlay.2.1, hlay.2.2.1, hlay.2.2.2.1, hlay.2.2.2.2.1⟩
      fun a ha => by rw [hf₁ a (Or.inl (by omega))]
  obtain ⟨m1, m2, m3, m4, m5⟩ := hm₁
  have hmid1 : 1 ≤ mid := by omega
  have hmidn : mid < n := by omega
  refine spec_seq ?_
  refine spec_use (hvy_heavy hS.coded vi hS.hV hS.hL hS.plane hS.bfs hS.tri hmid1 wP fdD
    hS.hfdD hS.hfd hS.hw hlay ⟨by omega, hW.2⟩ c₁ hw₁ hR₂ hH₂
    (by rw [hr₁ 168 (Or.inl (by omega))]; config_simp; exact h168) m1 m2 m3 m4 m5 hz₁) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hfl1, hfl, hr₂, hf₂, ho₂⟩
  have g : ∀ r, (r < 150 ∨ (160 ≤ r ∧ r < 169) ∨ 180 ≤ r) → r < 183 ∨ 186 ≤ r →
      c₂.nreg r = c₁.nreg r := fun r h1 _ => hr₂ r h1
  have g180 : c₂.nreg 180 = lo := by
    rw [g 180 (by omega) (by omega), hr₁ 180 (by omega)]; config_simp; exact h180
  have g181 : c₂.nreg 181 = hi := by
    rw [g 181 (by omega) (by omega), hr₁ 181 (by omega)]; config_simp; exact h181
  have g182 : c₂.nreg 182 = mid := by
    rw [g 182 (by omega) (by omega), hr₁ 182 (by omega)]; config_simp; exact hmid.symm
  have g141 : c₂.nreg 141 = 1 := by
    rw [g 141 (by omega) (by omega), hr₁ 141 (by omega)]; config_simp; exact r141
  have hR₃ : CR k bA bL bS bR c₂ := hR₂.of fun r hr => hr₂ r (Or.inl hr)
  have hH₃ : HR mid n bV bLv bF bw bSum c₂ := hH₂.of fun r h1 h2 => hr₂ r (Or.inr (Or.inl ⟨h1,
    by omega⟩))
  have g168 : c₂.nreg 168 = ∑ v, wP v := by
    rw [hr₂ 168 (by omega), hr₁ 168 (by omega)]; config_simp; exact h168
  have hm₂ : InMem k n bR bV bLv bF bw A V L fd w c₂.nmem := (hm.of
    ⟨hlay.1, hlay.2.1, hlay.2.2.1, hlay.2.2.2.1, hlay.2.2.2.2.1⟩ fun a ha => by
      rw [hf₂ a (Or.inl ha), hf₁ a (Or.inl (by omega))])
  refine spec_seq ?_
  by_cases hh : Heavy T (wR wP) mid
  · have h1 : c₂.nreg 169 = 1 := hfl.2 hh
    refine spec_ifLtN_false (by rw [h1, g141]; omega) ?_
    refine spec_instr (Exec.copyN hw₂ 180 182) fun hw => ?_
    refine spec_instr (Exec.addN hw _ _ _ (by config_simp; rw [g182, g141]; omega)) fun hw' => ?_
    refine ⟨by omega, fun _ => ⟨by config_simp; exact g182, by config_simp; exact g181⟩,
      fun h' => absurd hh h', by config_simp; rw [g182, g141], hR₃.of fun r hr => by
      config_simp; simp only [upd_apply]; split_ifs <;> omega, hH₃.of fun r h1 h2 => by
      config_simp; simp only [upd_apply]; split_ifs <;> omega, by config_simp; exact g168,
      hm₂, by config_simp; rw [ho₂, ho₁]⟩
  · have h0 : c₂.nreg 169 = 0 := by
      have := hfl.not.2 hh; omega
    refine spec_ifLtN_true (by rw [h0, g141]; omega) ?_
    refine spec_instr (Exec.copyN hw₂ 181 182) fun hw => ?_
    refine spec_instr (Exec.addN hw _ _ _ (by config_simp; rw [g180, g141]; omega)) fun hw' => ?_
    refine ⟨by omega, fun h' => absurd h' hh,
      fun _ => ⟨by config_simp; exact g180, by config_simp; exact g182⟩,
      by config_simp; rw [g180, g141], hR₃.of fun r hr => by
      config_simp; simp only [upd_apply]; split_ifs <;> omega, hH₃.of fun r h1 h2 => by
      config_simp; simp only [upd_apply]; split_ifs <;> omega, by config_simp; exact g168,
      hm₂, by config_simp; rw [ho₂, ho₁]⟩

omit [DecidableEq P] in
theorem wR_nonneg (wP : P → ℕ) (v : P) : 0 ≤ wR wP v := by
  unfold wR; positivity

/-- **The last heavy level.** For a coded triangulation with `n ≥ 1` vertices, a breadth-first
tree, levels, darts and weights in memory, `bsearch` ends within
`(106 k + 21 n + 30) ⌈log₂ n⌉ + 5` steps with a level `ls < n` in `r180` which is `0` or heavy,
and no level above `ls` is heavy (`PlanarSeparator.Map.Heavy` for the weights `wP v / Σ wP`). -/
theorem bsearch_exec (hS : Setup M T₀ T k n cd A Tm V L fd w vi wP fdD) (hn : 1 ≤ n)
    (hlay : bR + 3 * k ≤ bA ∧ bV + 3 * k ≤ bA ∧ bLv + n ≤ bA ∧ bF + n ≤ bA ∧ bw + n ≤ bA ∧
      bA + k ≤ bL ∧ bL + k ≤ bS ∧ bS + k ≤ bSum)
    (hW : bSum + 3 * k + 4 * n + 1 ≤ W ∧ 3 * ∑ v, wP v ≤ W) {l₀ : ℕ} (c : Config)
    (hc : WordsBounded W c) (hR : CR k bA bL bS bR c) (hH : HR l₀ n bV bLv bF bw bSum c)
    (h168 : c.nreg 168 = ∑ v, wP v) (hm : InMem k n bR bV bLv bF bw A V L fd w c.nmem) :
    ∃ c' t, Exec P' W bsearch c c' t ∧ t ≤ (106 * k + 21 * n + 30) * Nat.clog 2 n + 5 ∧
      c'.nreg 180 < n ∧ (c'.nreg 180 = 0 ∨ Heavy T (wR wP) (c'.nreg 180)) ∧
      (∀ l, c'.nreg 180 < l → ¬ Heavy T (wR wP) l) ∧ c'.output = c.output := by
  have hcard : Fintype.card P = n := by rw [Fintype.card_congr vi, Fintype.card_fin]
  have hnot : ¬ Heavy T (wR wP) n := fun h => by
    have := heavy_lt hS.plane hS.bfs hn h; omega
  set K := 106 * k + 21 * n + 30
  let J : Config → Prop := fun c' => WordsBounded W c' ∧ CR k bA bL bS bR c' ∧
    (∃ l', HR l' n bV bLv bF bw bSum c') ∧ c'.nreg 168 = ∑ v, wP v ∧
    InMem k n bR bV bLv bF bw A V L fd w c'.nmem ∧ c'.nreg 180 < c'.nreg 181 ∧
    c'.nreg 181 ≤ n ∧ c'.nreg 187 = c'.nreg 180 + 1 ∧
    (c'.nreg 180 = 0 ∨ Heavy T (wR wP) (c'.nreg 180)) ∧ ¬ Heavy T (wR wP) (c'.nreg 181) ∧
    c'.output = c.output
  have hR' := hR
  obtain ⟨r140, r141, r142, r143, r144, r145, r146, r147⟩ := hR
  obtain ⟨c₁, k₁, e₁, hJ₁, h180₁, h181₁, rfl⟩ : ∃ c₁ k₁, Exec P' W (block [.copyN 180 140,
      .copyN 181 161, .addN 187 180 141]) c c₁ k₁ ∧ J c₁ ∧ c₁.nreg 180 = 0 ∧ c₁.nreg 181 = n ∧
      k₁ = 3 := by
    exec_block
    · config_simp; rw [r140, r141]; omega
    refine ⟨⟨‹_›, hR'.of fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> omega,
      ⟨l₀, hH.of fun r h1 h2 => by config_simp; simp only [upd_apply]; split_ifs <;> omega⟩,
      by config_simp; exact h168, hm, by config_simp; rw [r140, hH.r161]; omega,
      by config_simp; rw [hH.r161], by config_simp; rw [r141],
      by config_simp; rw [r140]; exact Or.inl rfl, by config_simp; rw [hH.r161]; exact hnot, rfl⟩,
      by config_simp; exact r140, by config_simp; exact hH.r161, rfl⟩
  obtain ⟨c', t, e, hJ, hn', ht⟩ := Exec.whileLtN_potential (P := P') (W := W) (a := 187)
    (b := 181) (body := bbody) J (fun c' => K * Nat.clog 2 (c'.nreg 181 - c'.nreg 180))
    (fun _ h => h.1)
    (fun c₂ ⟨hw, hR₂, ⟨l', hH₂⟩, h168₂, hm₂, hlh, hhi, h187, hlo, hhi', ho⟩ hlt => by
      rw [h187] at hlt
      obtain ⟨c₃, t₃, e₃, ht₃, hyes, hno, h187₃, hR₃, hH₃, h168₃, hm₃, ho₃⟩ :=
        bbody_exec (P' := P') hS hlay hW hlt hhi c₂ hw hR₂ hH₂ h168₂ hm₂ rfl rfl
      set lo := c₂.nreg 180
      set hi := c₂.nreg 181
      have hg : (2 : ℕ) ≤ hi - lo := by omega
      have hcl := clog_half hg
      refine ⟨c₃, t₃, e₃, ?_, ?_⟩
      · by_cases hh : Heavy T (wR wP) ((lo + hi) / 2)
        · obtain ⟨a1, a2⟩ := hyes hh
          exact ⟨e₃.wb_right, hR₃, ⟨_, hH₃⟩, h168₃, hm₃, by omega, by omega, h187₃,
            Or.inr (by rw [a1]; exact hh), by rw [a2]; exact hhi', by rw [ho₃, ho]⟩
        · obtain ⟨a1, a2⟩ := hno hh
          exact ⟨e₃.wb_right, hR₃, ⟨_, hH₃⟩, h168₃, hm₃, by omega, by omega, h187₃,
            by rw [a1]; exact hlo, by rw [a2]; exact hh, by rw [ho₃, ho]⟩
      · have hgap : c₃.nreg 181 - c₃.nreg 180 ≤ (hi - lo) - (hi - lo) / 2 := by
          by_cases hh : Heavy T (wR wP) ((lo + hi) / 2)
          · obtain ⟨a1, a2⟩ := hyes hh; rw [a1, a2]; omega
          · obtain ⟨a1, a2⟩ := hno hh; rw [a1, a2]; omega
        have := Nat.clog_mono_right 2 hgap
        have h2 : K * Nat.clog 2 (c₃.nreg 181 - c₃.nreg 180) + K ≤ K * Nat.clog 2 (hi - lo) := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
        omega) hJ₁
  obtain ⟨-, -, -, -, -, hlh, hhi, h187, hlo, hhi', ho⟩ := hJ
  rw [h187] at hn'
  have hfin : c'.nreg 181 = c'.nreg 180 + 1 := by omega
  refine ⟨c', 3 + t, .seq e₁ e, ?_, by omega, hlo, fun l hl hh => hhi' ?_, ho⟩
  · have : Nat.clog 2 (c₁.nreg 181 - c₁.nreg 180) = Nat.clog 2 n := by
      rw [h180₁, h181₁, Nat.sub_zero]
    rw [this] at ht
    omega
  · rw [hfin]; exact heavy_mono (wR_nonneg wP) (by omega) hh

end Search

end MillerProg

end PlanarSeparator
