module

public import PlanarSeparator.Machine.MillerS8Run
public import PlanarSeparator.Machine.Miller

/-!
# Miller's separator on the machine: steps 1–8 as one program

The program `millerA` runs steps 1–8 of Miller's separator algorithm
(`PlanarSeparator/Machine/Miller.lean`) on a coded triangulation with `k ≥ 2` triangles and
`n` vertices, for natural vertex weights `wP` of positive total:

1. `bprog`: the breadth-first tree `T` from the vertex `0`, its levels at `bLv` and its parent
   darts at `bPr`;
2. `dpass`: a dart at every vertex (at `bF`);
3. `wsum`: the total weight `Σ wP` (in `r168`);
4. `bsearch`: the last heavy level `ls` (in `r180`) for the weights `wR wP = wP / Σ wP`;
5. `thin`: two thin levels `l₀ = ls - ⌊√n⌋ + j₀` and `l₂ = ls + 1 + j₂`, `j₀, j₂ ≤ ⌊√n⌋`;
6. `innerStep`: if `⌊√n⌋ < ls`, the tree `T₁` of an inner region at the (heavy) level `l₀`
   (`iprog`); otherwise `T₁ = T` and the level `0` (`Map.inner_univ`). The parent darts of `T₁`
   replace those of `T` at `bPr`;
7. `concStep`: the moved weights of a concentration map at the level `l₂` at `bWC` (`cprog` if
   `l₂ < n`, the weights themselves otherwise);
8. `step8run`: a dart `δ` off `T₁` (in `r353`) whose strict inside and strict outside weigh at
   most `2/3` for the moved weights.

The arrays are laid out by `ABase`/`ALay` (the reversals at `0`, the cycle search below `11 k`,
the Miller arrays above), the starting registers by `ARegs`. The theorem `millerA_spec` bounds
the running time by `O((k + n) log n)` and gives the data of steps 9–10: the hypotheses `hδ`,
`hA`, `hB` and `hlight` of `PlanarSeparator.Map.band_separator_of_dart`, the levels, the
concentration map and the parent darts of `T₁`; `millerA_band` applies the band theorem.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset Map CycleSearch

/-! ### The bisection, with its frame -/

section Search

variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] {M : Map D P}
  {T₀ T : M.SpTree} {k n : ℕ} {cd : D ≃ Fin (3 * k)} {A Tm V L fd w : ℕ → ℕ}
  {vi : P ≃ Fin n} {wP : P → ℕ} {fdD : P → D}
variable {W : ℕ} {P' : Input} {bA bL bS bR bV bLv bF bw bSum : ℕ}

/-- `bbody_exec` with the memory frame. -/
theorem bbody_exec' (hS : Setup M T₀ T k n cd A Tm V L fd w vi wP fdD)
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
      InMem k n bR bV bLv bF bw A V L fd w c'.nmem ∧ c'.output = c.output ∧
      (∀ a, a < bA ∨ bSum + k + 1 ≤ a → c'.nmem a = c.nmem a) := by
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
      hm₂, by config_simp; rw [ho₂, ho₁],
      fun a ha => by config_simp; rw [hf₂ a ha, hf₁ a (by omega)]⟩
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
      hm₂, by config_simp; rw [ho₂, ho₁],
      fun a ha => by config_simp; rw [hf₂ a ha, hf₁ a (by omega)]⟩

/-- **`bsearch_exec` with its frame**: the constant registers, the total weight, the memory of
the heavy test and the memory outside `[bA, bSum + k]` are kept. -/
theorem bsearch_exec' (hS : Setup M T₀ T k n cd A Tm V L fd w vi wP fdD) (hn : 1 ≤ n)
    (hlay : bR + 3 * k ≤ bA ∧ bV + 3 * k ≤ bA ∧ bLv + n ≤ bA ∧ bF + n ≤ bA ∧ bw + n ≤ bA ∧
      bA + k ≤ bL ∧ bL + k ≤ bS ∧ bS + k ≤ bSum)
    (hW : bSum + 3 * k + 4 * n + 1 ≤ W ∧ 3 * ∑ v, wP v ≤ W) {l₀ : ℕ} (c : Config)
    (hc : WordsBounded W c) (hR : CR k bA bL bS bR c) (hH : HR l₀ n bV bLv bF bw bSum c)
    (h168 : c.nreg 168 = ∑ v, wP v) (hm : InMem k n bR bV bLv bF bw A V L fd w c.nmem) :
    ∃ c' t, Exec P' W bsearch c c' t ∧ t ≤ (106 * k + 21 * n + 30) * Nat.clog 2 n + 5 ∧
      c'.nreg 180 < n ∧ (c'.nreg 180 = 0 ∨ Heavy T (wR wP) (c'.nreg 180)) ∧
      (∀ l, c'.nreg 180 < l → ¬ Heavy T (wR wP) l) ∧ c'.output = c.output ∧
      CR k bA bL bS bR c' ∧ c'.nreg 168 = ∑ v, wP v ∧
      InMem k n bR bV bLv bF bw A V L fd w c'.nmem ∧
      (∀ a, a < bA ∨ bSum + k + 1 ≤ a → c'.nmem a = c.nmem a) := by
  have hcard : Fintype.card P = n := by rw [Fintype.card_congr vi, Fintype.card_fin]
  have hnot : ¬ Heavy T (wR wP) n := fun h => by
    have := heavy_lt hS.plane hS.bfs hn h; omega
  set K := 106 * k + 21 * n + 30
  let J : Config → Prop := fun c' => WordsBounded W c' ∧ CR k bA bL bS bR c' ∧
    (∃ l', HR l' n bV bLv bF bw bSum c') ∧ c'.nreg 168 = ∑ v, wP v ∧
    InMem k n bR bV bLv bF bw A V L fd w c'.nmem ∧ c'.nreg 180 < c'.nreg 181 ∧
    c'.nreg 181 ≤ n ∧ c'.nreg 187 = c'.nreg 180 + 1 ∧
    (c'.nreg 180 = 0 ∨ Heavy T (wR wP) (c'.nreg 180)) ∧ ¬ Heavy T (wR wP) (c'.nreg 181) ∧
    c'.output = c.output ∧ (∀ a, a < bA ∨ bSum + k + 1 ≤ a → c'.nmem a = c.nmem a)
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
      by config_simp; rw [r140]; exact Or.inl rfl, by config_simp; rw [hH.r161]; exact hnot, rfl,
      fun a _ => rfl⟩,
      by config_simp; exact r140, by config_simp; exact hH.r161, rfl⟩
  obtain ⟨c', t, e, hJ, hn', ht⟩ := Exec.whileLtN_potential (P := P') (W := W) (a := 187)
    (b := 181) (body := bbody) J (fun c' => K * Nat.clog 2 (c'.nreg 181 - c'.nreg 180))
    (fun _ h => h.1)
    (fun c₂ ⟨hw, hR₂, ⟨l', hH₂⟩, h168₂, hm₂, hlh, hhi, h187, hlo, hhi', ho, hfr⟩ hlt => by
      rw [h187] at hlt
      obtain ⟨c₃, t₃, e₃, ht₃, hyes, hno, h187₃, hR₃, hH₃, h168₃, hm₃, ho₃, hf₃⟩ :=
        bbody_exec' (P' := P') hS hlay hW hlt hhi c₂ hw hR₂ hH₂ h168₂ hm₂ rfl rfl
      set lo := c₂.nreg 180
      set hi := c₂.nreg 181
      have hg : (2 : ℕ) ≤ hi - lo := by omega
      have hcl := clog_half hg
      refine ⟨c₃, t₃, e₃, ?_, ?_⟩
      · by_cases hh : Heavy T (wR wP) ((lo + hi) / 2)
        · obtain ⟨a1, a2⟩ := hyes hh
          exact ⟨e₃.wb_right, hR₃, ⟨_, hH₃⟩, h168₃, hm₃, by omega, by omega, h187₃,
            Or.inr (by rw [a1]; exact hh), by rw [a2]; exact hhi', by rw [ho₃, ho],
            fun a ha => by rw [hf₃ a ha, hfr a ha]⟩
        · obtain ⟨a1, a2⟩ := hno hh
          exact ⟨e₃.wb_right, hR₃, ⟨_, hH₃⟩, h168₃, hm₃, by omega, by omega, h187₃,
            by rw [a1]; exact hlo, by rw [a2]; exact hh, by rw [ho₃, ho],
            fun a ha => by rw [hf₃ a ha, hfr a ha]⟩
      · have hgap : c₃.nreg 181 - c₃.nreg 180 ≤ (hi - lo) - (hi - lo) / 2 := by
          by_cases hh : Heavy T (wR wP) ((lo + hi) / 2)
          · obtain ⟨a1, a2⟩ := hyes hh; rw [a1, a2]; omega
          · obtain ⟨a1, a2⟩ := hno hh; rw [a1, a2]; omega
        have := Nat.clog_mono_right 2 hgap
        have h2 : K * Nat.clog 2 (c₃.nreg 181 - c₃.nreg 180) + K ≤ K * Nat.clog 2 (hi - lo) := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
        omega) hJ₁
  obtain ⟨-, hRf, -, h168f, hmf, hlh, hhi, h187, hlo, hhi', ho, hff⟩ := hJ
  rw [h187] at hn'
  have hfin : c'.nreg 181 = c'.nreg 180 + 1 := by omega
  refine ⟨c', 3 + t, .seq e₁ e, ?_, by omega, hlo, fun l hl hh => hhi' ?_, ho, hRf, h168f, hmf,
    hff⟩
  · have : Nat.clog 2 (c₁.nreg 181 - c₁.nreg 180) = Nat.clog 2 n := by
      rw [h180₁, h181₁, Nat.sub_zero]
    rw [this] at ht
    omega
  · rw [hfin]; exact heavy_mono (wR_nonneg wP) (by omega) hh

end Search

/-! ### Without concentration -/

/-- Copy the weight of `r395 = v` from `bw` to `bWC`. -/
def wcbody : Stmt :=
  block [.addN 396 165 395, .loadN 397 396, .addN 396 190 395, .storeN 396 397, .addN 395 395 141]

/-- **The weights unmoved**: copy `bw` to `bWC` (when the level `l₂` is above every vertex). -/
def wcopy : Stmt := .seq (.instr (.copyN 395 140)) (.whileLtN 395 161 wcbody)

/-- `wcopy` ends within `7 n + 3` steps with the `n` numbers at `bw` copied to `bWC`. -/
theorem wcopy_exec {W : ℕ} {P : Input} {n bw bWC : ℕ} (hlay : bw + n ≤ bWC) (hW : bWC + n ≤ W)
    (c : Config) (hc : WordsBounded W c) (h140 : c.nreg 140 = 0) (h141 : c.nreg 141 = 1)
    (h161 : c.nreg 161 = n) (h165 : c.nreg 165 = bw) (h190 : c.nreg 190 = bWC) :
    ∃ c' t, Exec P W wcopy c c' t ∧ t ≤ 7 * n + 3 ∧
      (∀ u < n, c'.nmem (bWC + u) = c.nmem (bw + u)) ∧
      (∀ a, a < bWC ∨ bWC + n ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 395 = i ∧ i ≤ n ∧
    (∀ r, r ≠ 395 → r ≠ 396 → r ≠ 397 → c'.nreg r = c.nreg r) ∧
    (∀ u < i, c'.nmem (bWC + u) = c.nmem (bw + u)) ∧
    (∀ a, ¬ (bWC ≤ a ∧ a < bWC + i) → c'.nmem a = c.nmem a) ∧ c'.output = c.output
  have e₁ := Exec.copyN (P := P) hc 395 140
  obtain ⟨c', t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 395) (rN := 161) (N := n)
    (lo := 0) (B := 5) (body := wcbody) I
    (fun i c' h => ⟨h.1, h.2.1, (h.2.2.2.1 161 (by omega) (by omega) (by omega)).trans h161⟩)
    (fun i c₁ ⟨hw, h395, hi, hr, hd, hm, ho⟩ hlt => by
      have hc := hw
      have g165 := (hr 165 (by omega) (by omega) (by omega)).trans h165
      have g190 := (hr 190 (by omega) (by omega) (by omega)).trans h190
      have g141 := (hr 141 (by omega) (by omega) (by omega)).trans h141
      have mw : c₁.nmem (bw + i) = c.nmem (bw + i) := hm _ (by omega)
      unfold wcbody
      exec_block
      all_goals try (config_simp; simp only [g165, g190, h395, g141]; omega)
      refine ⟨⟨‹_›, ?_, by omega, fun r a b d => ?_, fun u hu => ?_, fun a ha => ?_, ho⟩, le_rfl⟩
      all_goals config_simp
      · rw [h395, g141]
      · simp only [upd_apply]; split_ifs <;> first | omega | exact hr r a b d
      · simp only [g165, g190, h395, mw]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
        · rw [upd_other _ _ _ (by omega)]; exact hd u hu
        · rw [upd_same]
      · simp only [g165, g190, h395, mw]
        rw [upd_other _ _ _ (by omega)]; exact hm a (by omega))
    (by omega) ⟨e₁.wb_right, by config_simp; exact h140, by omega,
      fun r a _ _ => by config_simp; rw [upd_other _ _ _ a], fun u hu => absurd hu (by omega),
      fun a _ => rfl, rfl⟩
  obtain ⟨-, -, -, -, hd, hm, ho⟩ := hI
  exact ⟨c', 1 + t, .seq e₁ e, by omega, hd, fun a ha => hm a (by omega), ho⟩

section Conc

variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] {M : Map D P}

/-- Above every vertex, the identity is a concentration. -/
theorem isConc_id {T : M.SpTree} {l : ℕ} (hl : ∀ v, T.height v ≤ l) : IsConc T l id :=
  ⟨fun _ _ => rfl, fun v h => absurd (hl v) (by omega), fun u _ h _ _ => absurd (hl u) (by omega)⟩

/-- The identity moves no weight. -/
theorem wcf_id (w : P → ℝ) (u : P) : wcf id w u = w u := by
  unfold wcf
  rw [sum_filter]
  simp

end Conc

/-! ### Steps 1–8 -/

/-- The inner region at `l₀ = ls - t + j₀` if `t < ls`. -/
def innerStep : Stmt :=
  .ifLtN 201 180 (.seq (block [.subN 160 180 201, .addN 160 160 204]) iprog) .skip

/-- The concentrated weights at `l₂ = ls + 1 + j₂` (the weights unmoved if `l₂ ≥ n`). -/
def concStep : Stmt :=
  .seq (block [.addN 160 180 141, .addN 160 160 210]) (.ifLtN 160 161 cprog wcopy)

/-- **Steps 1–7** and the registers of step 8. -/
def millerPre : Stmt :=
  .seq (.instr (.copyN 250 165)) <| .seq bprog <| .seq dpass <| .seq wsum <|
  .seq (.instr (.copyN 168 320)) <| .seq bsearch <| .seq thin <| .seq innerStep <|
  .seq concStep (block [.copyN 250 190, .copyN 255 140])

/-- **Steps 1–8 of Miller's separator**: the breadth-first search, a dart at every vertex, the
total weight, the last heavy level, the thin levels, the inner region (if `t < ls`), the
concentrated weights at `l₂` (or the weights unmoved if `l₂ ≥ n`), and step 8 for the tree
`T₁` and these weights. -/
def millerA : Stmt := .seq millerPre step8run

section Glue

variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] {M : Map D P}
  {T₀ T : M.SpTree} {k n : ℕ} {cd : D ≃ Fin (3 * k)} {A Tm V L fd w : ℕ → ℕ}
  {vi : P ≃ Fin n} {wP : P → ℕ} {fdD : P → D}
variable {W : ℕ} {P' : Input} {bA bL bS bR bV bLv bF bw bSum bPr bRep bCN bWC : ℕ}

/-- The memory still holds the data if it is unchanged on the arrays. -/
theorem inMem_of {m m' : ℕ → ℕ} (h : InMem k n bR bV bLv bF bw A V L fd w m)
    (e : ∀ a, (bR ≤ a ∧ a < bR + 3 * k) ∨ (bV ≤ a ∧ a < bV + 3 * k) ∨ (bLv ≤ a ∧ a < bLv + n) ∨
      (bF ≤ a ∧ a < bF + n) ∨ (bw ≤ a ∧ a < bw + n) → m' a = m a) :
    InMem k n bR bV bLv bF bw A V L fd w m' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨fun x hx => (e _ (by omega)).trans (h1 x hx), fun x hx => (e _ (by omega)).trans (h2 x hx),
    fun v hv => (e _ (by omega)).trans (h3 v hv), fun v hv => (e _ (by omega)).trans (h4 v hv),
    fun v hv => (e _ (by omega)).trans (h5 v hv)⟩

/-- The normalized weights add up to `1`. -/
theorem sum_wR (hpos : 0 < ∑ v, wP v) : ∑ v, wR wP v = 1 := by
  have hS : (0 : ℝ) < ∑ v, (wP v : ℝ) := by exact_mod_cast hpos
  unfold wR; rw [← sum_div, div_self hS.ne']

/-- **The inner region on the machine.** With the last heavy level `ls` in `r180` and the thin
level `ls - ⌊√n⌋ + j₀` (`j₀ = r204`), the program `innerStep` computes the tree `T₁` of an inner
region at the level `l₀ = ls - ⌊√n⌋ + j₀` if `⌊√n⌋ < ls` (by `iprog`, the level `l₀` being heavy
as `ls` is), and keeps `T₁ = T` at the level `l₀ = 0` otherwise (`inner_univ`). The parent darts
of `T₁` are at `bPr`. -/
theorem innerStep_exec (hS : Setup M T₀ T k n cd A Tm V L fd w vi wP fdD)
    (htri : ∀ δ : D, M.IsTriangle δ)
    (hlay : 3 * k ≤ bPr ∧ bV + 3 * k ≤ bPr ∧ bPr + n ≤ bA ∧ bLv + n ≤ bA ∧
      bF + n ≤ bA ∧ bw + n ≤ bA ∧ bA + k ≤ bL ∧ bL + k ≤ bS ∧ bS + k ≤ bSum)
    (hW : bSum + 3 * k + 4 * n + 1 ≤ W ∧ 3 * ∑ v, wP v ≤ W) (hk : 0 < k)
    (hpos : 0 < ∑ v, wP v)
    (c : Config) (hc : WordsBounded W c) (hR : CR k bA bL bS 0 c)
    (hH : HR (c.nreg 160) n bV bLv bF bw bSum c) (h168 : c.nreg 168 = ∑ v, wP v)
    (h215 : c.nreg 215 = bPr) (hm : InMem k n 0 bV bLv bF bw A V L fd w c.nmem)
    (hpar : ∀ v (h : v ≠ T.root), (cd (T.par v h) : ℕ) = c.nmem (bPr + vi v))
    {ls : ℕ} (h180 : c.nreg 180 = ls) (hls : ls < n) (hlsH : ls = 0 ∨ Heavy T (wR wP) ls)
    (h201 : c.nreg 201 = Nat.sqrt n) (hj₀ : c.nreg 204 ≤ Nat.sqrt n)
    (hth₀ : (Nat.sqrt n + 1) * #(T.lvl (ls - Nat.sqrt n + c.nreg 204)) ≤ n) :
    ∃ c' t, Exec P' W innerStep c c' t ∧ t ≤ 247 * k + 39 * n + 36 ∧
      (∃ (l₀ : ℕ) (H : Finset M.Face) (K₀ : Finset P) (c₀ : P) (T₁ : M.SpTree),
        Inner T (wR wP) l₀ H K₀ c₀ T₁ ∧ T₁.root = T.root ∧ l₀ ≤ ls ∧ ls ≤ l₀ + Nat.sqrt n ∧
        ((l₀ = 0 ∧ K₀ = {T.root}) ∨
          (1 ≤ l₀ ∧ K₀ ⊆ T.lvl l₀ ∧ (Nat.sqrt n + 1) * #(T.lvl l₀) ≤ n)) ∧
        ∀ v (h : v ≠ T₁.root), (cd (T₁.par v h) : ℕ) = c'.nmem (bPr + vi v)) ∧
      (∀ a, a < bPr ∨ (bPr + n ≤ a ∧ a < bA) ∨ bSum + k + 1 ≤ a → c'.nmem a = c.nmem a) ∧
      c'.output = c.output := by
  obtain ⟨l0, l0', l00, l3, l4, l5, l6, l7, l8⟩ := hlay
  set t := Nat.sqrt n
  have htn : t ≤ n := Nat.sqrt_le_self n
  by_cases hb : t < ls
  · have e₁ := Exec.subN (P := P') hc 160 180 201
    set c₁ : Config := { c with nreg := upd c.nreg 160 (c.nreg 180 - c.nreg 201) }
    have k₁ : ∀ r, r ≠ 160 → c₁.nreg r = c.nreg r := fun r hr => upd_other _ _ _ hr
    have q₁ : c₁.nreg 160 = ls - t := by
      show upd c.nreg 160 (c.nreg 180 - c.nreg 201) 160 = _; rw [upd_same, h180, h201]
    have e₂ := Exec.addN (P := P') e₁.wb_right 160 160 204
      (by rw [q₁, k₁ 204 (by omega)]; omega)
    set c₂ : Config := { c₁ with nreg := upd c₁.nreg 160 (c₁.nreg 160 + c₁.nreg 204) }
    have k₂ : ∀ r, r ≠ 160 → c₂.nreg r = c.nreg r := fun r hr =>
      (upd_other _ _ _ hr).trans (k₁ r hr)
    set l₀ := ls - t + c.nreg 204 with hl₀
    have q₂ : c₂.nreg 160 = l₀ := by
      show upd c₁.nreg 160 (c₁.nreg 160 + c₁.nreg 204) 160 = _; rw [upd_same, q₁, k₁ 204 (by omega)]
    have hw₂ := e₂.wb_right
    have eb : Exec P' W (block [.subN 160 180 201, .addN 160 160 204]) c c₂ 2 :=
      .seq e₁ (.seq e₂ (.skip hw₂))
    have hheavy : Heavy T (wR wP) l₀ := by
      rcases hlsH with h | h
      · omega
      · exact heavy_mono (wR_nonneg wP) (by omega) h
    obtain ⟨c₃, t₃, e₃, ht₃, ⟨H, K₀, c₀, T₁, hI, hK, hroot, -, hpar₃⟩, -, hm₃, ho₃⟩ :=
      iprog_inner (P' := P') (l := l₀) hS htri ⟨by omega, l0', l00, l3, l4, l5, l6, l7, l8⟩ hW
        hk (by omega) (by omega) hheavy c₂ hw₂ (hR.of fun r hr => k₂ r (by omega))
        ⟨q₂, (k₂ 161 (by omega)).trans hH.r161, (k₂ 162 (by omega)).trans hH.r162,
          (k₂ 163 (by omega)).trans hH.r163, (k₂ 164 (by omega)).trans hH.r164,
          (k₂ 165 (by omega)).trans hH.r165, (k₂ 166 (by omega)).trans hH.r166⟩
        ((k₂ 168 (by omega)).trans h168) ((k₂ 215 (by omega)).trans h215) hm hpar
    exact ⟨c₃, 2 + t₃ + 1, Exec.ifLtN_true (by rw [h201, h180]; exact hb) (Exec.seq eb e₃),
      by omega, ⟨l₀, H, K₀, c₀, T₁, hI, hroot, by omega, by omega,
        Or.inr ⟨by omega, hK, hth₀⟩, hpar₃⟩, hm₃, ho₃⟩
  · refine ⟨c, 0 + 2, Exec.ifLtN_false (by rw [h201, h180]; exact hb) (.skip hc), by omega,
      ⟨0, univ, {T.root}, T.root, T,
        inner_univ hS.plane hS.bfs (by rw [sum_wR hpos]; norm_num), rfl, by omega, by omega,
        Or.inl ⟨rfl, rfl⟩, hpar⟩, fun a _ => rfl, rfl⟩

/-- **The concentrated weights on the machine.** With `ls` in `r180` and `j₂` in `r210`, the
program `concStep` puts `l₂ = ls + 1 + j₂` in `r160` and, at `bWC`, the moved weights of a
concentration map at level `l₂`: by `cprog` if `l₂ < n`, and the weights themselves (the identity
being a concentration map above every vertex) otherwise. -/
theorem concStep_exec (hS : Setup M T₀ T k n cd A Tm V L fd w vi wP fdD)
    (hlay : 3 * k ≤ bA ∧ bV + 3 * k ≤ bA ∧ bLv + n ≤ bA ∧ bF + n ≤ bA ∧ bw + n ≤ bA ∧
      bA + k ≤ bL ∧ bL + k ≤ bS ∧ bS + k ≤ bSum ∧ bSum + k + 1 ≤ bRep ∧
      bRep + k + 1 ≤ bCN ∧ bCN + n ≤ bWC)
    (hW : bWC + 3 * k + 4 * n + 1 ≤ W ∧ 3 * ∑ v, wP v ≤ W)
    (c : Config) (hc : WordsBounded W c) (hR : CR k bA bL bS 0 c)
    (hH : HR (c.nreg 160) n bV bLv bF bw bSum c) (h168 : c.nreg 168 = ∑ v, wP v)
    (h188 : c.nreg 188 = bRep) (h189 : c.nreg 189 = bCN) (h190 : c.nreg 190 = bWC)
    (hm : InMem k n 0 bV bLv bF bw A V L fd w c.nmem)
    {ls : ℕ} (h180 : c.nreg 180 = ls) (hls : ls < n) (h210 : c.nreg 210 ≤ Nat.sqrt n) :
    ∃ c' t, Exec P' W concStep c c' t ∧ t ≤ 106 * k + 59 * n + 29 ∧
      c'.nreg 160 = ls + 1 + c.nreg 210 ∧
      (∃ cn : P → P, IsConc T (ls + 1 + c.nreg 210) cn ∧
        (∀ u, wcf cn (wR wP) u = (c'.nmem (bWC + vi u) : ℝ) / ∑ v, (wP v : ℝ)) ∧
        (ls + 1 + c.nreg 210 < n → ∀ v, c'.nmem (bCN + vi v) = vi (cn v))) ∧
      (∀ a, a < bA ∨ bWC + n ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := hlay
  have htn : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
  have e₁ := Exec.addN (P := P') hc 160 180 141 (by rw [h180, hR.r141]; omega)
  set c₁ : Config := { c with nreg := upd c.nreg 160 (c.nreg 180 + c.nreg 141) }
  have k₁ : ∀ r, r ≠ 160 → c₁.nreg r = c.nreg r := fun r hr => upd_other _ _ _ hr
  have q₁ : c₁.nreg 160 = ls + 1 := by
    show upd c.nreg 160 (c.nreg 180 + c.nreg 141) 160 = _; rw [upd_same, h180, hR.r141]
  have e₂ := Exec.addN (P := P') e₁.wb_right 160 160 210 (by rw [q₁, k₁ 210 (by omega)]; omega)
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg 160 (c₁.nreg 160 + c₁.nreg 210) }
  have k₂ : ∀ r, r ≠ 160 → c₂.nreg r = c.nreg r := fun r hr =>
    (upd_other _ _ _ hr).trans (k₁ r hr)
  set l₂ := ls + 1 + c.nreg 210 with hl₂
  have q₂ : c₂.nreg 160 = l₂ := by
    show upd c₁.nreg 160 (c₁.nreg 160 + c₁.nreg 210) 160 = _; rw [upd_same, q₁, k₁ 210 (by omega)]
  have hw₂ := e₂.wb_right
  have eb : Exec P' W (block [.addN 160 180 141, .addN 160 160 210]) c c₂ 2 :=
    .seq e₁ (.seq e₂ (.skip hw₂))
  have hR₂ : CR k bA bL bS 0 c₂ := hR.of fun r hr => k₂ r (by omega)
  have g161 : c₂.nreg 161 = n := (k₂ 161 (by omega)).trans hH.r161
  by_cases hb : l₂ < n
  · obtain ⟨c₃, t₃, e₃, ht₃, ⟨cn, hcn, hCN, hcf⟩, hr₃, hm₃, ho₃⟩ :=
      conc_exec (P' := P') hS ⟨by omega, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ hW hb c₂ hw₂
        hR₂ ⟨q₂, g161, (k₂ 162 (by omega)).trans hH.r162,
          (k₂ 163 (by omega)).trans hH.r163, (k₂ 164 (by omega)).trans hH.r164,
          (k₂ 165 (by omega)).trans hH.r165, (k₂ 166 (by omega)).trans hH.r166⟩
        ((k₂ 168 (by omega)).trans h168) ((k₂ 188 (by omega)).trans h188)
        ((k₂ 189 (by omega)).trans h189) ((k₂ 190 (by omega)).trans h190) hm
    exact ⟨c₃, 2 + (t₃ + 1), .seq eb (.ifLtN_true (by rw [q₂, g161]; exact hb) e₃), by omega,
      (hr₃ 160 (by omega)).trans q₂, ⟨cn, hcn, hcf, fun _ => hCN⟩, hm₃, ho₃⟩
  · obtain ⟨c₃, t₃, e₃, ht₃, hd₃, hm₃, ho₃⟩ := wcopy_exec (P := P') (n := n) (bw := bw)
      (bWC := bWC) (by omega) (by omega) c₂ hw₂ hR₂.r140 hR₂.r141 g161
      ((k₂ 165 (by omega)).trans hH.r165) ((k₂ 190 (by omega)).trans h190)
    have hcard : Fintype.card P = n := by rw [Fintype.card_congr vi, Fintype.card_fin]
    refine ⟨c₃, 2 + (t₃ + 2), .seq eb (.ifLtN_false (by rw [q₂, g161]; exact hb) e₃), by omega,
      (e₃.nreg_of_wr (by decide)).trans q₂,
      ⟨id, isConc_id fun v => ?_, fun u => ?_, fun h => absurd h hb⟩,
      fun a ha => hm₃ a (by omega), ho₃⟩
    · have := height_lt_card hS.bfs v; omega
    · rw [wcf_id, hd₃ _ (vi u).2, show c₂.nmem = c.nmem from rfl, hm.2.2.2.2 _ (vi u).2, hS.hw]
      rfl

end Glue

/-- The bases of the arrays of `millerA`. -/
structure ABase where
  bV : ℕ
  bLv : ℕ
  bPr : ℕ
  bMk : ℕ
  bQ : ℕ
  bHd : ℕ
  bNx : ℕ
  bF : ℕ
  bw : ℕ
  bA : ℕ
  bL : ℕ
  bS : ℕ
  bSum : ℕ
  bRep : ℕ
  bCN : ℕ
  bLC : ℕ
  bU : ℕ
  bWC : ℕ
  bD : ℕ
  bS8 : ℕ
  bD₂ : ℕ
  bS₂ : ℕ

/-- The layout: the reversals at `[0, 3k)`, the arrays of the cycle search in `[3k, 11k)`, and
the arrays of the Miller programs above, in this order. -/
structure ALay (b : ABase) (k n W : ℕ) : Prop where
  l1 : 11 * k ≤ b.bV
  l2 : b.bV + 3 * k ≤ b.bLv
  l3 : b.bLv + n ≤ b.bPr
  l4 : b.bPr + n ≤ b.bMk
  l5 : b.bMk + n ≤ b.bQ
  l6 : b.bQ + n ≤ b.bHd
  l7 : b.bHd + n ≤ b.bNx
  l8 : b.bNx + 3 * k ≤ b.bF
  l9 : b.bF + n ≤ b.bw
  l10 : b.bw + n ≤ b.bA
  l11 : b.bA + k ≤ b.bL
  l12 : b.bL + k ≤ b.bS
  l13 : b.bS + k ≤ b.bSum
  l14 : b.bSum + k + 1 ≤ b.bRep
  l15 : b.bRep + k + 1 ≤ b.bCN
  l16 : b.bCN + n ≤ b.bLC
  l17 : b.bLC + 2 * n + 1 ≤ b.bU
  l18 : b.bU + (Nat.log 2 n + 1) * n ≤ b.bWC
  l19 : b.bWC + n ≤ b.bD
  l20 : b.bD + n ≤ b.bS8
  l21 : b.bS8 + n ≤ b.bD₂
  l22 : b.bD₂ + n ≤ b.bS₂
  hW : b.bS₂ + 3 * k + 4 * n + 4 ≤ W

/-- The registers `millerA` starts from: the constants and the bases. -/
structure ARegs (b : ABase) (k n : ℕ) (c : Config) : Prop where
  cregs : CRegs k c
  r140 : c.nreg 140 = 0
  r141 : c.nreg 141 = 1
  r142 : c.nreg 142 = 3
  r143 : c.nreg 143 = k
  r144 : c.nreg 144 = b.bA
  r145 : c.nreg 145 = b.bL
  r146 : c.nreg 146 = b.bS
  r147 : c.nreg 147 = 0
  r161 : c.nreg 161 = n
  r162 : c.nreg 162 = b.bV
  r163 : c.nreg 163 = b.bLv
  r164 : c.nreg 164 = b.bF
  r165 : c.nreg 165 = b.bw
  r166 : c.nreg 166 = b.bSum
  r188 : c.nreg 188 = b.bRep
  r189 : c.nreg 189 = b.bCN
  r190 : c.nreg 190 = b.bWC
  r200 : c.nreg 200 = b.bLC
  r215 : c.nreg 215 = b.bPr
  r216 : c.nreg 216 = b.bMk
  r217 : c.nreg 217 = b.bQ
  r218 : c.nreg 218 = b.bHd
  r219 : c.nreg 219 = b.bNx
  r252 : c.nreg 252 = b.bS8
  r253 : c.nreg 253 = b.bD
  r254 : c.nreg 254 = b.bU
  r381 : c.nreg 381 = b.bD₂
  r382 : c.nreg 382 = b.bS₂


section Whole

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}

set_option maxHeartbeats 16000000 in
/-- **Steps 1–8 of Miller's separator on the machine.** For a coded triangulation (`A` the
reversals at `0`, `V` the vertex numbers at `bV`) with `k ≥ 2` triangles and `n` vertices,
natural weights `wP` of positive total at `bw`, the layout `ALay` and the registers `ARegs`, the
program `millerA` ends within `(231 log₂ n + 1134) k + (60 n + 152) log₂ n + 278 n + 637` steps
with:
* a breadth-first tree `T` from the vertex `0` and its levels at `bLv`;
* the last heavy level `ls < n` (in `r180`): no level above it is heavy;
* the tree `T₁` of an inner region at the level `l₀ ≤ ls ≤ l₀ + ⌊√n⌋` (`T₁ = T`, `l₀ = 0` and
  `K₀ = {T.root}`, or `l₀ ≥ 1` a thin level with `K₀` in it), its parent darts at `bPr`;
* a thin level `ls < l₂ ≤ ls + 1 + ⌊√n⌋` (in `r160`), a concentration map `cn` at `l₂` and its
  moved weights at `bWC`; the level `l₂` is light (`hlight` of `band_separator_of_dart`);
* a dart `δ` off `T₁` (in `r353`) whose strict inside and outside have moved weight at most
  `2/3` each (`hA`, `hB` of `band_separator_of_dart`). -/
theorem millerA_spec {k n : ℕ} {cd : D ≃ Fin (3 * k)} {vi : Q ≃ Fin n} {A V : ℕ → ℕ}
    (wP : Q → ℕ) {W : ℕ} {P : Input} {c : Config} {b : ABase}
    (hM : M.IsPlane) (hT3 : ∀ δ, M.IsTriangle δ) (hk2 : 2 ≤ k)
    (hAcd : ∀ x, A (cd x) = cd (M.α x)) (hφ : ∀ x, (cd (M.φ x) : ℕ) = phi3 (cd x))
    (hV : ∀ x, V (cd x) = vi (M.vert x)) (hpos : 0 < ∑ v, wP v)
    (hlay : ALay b k n W) (hWt : 11 * k + 3 * ∑ v, wP v + 4 ≤ W)
    (hc : WordsBounded W c) (hR : ARegs b k n c)
    (mA : ∀ x < 3 * k, c.nmem x = A x) (mV : ∀ x < 3 * k, c.nmem (b.bV + x) = V x)
    (mW : ∀ v, c.nmem (b.bw + vi v) = wP v) :
    ∃ c' t, Exec P W millerA c c' t ∧
      t ≤ (231 * Nat.log 2 n + 1134) * k + (60 * n + 152) * Nat.log 2 n + 278 * n + 637 ∧
      ∃ (T : M.SpTree) (ls l₀ l₂ : ℕ) (H : Finset M.Face) (K₀ : Finset Q) (c₀ : Q)
        (T₁ : M.SpTree) (cn : Q → Q) (δ : D),
        -- the breadth-first tree (step 1)
        (vi T.root : ℕ) = 0 ∧ IsBFS T ∧ (∀ v, c'.nmem (b.bLv + vi v) = T.height v) ∧
        -- the last heavy level (step 4)
        ls < n ∧ (ls = 0 ∨ Heavy T (wR wP) ls) ∧ (∀ l, ls < l → ¬ Heavy T (wR wP) l) ∧
        c'.nreg 180 = ls ∧
        -- the inner region at the thin level `l₀` (steps 5–6)
        Inner T (wR wP) l₀ H K₀ c₀ T₁ ∧ T₁.root = T.root ∧ l₀ ≤ ls ∧ ls ≤ l₀ + Nat.sqrt n ∧
        ((l₀ = 0 ∧ K₀ = {T.root}) ∨
          (1 ≤ l₀ ∧ K₀ ⊆ T.lvl l₀ ∧ (Nat.sqrt n + 1) * #(T.lvl l₀) ≤ n)) ∧
        (∀ v (h : v ≠ T₁.root), (cd (T₁.par v h) : ℕ) = c'.nmem (b.bPr + vi v)) ∧
        -- the concentration at the thin level `l₂` (steps 5, 7)
        ls < l₂ ∧ l₂ ≤ ls + 1 + Nat.sqrt n ∧ (Nat.sqrt n + 1) * #(T.lvl l₂) ≤ n ∧
        c'.nreg 160 = l₂ ∧ IsConc T l₂ cn ∧
        (∀ u, wcf cn (wR wP) u = (c'.nmem (b.bWC + vi u) : ℝ) / ∑ v, (wP v : ℝ)) ∧
        -- the hypothesis `hlight` of `band_separator_of_dart`
        (∀ f, f ∉ M.zone (T.low l₂) → ∑ v ∈ ins (M.comp (T.low l₂) f), wR wP v ≤ 2 / 3) ∧
        -- the dart of step 8 and the hypotheses `hδ`, `hA`, `hB` of `band_separator_of_dart`
        (cd δ : ℕ) = c'.nreg 353 ∧ ¬ T₁.IsTree δ ∧
        ∑ v ∈ T₁.inC δ, wcf cn (wR wP) v ≤ 2 / 3 ∧
        ∑ v ∈ T₁.outC δ, wcf cn (wR wP) v ≤ 2 / 3 ∧
        -- the arrays read by steps 9–10, and the memory above the arrays untouched
        (∀ x < 3 * k, c'.nmem x = A x) ∧ (∀ x < 3 * k, c'.nmem (b.bV + x) = V x) ∧
        (∀ v, c'.nmem (b.bw + vi v) = wP v) ∧
        (∃ fdD : Q → D, (∀ u, M.vert (fdD u) = u) ∧ ∀ u, c'.nmem (b.bF + vi u) = cd (fdD u)) ∧
        (∀ a, b.bS₂ + n ≤ a → c'.nmem a = c.nmem a) ∧
        -- the concentration map itself at `bCN` (if `l₂ < n`)
        (l₂ < n → ∀ v, c'.nmem (b.bCN + vi v) = vi (cn v)) := by
  classical
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19,
    l20, l21, l22, lW⟩ := hlay
  have hk : 0 < k := by omega
  have hn : 0 < n := by
    obtain ⟨d⟩ : Nonempty D := ⟨cd.symm ⟨0, by omega⟩⟩
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) (vi (M.vert d)).2
  have hAr : ∀ x < 3 * k, A x < 3 * k ∧ A (A x) = x := revOk_of cd hAcd
  -- 0. `r250 := bw`
  have e₀ := Exec.copyN (P := P) hc 250 165
  set c₀ : Config := { c with nreg := upd c.nreg 250 (c.nreg 165) }
  have hw₀ := e₀.wb_right
  have k₀ : ∀ r, r ≠ 250 → c₀.nreg r = c.nreg r := fun r hr => upd_other _ _ _ hr
  -- 1. the breadth-first search
  obtain ⟨c₁, t₁, e₁, ht₁, ⟨T, hroot, hbfs, hlv₁, hpar₁⟩, hr₁, hm₁, ho₁⟩ :=
    bprog_tree (P' := P) cd vi hM hn hAcd hV (bR := 0) (bV := b.bV) (bLv := b.bLv) (bPr := b.bPr)
      (bMk := b.bMk) (bQ := b.bQ) (bHd := b.bHd) (bNx := b.bNx) ⟨by omega, by omega, l3, l4, l5,
      l6, l7⟩ (by omega) c₀ hw₀ ((k₀ 140 (by omega)).trans hR.r140)
      ((k₀ 141 (by omega)).trans hR.r141) ((k₀ 142 (by omega)).trans hR.r142)
      ((k₀ 143 (by omega)).trans hR.r143) ((k₀ 147 (by omega)).trans hR.r147)
      ((k₀ 161 (by omega)).trans hR.r161) ((k₀ 162 (by omega)).trans hR.r162)
      ((k₀ 163 (by omega)).trans hR.r163) ((k₀ 215 (by omega)).trans hR.r215)
      ((k₀ 216 (by omega)).trans hR.r216) ((k₀ 217 (by omega)).trans hR.r217)
      ((k₀ 218 (by omega)).trans hR.r218) ((k₀ 219 (by omega)).trans hR.r219)
      (fun x hx => by rw [zero_add]; exact mA x hx) (fun x hx => mV x hx)
  have hw₁ := e₁.wb_right
  have g₁ : ∀ r, (r < 220 ∨ 230 ≤ r) → r ≠ 250 → c₁.nreg r = c.nreg r := fun r a b' =>
    (hr₁ r a).trans (k₀ r b')
  -- 2. a dart at every vertex
  have gV : ∀ x < 3 * k, V x < n := vlt_of cd vi hV
  obtain ⟨c₂, t₂, e₂, ht₂, hF₂, hr₂, hm₂, ho₂⟩ := dpass_exec (P := P) (k := k) (n := n)
    (bV := b.bV) (bF := b.bF) (V := V) (by omega) (by omega) c₁ hw₁
    ((g₁ 140 (by omega) (by omega)).trans hR.r140) ((g₁ 141 (by omega) (by omega)).trans hR.r141)
    ((g₁ 142 (by omega) (by omega)).trans hR.r142) ((g₁ 143 (by omega) (by omega)).trans hR.r143)
    ((g₁ 162 (by omega) (by omega)).trans hR.r162) ((g₁ 164 (by omega) (by omega)).trans hR.r164)
    (fun x hx => ⟨by rw [hm₁ _ (by omega)]; exact mV x hx, gV x hx⟩)
  obtain ⟨fdD, hfdD, hfd⟩ := dpass_dart cd vi hM hV (F := fun u => c₂.nmem (b.bF + u)) hF₂
  have hw₂ := e₂.wb_right
  have g₂ : ∀ r, (r < 211 ∨ 215 ≤ r) → (r < 220 ∨ 230 ≤ r) → r ≠ 250 → c₂.nreg r = c.nreg r :=
    fun r a b' d => (hr₂ r a).trans (g₁ r b' d)
  have m₂ : ∀ a, (a < b.bLv ∨ (b.bLv + n ≤ a ∧ a < b.bPr) ∨ b.bNx + 3 * k ≤ a) →
      (a < b.bF ∨ b.bF + n ≤ a) → c₂.nmem a = c.nmem a := fun a h1 h2 => by
    rw [hm₂ a h2, hm₁ a h1]
  -- 3. the total weight
  set w : ℕ → ℕ := fun u => c.nmem (b.bw + u)
  have hw : ∀ v, w (vi v) = wP v := mW
  have hsum := sum_range_ofvi vi hw
  have htot : ∀ X : Finset Q, ∑ v ∈ X, wP v ≤ W := fun X =>
    (sum_le_sum_of_subset (subset_univ X)).trans (by omega)
  obtain ⟨c₃, t₃, e₃, ht₃, h320, hr₃, hm₃, ho₃⟩ := wsum_exec (P := P) (n := n) (bW := b.bw) (w := w)
    (by omega) (by rw [hsum]; exact htot _) c₂ hw₂
    ((g₂ 140 (by omega) (by omega) (by omega)).trans hR.r140)
    ((g₂ 141 (by omega) (by omega) (by omega)).trans hR.r141)
    ((g₂ 161 (by omega) (by omega) (by omega)).trans hR.r161)
    (by rw [hr₂ 250 (by omega), hr₁ 250 (by omega)]; exact hR.r165)
    (fun u hu => m₂ _ (Or.inr (Or.inr (by omega))) (Or.inr (by omega)))
  rw [hsum] at h320
  have hw₃ := e₃.wb_right
  have e₄ := Exec.copyN (P := P) hw₃ 168 320
  set c₄ : Config := { c₃ with nreg := upd c₃.nreg 168 (c₃.nreg 320) }
  have hw₄ := e₄.wb_right
  have g₄ : ∀ r, r ≠ 168 → r ≠ 320 → r ≠ 365 → r ≠ 366 → r ≠ 367 → (r < 211 ∨ 215 ≤ r) →
      (r < 220 ∨ 230 ≤ r) → r ≠ 250 → c₄.nreg r = c.nreg r := fun r a b' d e f' g' h' i' => by
    show upd c₃.nreg 168 (c₃.nreg 320) r = c.nreg r
    rw [upd_other _ _ _ a, hr₃ r b' d e f']; exact g₂ r g' h' i'
  have m₄ : ∀ a, (a < b.bLv ∨ (b.bLv + n ≤ a ∧ a < b.bPr) ∨ b.bNx + 3 * k ≤ a) →
      (a < b.bF ∨ b.bF + n ≤ a) → c₄.nmem a = c.nmem a := fun a h1 h2 => by
    show c₃.nmem a = _; rw [hm₃]; exact m₂ a h1 h2
  have h168 : c₄.nreg 168 = ∑ v, wP v := by show upd c₃.nreg 168 (c₃.nreg 320) 168 = _; simp [h320]
  -- the data of the heavy test
  set Pr : ℕ → ℕ := fun u => c₁.nmem (b.bPr + u)
  have hPrT : ∀ v (h : v ≠ T.root), Pr (vi v) = cd (T.par v h) := fun v h => (hpar₁ v h).symm
  set L : ℕ → ℕ := fun u => c₁.nmem (b.bLv + u)
  set fd : ℕ → ℕ := fun u => c₂.nmem (b.bF + u)
  have hC₀ := coded_of_tmark (k := k) (cd := cd) (vi := vi) (A := A) (Pr := Pr) hAcd hφ hPrT
  have hS : Setup M T T k n cd A (tmark A Pr (vi T.root) n) V L fd w vi wP fdD :=
    ⟨hM, hbfs, fun d => (hT3 d).φ_three, hC₀, hV, hlv₁, hfdD, hfd, hw⟩
  have hm₄ : InMem k n 0 b.bV b.bLv b.bF b.bw A V L fd w c₄.nmem := by
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
    · rw [zero_add, m₄ _ (Or.inl (by omega)) (Or.inl (by omega))]; exact mA x hx
    · rw [m₄ _ (Or.inl (by omega)) (Or.inl (by omega))]; exact mV x hx
    · show c₃.nmem _ = _; rw [hm₃, hm₂ _ (Or.inl (by omega))]
    · show c₃.nmem _ = _; rw [hm₃]
    · rw [m₄ _ (Or.inr (Or.inr (by omega))) (Or.inr (by omega))]
  have hCR₄ : CR k b.bA b.bL b.bS 0 c₄ :=
    ⟨(g₄ 140 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans hR.r140,
    (g₄ 141 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans hR.r141,
    (g₄ 142 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans hR.r142,
    (g₄ 143 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans hR.r143,
    (g₄ 144 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans hR.r144,
    (g₄ 145 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans hR.r145,
    (g₄ 146 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans hR.r146,
    (g₄ 147 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans hR.r147⟩
  have gg : ∀ r, 160 < r → r < 167 → c₄.nreg r = c.nreg r := fun r a b' =>
    g₄ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hHR₄ : HR (c₄.nreg 160) n b.bV b.bLv b.bF b.bw b.bSum c₄ :=
    ⟨rfl, (gg 161 (by omega) (by omega)).trans hR.r161,
      (gg 162 (by omega) (by omega)).trans hR.r162,
      (gg 163 (by omega) (by omega)).trans hR.r163, (gg 164 (by omega) (by omega)).trans hR.r164,
      (gg 165 (by omega) (by omega)).trans hR.r165, (gg 166 (by omega) (by omega)).trans hR.r166⟩
  -- 4. the last heavy level
  obtain ⟨c₅, t₅, e₅, ht₅, hls, hlsH, hlsN, ho₅, hCR₅, h168₅, hm₅, hf₅⟩ :=
    bsearch_exec' (P' := P) hS hn ⟨by omega, by omega, by omega, by omega, by omega, l11, l12, l13⟩
      ⟨by omega, by have := htot univ; omega⟩ c₄ hw₄ hCR₄ hHR₄ h168 hm₄
  have hw₅ := e₅.wb_right
  set ls := c₅.nreg 180
  -- 5. the thin levels
  obtain ⟨c₆, t₆, e₆, ht₆, h201, hj₂, hth₂, hj₀, hth₀, hr₆, hm₆, ho₆⟩ := thin_exec (P' := P) vi
    (L := L) hlv₁ hbfs (bLv := b.bLv) (bLC := b.bLC) (by omega) (by omega) c₅ hw₅
    (hCR₅.r140) (hCR₅.r141)
    ((e₅.nreg_of_wr (by decide)).trans (hHR₄.r161))
    ((e₅.nreg_of_wr (by decide)).trans (hHR₄.r163))
    ((e₅.nreg_of_wr (by decide)).trans ((g₄ 200 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)).trans hR.r200)) rfl hls
    (fun v hv => hm₅.2.2.1 v hv)
  have hw₆ := e₆.wb_right
  have k180 : c₆.nreg 180 = ls := hr₆ 180 (by omega)
  have htn : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
  -- the registers kept from the start
  have G₆ : ∀ r, (bsearch.wr r = false ∧ thin.wr r = false) →
      (r ≠ 168 ∧ r ≠ 320 ∧ r ≠ 365 ∧ r ≠ 366 ∧ r ≠ 367 ∧ (r < 211 ∨ 215 ≤ r) ∧
        (r < 220 ∨ 230 ≤ r) ∧ r ≠ 250) → c₆.nreg r = c.nreg r :=
    fun r ⟨a, b'⟩ ⟨d, e, f', g', h', i', j', l'⟩ =>
      (e₆.nreg_of_wr b').trans ((e₅.nreg_of_wr a).trans (g₄ r d e f' g' h' i' j' l'))
  have low : ∀ r < 11, bsearch.wr r = false ∧ thin.wr r = false ∧ innerStep.wr r = false ∧
      concStep.wr r = false := by decide
  -- 6. the inner region
  have hCR₆ : CR k b.bA b.bL b.bS 0 c₆ :=
    ⟨(hr₆ 140 (by omega)).trans hCR₅.r140, (hr₆ 141 (by omega)).trans hCR₅.r141,
      (hr₆ 142 (by omega)).trans hCR₅.r142, (hr₆ 143 (by omega)).trans hCR₅.r143,
      (hr₆ 144 (by omega)).trans hCR₅.r144, (hr₆ 145 (by omega)).trans hCR₅.r145,
      (hr₆ 146 (by omega)).trans hCR₅.r146, (hr₆ 147 (by omega)).trans hCR₅.r147⟩
  have hHR₆ : HR (c₆.nreg 160) n b.bV b.bLv b.bF b.bw b.bSum c₆ :=
    ⟨rfl, (G₆ 161 (by decide) (by decide)).trans hR.r161,
      (G₆ 162 (by decide) (by decide)).trans hR.r162,
      (G₆ 163 (by decide) (by decide)).trans hR.r163,
      (G₆ 164 (by decide) (by decide)).trans hR.r164,
      (G₆ 165 (by decide) (by decide)).trans hR.r165,
      (G₆ 166 (by decide) (by decide)).trans hR.r166⟩
  have h168₆ : c₆.nreg 168 = ∑ v, wP v := (hr₆ 168 (by omega)).trans h168₅
  have h215₆ : c₆.nreg 215 = b.bPr := (G₆ 215 (by decide) (by decide)).trans hR.r215
  have hm₆' : InMem k n 0 b.bV b.bLv b.bF b.bw A V L fd w c₆.nmem :=
    inMem_of hm₅ fun a ha => hm₆ a (Or.inl (by omega))
  have hpar₆ : ∀ v (h : v ≠ T.root), (cd (T.par v h) : ℕ) = c₆.nmem (b.bPr + vi v) :=
    fun v h => by
      have := (vi v).2
      rw [hm₆ _ (Or.inl (by omega)), hf₅ _ (Or.inl (by omega)),
        show c₄.nmem = c₃.nmem from rfl, hm₃, hm₂ _ (Or.inl (by omega))]
      exact hpar₁ v h
  obtain ⟨c₇, t₇, e₇, ht₇, ⟨l₀, H, K₀, c₀, T₁, hI, hroot₁, hl₀a, hl₀b, hK₀, hpar₇⟩, hm₇, ho₇⟩ :=
    innerStep_exec (P' := P) hS hT3 ⟨by omega, by omega, by omega, by omega, by omega, by omega,
      l11, l12, l13⟩ ⟨by omega, by omega⟩ hk hpos c₆ hw₆ hCR₆ hHR₆ h168₆ h215₆ hm₆' hpar₆ k180
      hls hlsH h201 hj₀ hth₀
  have hw₇ := e₇.wb_right
  have G₇ : ∀ r, (bsearch.wr r = false ∧ thin.wr r = false ∧ innerStep.wr r = false) →
      (r ≠ 168 ∧ r ≠ 320 ∧ r ≠ 365 ∧ r ≠ 366 ∧ r ≠ 367 ∧ (r < 211 ∨ 215 ≤ r) ∧
        (r < 220 ∨ 230 ≤ r) ∧ r ≠ 250) → c₇.nreg r = c.nreg r :=
    fun r ⟨a, b', d⟩ h => (e₇.nreg_of_wr d).trans (G₆ r ⟨a, b'⟩ h)
  have hCR₇ : CR k b.bA b.bL b.bS 0 c₇ :=
    ⟨(G₇ 140 (by decide) (by decide)).trans hR.r140,
      (G₇ 141 (by decide) (by decide)).trans hR.r141,
      (G₇ 142 (by decide) (by decide)).trans hR.r142,
      (G₇ 143 (by decide) (by decide)).trans hR.r143,
      (G₇ 144 (by decide) (by decide)).trans hR.r144,
      (G₇ 145 (by decide) (by decide)).trans hR.r145,
      (G₇ 146 (by decide) (by decide)).trans hR.r146,
      (G₇ 147 (by decide) (by decide)).trans hR.r147⟩
  have hHR₇ : HR (c₇.nreg 160) n b.bV b.bLv b.bF b.bw b.bSum c₇ :=
    ⟨rfl, (G₇ 161 (by decide) (by decide)).trans hR.r161,
      (G₇ 162 (by decide) (by decide)).trans hR.r162,
      (G₇ 163 (by decide) (by decide)).trans hR.r163,
      (G₇ 164 (by decide) (by decide)).trans hR.r164,
      (G₇ 165 (by decide) (by decide)).trans hR.r165,
      (G₇ 166 (by decide) (by decide)).trans hR.r166⟩
  have h168₇ : c₇.nreg 168 = ∑ v, wP v := (e₇.nreg_of_wr (by decide)).trans h168₆
  have h180₇ : c₇.nreg 180 = ls := (e₇.nreg_of_wr (by decide)).trans k180
  have k210 : c₇.nreg 210 = c₆.nreg 210 := e₇.nreg_of_wr (by decide)
  have hm₇' : InMem k n 0 b.bV b.bLv b.bF b.bw A V L fd w c₇.nmem :=
    inMem_of hm₆' fun a ha => hm₇ a (by omega)
  -- 7. the concentration
  obtain ⟨c₈, t₈, e₈, ht₈, h160₈, ⟨cn, hcn, hcf, hCN⟩, hm₈, ho₈⟩ :=
    concStep_exec (P' := P) hS ⟨by omega, by omega, by omega, by omega, by omega, l11, l12, l13,
      l14, l15, by omega⟩ ⟨by omega, by omega⟩ c₇ hw₇ hCR₇ hHR₇ h168₇
      ((G₇ 188 (by decide) (by decide)).trans hR.r188)
      ((G₇ 189 (by decide) (by decide)).trans hR.r189)
      ((G₇ 190 (by decide) (by decide)).trans hR.r190) hm₇' h180₇ hls (k210 ▸ hj₂)
  rw [k210] at h160₈ hcn hCN
  have hw₈ := e₈.wb_right
  have G₈ : ∀ r, (bsearch.wr r = false ∧ thin.wr r = false ∧ innerStep.wr r = false ∧
      concStep.wr r = false) →
      (r ≠ 168 ∧ r ≠ 320 ∧ r ≠ 365 ∧ r ≠ 366 ∧ r ≠ 367 ∧ (r < 211 ∨ 215 ≤ r) ∧
        (r < 220 ∨ 230 ≤ r) ∧ r ≠ 250) → c₈.nreg r = c.nreg r :=
    fun r ⟨a, b', d, d'⟩ h => (e₈.nreg_of_wr d').trans (G₇ r ⟨a, b', d⟩ h)
  have M8 : ∀ a, a < b.bLv → c₈.nmem a = c.nmem a := fun a ha => by
    rw [hm₈ a (Or.inl (by omega)), hm₇ a (Or.inl (by omega)), hm₆ a (Or.inl (by omega)),
      hf₅ a (Or.inl (by omega)), m₄ a (Or.inl ha) (Or.inl (by omega))]
  -- the registers of step 8
  have e₉a := Exec.copyN (P := P) hw₈ 250 190
  set c₉a : Config := { c₈ with nreg := upd c₈.nreg 250 (c₈.nreg 190) }
  have e₉b := Exec.copyN (P := P) e₉a.wb_right 255 140
  set c₉ : Config := { c₉a with nreg := upd c₉a.nreg 255 (c₉a.nreg 140) }
  have hw₉ := e₉b.wb_right
  have e₉ : Exec P W (block [.copyN 250 190, .copyN 255 140]) c₈ c₉ 2 :=
    .seq e₉a (.seq e₉b (.skip hw₉))
  have k₉ : ∀ r, r ≠ 250 → r ≠ 255 → c₉.nreg r = c₈.nreg r := fun r a b' =>
    (upd_other _ _ _ b').trans (upd_other _ _ _ a)
  have q250 : c₉.nreg 250 = b.bWC := by
    show upd c₉a.nreg 255 (c₉a.nreg 140) 250 = _
    rw [upd_other _ _ _ (by omega)]
    show upd c₈.nreg 250 (c₈.nreg 190) 250 = _
    rw [upd_same, G₈ 190 (by decide) (by decide)]; exact hR.r190
  have q255 : c₉.nreg 255 = vi T₁.root := by
    show upd c₉a.nreg 255 (c₉a.nreg 140) 255 = _
    rw [upd_same]
    show upd c₈.nreg 250 (c₈.nreg 190) 140 = _
    rw [upd_other _ _ _ (by omega), G₈ 140 (by decide) (by decide), hR.r140, hroot₁, hroot]
    simp
  have G₉ : ∀ r, (bsearch.wr r = false ∧ thin.wr r = false ∧ innerStep.wr r = false ∧
      concStep.wr r = false) →
      (r ≠ 168 ∧ r ≠ 320 ∧ r ≠ 365 ∧ r ≠ 366 ∧ r ≠ 367 ∧ (r < 211 ∨ 215 ≤ r) ∧
        (r < 220 ∨ 230 ≤ r) ∧ r ≠ 250 ∧ r ≠ 255) → c₉.nreg r = c.nreg r :=
    fun r h ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ =>
      (k₉ r a8 a9).trans (G₈ r h ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩)
  have hCRegs₉ : CRegs k c₉ := cregs_of hR.cregs fun r hr =>
    G₉ r (low r (by omega)) ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega⟩
  have hPr₉ : ∀ v (h : v ≠ T₁.root), c₉.nmem (b.bPr + vi v) = cd (T₁.par v h) := fun v h => by
    have := (vi v).2
    rw [show c₉.nmem = c₈.nmem from rfl, hm₈ _ (Or.inl (by omega))]
    exact (hpar₇ v h).symm
  -- 8. step 8
  obtain ⟨c', t₁₀, e₁₀, ht₁₀, hfr, hlo, δ, hδ, hnt, hA, hB⟩ :=
    step8run_conc (P := P) (c := c₉) (T₁ := T₁) (cn := cn) (bV := b.bV) (bPr := b.bPr) (bU := b.bU)
      (bWC := b.bWC) (bD := b.bD) (bS := b.bS8) (bD₂ := b.bD₂) (bS₂ := b.bS₂) hM hT3 hk2 hAcd
      hφ hV hcf hpos ⟨l1, by omega, by omega, l18, l19, l20, l21, l22, by omega⟩ hWt hw₉ hCRegs₉
      ((G₉ 140 (by decide) (by decide)).trans hR.r140)
      ((G₉ 141 (by decide) (by decide)).trans hR.r141)
      ((G₉ 147 (by decide) (by decide)).trans hR.r147)
      ((G₉ 161 (by decide) (by decide)).trans hR.r161)
      ((G₉ 162 (by decide) (by decide)).trans hR.r162)
      ((G₉ 215 (by decide) (by decide)).trans hR.r215) q250
      ((G₉ 252 (by decide) (by decide)).trans hR.r252)
      ((G₉ 253 (by decide) (by decide)).trans hR.r253)
      ((G₉ 254 (by decide) (by decide)).trans hR.r254) q255
      ((G₉ 381 (by decide) (by decide)).trans hR.r381)
      ((G₉ 382 (by decide) (by decide)).trans hR.r382)
      (fun x hx => (M8 x (by omega)).trans (mA x hx))
      (fun x hx => (M8 _ (by omega)).trans (mV x hx)) hPr₉
  -- the whole program
  have eA : Exec P W millerA c c' _ :=
    .seq (.seq e₀ (.seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇
      (.seq e₈ e₉))))))))) e₁₀
  have hcl : Nat.clog 2 n ≤ Nat.log 2 n + 1 :=
    Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by norm_num) n).le
  have h5' : t₅ ≤ (106 * k + 21 * n + 30) * (Nat.log 2 n + 1) + 5 :=
    ht₅.trans (by gcongr)
  refine ⟨c', _, eA, by nlinarith, T, ls, l₀, ls + 1 + c₆.nreg 210, H, K₀, c₀, T₁, cn, δ,
    by rw [hroot]; simp, hbfs, fun v => ?_, hls, hlsH, hlsN, ?_, hI, hroot₁, hl₀a, hl₀b, hK₀,
    fun v h => ?_, by omega, by omega, hth₂, ?_, hcn, fun u => ?_,
    fun f hf => le_of_not_gt fun h => hlsN _ (by omega) ⟨f, hf, h⟩, hδ, hnt, hA, hB, hlo,
    fun x hx => ?_, fun v => ?_, ⟨fdD, hfdD, fun u => ?_⟩, fun a ha => ?_, fun hl v => ?_⟩
  · have := (vi v).2
    rw [hfr _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
      show c₉.nmem = c₈.nmem from rfl, hm₈ _ (Or.inl (by omega)), hm₇ _ (Or.inl (by omega)),
      hm₆ _ (Or.inl (by omega)), hm₅.2.2.1 _ this]
    exact hlv₁ v
  · rw [e₁₀.nreg_of_wr (by decide), k₉ 180 (by omega) (by omega), e₈.nreg_of_wr (by decide),
      h180₇]
  · have := (vi v).2
    rw [hfr _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
      show c₉.nmem = c₈.nmem from rfl, hm₈ _ (Or.inl (by omega))]
    exact hpar₇ v h
  · rw [e₁₀.nreg_of_wr (by decide), k₉ 160 (by omega) (by omega), h160₈]
  · have := (vi u).2
    rw [hfr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))]
    exact hcf u
  · rw [hfr _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
      show c₉.nmem = c₈.nmem from rfl, hm₈ _ (Or.inl (by omega))]
    exact hm₇'.2.1 x hx
  · have := (vi v).2
    rw [hfr _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
      show c₉.nmem = c₈.nmem from rfl, hm₈ _ (Or.inl (by omega)), hm₇'.2.2.2.2 _ this]
    exact mW v
  · have := (vi u).2
    rw [hfr _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
      show c₉.nmem = c₈.nmem from rfl, hm₈ _ (Or.inl (by omega)), hm₇'.2.2.2.1 _ this]
    exact hfd u
  · rw [hfr a (by omega) (Or.inr (by omega)) (Or.inr ha), show c₉.nmem = c₈.nmem from rfl,
      hm₈ a (Or.inr (by omega)), hm₇ a (Or.inr (Or.inr (by omega))), hm₆ a (Or.inr (by omega)),
      hf₅ a (Or.inr (by omega)), m₄ a (Or.inr (Or.inr (by omega))) (Or.inr (by omega))]
  · have := (vi v).2
    rw [hfr _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
      show c₉.nmem = c₈.nmem from rfl]
    exact hCN hl v

/-- **Steps 1–8 and the band theorem.** The output of `millerA` meets the hypotheses of
`PlanarSeparator.Map.band_separator_of_dart`: for the weights `wP v / Σ wP` there is a simple
cycle separator with at most `2 (l₂ - l₀) + #K₀ + #(T.lvl l₂)` darts, where the levels
`l₀ < l₂` are at most `2 ⌊√n⌋ + 1` apart, the level `l₂` has at most `n / (⌊√n⌋ + 1)` vertices,
and `K₀` is the root (`l₀ = 0`) or a set of vertices of the level `l₀`, which has at most
`n / (⌊√n⌋ + 1)` vertices. -/
theorem millerA_band {k n : ℕ} {cd : D ≃ Fin (3 * k)} {vi : Q ≃ Fin n} {A V : ℕ → ℕ}
    (wP : Q → ℕ) {W : ℕ} {P : Input} {c : Config} {b : ABase}
    (hM : M.IsPlane) (hT3 : ∀ δ, M.IsTriangle δ) (hk2 : 2 ≤ k)
    (hAcd : ∀ x, A (cd x) = cd (M.α x)) (hφ : ∀ x, (cd (M.φ x) : ℕ) = phi3 (cd x))
    (hV : ∀ x, V (cd x) = vi (M.vert x)) (hpos : 0 < ∑ v, wP v)
    (hlay : ALay b k n W) (hWt : 11 * k + 3 * ∑ v, wP v + 4 ≤ W)
    (hc : WordsBounded W c) (hR : ARegs b k n c)
    (mA : ∀ x < 3 * k, c.nmem x = A x) (mV : ∀ x < 3 * k, c.nmem (b.bV + x) = V x)
    (mW : ∀ v, c.nmem (b.bw + vi v) = wP v) :
    ∃ c' t, Exec P W millerA c c' t ∧
      t ≤ (231 * Nat.log 2 n + 1134) * k + (60 * n + 152) * Nat.log 2 n + 278 * n + 637 ∧
      ∃ (T : M.SpTree) (l₀ l₂ : ℕ) (K₀ : Finset Q), l₀ < l₂ ∧ l₂ ≤ l₀ + 2 * Nat.sqrt n + 1 ∧
        (Nat.sqrt n + 1) * #(T.lvl l₂) ≤ n ∧
        ((l₀ = 0 ∧ K₀ = {T.root}) ∨
          (1 ≤ l₀ ∧ K₀ ⊆ T.lvl l₀ ∧ (Nat.sqrt n + 1) * #(T.lvl l₀) ≤ n)) ∧
        ∃ (C : M.SCycle) (Z : Finset M.Face), C.k ≤ 2 * (l₂ - l₀) + #K₀ + #(T.lvl l₂) ∧
          IsCycleSep C Z (sideIn C Z) (sideOut C Z) ∧
          ∑ v ∈ sideIn C Z, wR wP v ≤ 2 / 3 ∧ ∑ v ∈ sideOut C Z, wR wP v ≤ 2 / 3 := by
  obtain ⟨c', t, e, ht, T, ls, l₀, l₂, H, K₀, c₀, T₁, cn, δ, -, hbfs, -, -, -, -, -, hI, -, ha,
    hb, hK, -, h1, h2, h3, -, hcn, -, hlight, -, hδ, hA, hB, -⟩ :=
    millerA_spec wP hM hT3 hk2 hAcd hφ hV hpos hlay hWt hc hR mA mV mW
  exact ⟨c', t, e, ht, T, l₀, l₂, K₀, by omega, by omega, h3, hK,
    band_separator_of_dart hM hT3 hbfs (wR_nonneg wP) (sum_wR hpos).le hI (by omega) hcn hδ hA hB
      hlight⟩

end Whole

end MillerProg

end PlanarSeparator
