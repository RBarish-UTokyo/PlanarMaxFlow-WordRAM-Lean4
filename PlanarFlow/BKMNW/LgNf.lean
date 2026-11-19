module

public import PlanarFlow.BKMNW.LgS5E

/-!
# The large-piece separator, stage 6: the flags of the attached darts `pcNf`

`pcertD` answers `(pcNf M Q P Hs, ρ, liftI …)`, and the split `splitD` uses only `pcNf`, the
path `ρ` and the classes `clsF M P (pcNf …) Hs K ρ` (`splitOf` ignores the items): the lift
`liftI` of the items (`liProg`) is **not** needed by the separator program. Stage 6 writes the
flags `NF2[i] = bf (g i ∈ pcNf M Q P Hs)` on the record's enumeration `g`:

* `g i ∉ pcNf ↔` `g i` is inside a hole (`0 < HP[i] = HP[RP[i]]`, `inner_iff_hlab`) whose label
  no dart of the core's piece map `B` has on its tail (`TT[HP[i]] = 0` for the table
  `TT[h] = Σ_{j : HP[j] = h} CF[j]`, `CF` the flags of `B`);
* `nfv` (branch-free, no products), `nfv_eq`, **`mem_pcNf_iff_tt`** (pure);
* `nf0` (registers from `3100 = R`, `3102 = k`, `3111 = Y`), `vbNFa`, `vbNFb`, `vbNF`,
  `nfSA`, **`nfProg = nf0 ; cfScan ; zfill ; nfSA ; saProg ; nfScan`**;
* **`nfProg_exec`** / **`nfProg_rec`**: within `70 n + 7 k + 40` steps, `NF2` at `Y + n + k + 1`.
  Scratch `[Y, Y + 2n + k + 1)`; memory outside it, registers outside `nfW` kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.tacticAnalysis.rwaSuggestion false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-! ### The value and its meaning -/

/-- `bf (¬ (0 < h ∧ h = hr ∧ t = 0))`, branch-free without products. -/
def nfv (h hr t : ℕ) : ℕ :=
  1 - (1 - (3 - ((1 - (1 - h)) + (1 - ((h - hr) + (hr - h))) + (1 - t))))

lemma nfv_eq (h hr t : ℕ) : nfv h hr t = bf (¬ (0 < h ∧ h = hr ∧ t = 0)) := by
  unfold nfv bf
  split_ifs with hc <;> omega

/-- With pairwise disjoint holes, a vertex in a hole is related to `a` iff `a` has its label. -/
lemma hRel_iff_hlab_of_pos {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {a v : V}
    (hv : 0 < hlab Hs v) : HRel Hs a v ↔ hlab Hs a = hlab Hs v := by
  constructor
  · rintro (rfl | ⟨H, hH, ha, hv'⟩)
    · rfl
    · exact hlab_congr (sm_mem_iff_of_pw hd hH ha hv')
  · intro he
    obtain ⟨hlt, hm⟩ := hlab_mem hv
    have ha : 0 < hlab Hs a := he ▸ hv
    obtain ⟨-, hm'⟩ := hlab_mem ha
    rw [he] at hm'
    exact Or.inr ⟨_, sm_getD_mem hlt, hm', hm⟩

/-- **The attached darts through the table of the core's hole labels.** -/
theorem mem_pcNf_iff_tt {Q : Finset V} {P : Finset D} {Hs : List (Finset V)}
    (hd : Hs.Pairwise Disjoint) {n : ℕ} {g : ℕ → D} (hgm : ∀ i < n, g i ∈ P)
    (hgs : ∀ y ∈ P, ∃ i < n, g i = y) {rp hp cf : ℕ → ℕ}
    (hrp : ∀ i < n, rp i < n ∧ g (rp i) = M.rev (g i))
    (hhp : ∀ i < n, hp i = hlab Hs (M.tail (g i)))
    (hcf : ∀ i < n, cf i = bf (g i ∈ pdarts M (core M Q P) Hs)) {i : ℕ} (hi : i < n) :
    g i ∈ pcNf M Q P Hs ↔ ¬ (0 < hp i ∧ hp i = hp (rp i) ∧ saF hp cf n (hp i) = 0) := by
  classical
  have hinner : Inner M Hs (g i) ↔ 0 < hp i ∧ hp i = hp (rp i) := by
    rw [inner_iff_hlab hd, hhp i hi, hhp _ (hrp i hi).1, (hrp i hi).2, CombMap.tail_rev]
  have hB : ∀ b ∈ pdarts M (core M Q P) Hs, b ∈ P := fun b hb =>
    (mem_core.1 (mem_pdarts.1 hb).1).1
  have htt : 0 < hp i → ((∀ b ∈ pdarts M (core M Q P) Hs, ¬ HRel Hs (M.tail b) (M.tail (g i))) ↔
      saF hp cf n (hp i) = 0) := fun hpos => by
    rw [hhp i hi] at hpos ⊢
    unfold saF
    rw [sum_eq_zero_iff]
    constructor
    · intro h j hj
      obtain ⟨hjn, hjl⟩ := mem_filter.1 hj
      have hjn' := mem_range.1 hjn
      rw [hcf j hjn']
      unfold bf
      split_ifs with hm
      · exact absurd ((hRel_iff_hlab_of_pos hd hpos).2 (by rw [← hhp j hjn']; exact hjl))
          (h _ hm)
      · rfl
    · intro h b hb hr
      obtain ⟨j, hj, rfl⟩ := hgs b (hB b hb)
      have h1 := h j (mem_filter.2 ⟨mem_range.2 hj, by
        rw [hhp j hj]; exact (hRel_iff_hlab_of_pos hd hpos).1 hr⟩)
      rw [hcf j hj] at h1
      unfold bf at h1
      rw [if_pos hb] at h1
      exact one_ne_zero h1
  unfold pcNf
  simp only [mem_sdiff, mem_filter, hgm i hi, true_and, hinner]
  constructor
  · rintro hn ⟨h1, h2, h3⟩
    exact hn ⟨⟨h1, h2⟩, (htt h1).2 h3⟩
  · rintro hn ⟨⟨h1, h2⟩, h3⟩
    exact hn ⟨h1, h2, (htt h1).1 h3⟩

/-! ### The program -/

/-- The registers of stage 6 from `3100 = R`, `3102 = k`, `3111 = Y`: those of `cfScan`
(`5800 … 5807`, `6521`), `5961 = TTb = Y + n`, `5962 = NFb = Y + n + k + 1`, `5963 = k + 1`. -/
def nf0 : Stmt := block [.loadN 5800 3100, .constN 5806 1, .constN 5807 2, .constN 6521 1,
  .constN 5940 3, .addN 5941 3100 5940, .addN 5801 5941 5800, .addN 5802 5801 5800,
  .addN 5942 5802 5800, .addN 5803 5942 5800, .copyN 5804 3111, .addN 5961 5804 5800,
  .addN 5962 5961 3102, .addN 5962 5962 5806, .addN 5963 3102 5806]

/-- The loads: `6524 = RP[i]`, `6525 = HP[i]`, `6526 = HP[RP[i]]`, `6527 = TT[HP[i]]`. -/
def vbNFa : Stmt :=
  .seq (block [.addN 6524 5801 6520, .loadN 6524 6524])
    (.seq (block [.addN 6525 5802 6520, .loadN 6525 6525])
      (.seq (block [.addN 6526 5802 6524, .loadN 6526 6526])
        (block [.addN 6527 5961 6525, .loadN 6527 6527])))

/-- The arithmetic: `r6523 := nfv r6525 r6526 r6527`. -/
def vbNFb : Stmt :=
  block [.subN 6528 5806 6525, .subN 6528 5806 6528, .subN 6529 6525 6526, .subN 6524 6526 6525,
    .addN 6529 6529 6524, .subN 6529 5806 6529, .addN 6528 6528 6529, .subN 6529 5806 6527,
    .addN 6528 6528 6529, .constN 6529 3, .subN 6528 6529 6528, .subN 6528 5806 6528,
    .subN 6523 5806 6528]

/-- **The value block of the flags of `pcNf`.** -/
def vbNF : Stmt := .seq vbNFa vbNFb

/-- The registers of `saProg`: keys `HP`, values `CF`, stride `1`, table `TT`. -/
def nfSA : Stmt :=
  block [.copyN 4630 5800, .copyN 4631 5802, .copyN 4632 5804, .constN 4633 1, .copyN 4634 5961]

/-- **Stage 6**: the flags of `pcNf` at `Y + n + k + 1`. -/
def nfProg : Stmt :=
  .seq nf0 (.seq cfScan (.seq (zfill 5963 5961) (.seq nfSA (.seq saProg (mapRunS vbNF 5800 5962)))))

/-- The registers written by stage 6. -/
def nfW (x : ℕ) : Prop :=
  (5800 ≤ x ∧ x ≤ 5807) ∨ (5940 ≤ x ∧ x ≤ 5942) ∨ (5961 ≤ x ∧ x ≤ 5963) ∨
    (4630 ≤ x ∧ x ≤ 4639) ∨ (6520 ≤ x ∧ x ≤ 6529)

section Exec

variable {I : Input} {W : ℕ}

theorem nf0_exec (c : Config) (hc : WordsBounded W c) {R n k Y : ℕ} (r0 : c.nreg 3100 = R)
    (r2 : c.nreg 3102 = k) (r11 : c.nreg 3111 = Y) (hn : c.nmem R = n)
    (w : Y + R + 6 * n + k + 10 ≤ W) :
    ∃ c' t, Exec I W nf0 c c' t ∧ t = 15 ∧ c'.nreg 5800 = n ∧ c'.nreg 5801 = R + 3 + n ∧
      c'.nreg 5802 = R + 3 + 2 * n ∧ c'.nreg 5803 = R + 3 + 4 * n ∧ c'.nreg 5804 = Y ∧
      c'.nreg 5806 = 1 ∧ c'.nreg 5807 = 2 ∧ c'.nreg 6521 = 1 ∧ c'.nreg 5961 = Y + n ∧
      c'.nreg 5962 = Y + n + k + 1 ∧ c'.nreg 5963 = k + 1 ∧
      (∀ x, ¬ nfW x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold nf0
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r0, r2, r11, hn]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try (unfold nfW at hx)
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r0, r2, r11, hn])
    try omega

theorem vbNFa_exec (c : Config) (hc : WordsBounded W c) {i RPb HPb TTb : ℕ}
    (r20 : c.nreg 6520 = i) (r01 : c.nreg 5801 = RPb) (r02 : c.nreg 5802 = HPb)
    (r61 : c.nreg 5961 = TTb) (w1 : RPb + i ≤ W) (w4 : HPb + i ≤ W)
    (w5 : HPb + c.nmem (RPb + i) ≤ W) (w6 : TTb + c.nmem (HPb + i) ≤ W) :
    ∃ c' k, Exec I W vbNFa c c' k ∧ k = 8 ∧ c'.nreg 6525 = c.nmem (HPb + i) ∧
      c'.nreg 6526 = c.nmem (HPb + c.nmem (RPb + i)) ∧
      c'.nreg 6527 = c.nmem (TTb + c.nmem (HPb + i)) ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, v1, n1, m1, rr1, rm1, o1⟩ := ld2_exec (P := I) (t := 6524) (r := 6524)
    (b := 5801) (ctr := 6520) c hc r01 r20 w1 (by omega) (by omega)
  have q1 : ∀ x, ¬ vscr x → c₁.nreg x = c.nreg x := fun x hx => by
    unfold vscr at hx; exact n1 x (by omega) (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, v2, n2, m2, rr2, rm2, o2⟩ := ld2_exec (P := I) (t := 6525) (r := 6525)
    (b := 5802) (ctr := 6520) c₁ e₁.wb_right (by rw [q1 _ (by unfold vscr; omega), r02])
    (by rw [q1 _ (by unfold vscr; omega), r20]) w4 (by omega) (by omega)
  have q2 : ∀ x, ¬ vscr x → c₂.nreg x = c.nreg x := fun x hx => by
    unfold vscr at hx; rw [n2 x (by omega) (by omega), q1 x (by unfold vscr; omega)]
  have v1' : c₂.nreg 6524 = c.nmem (RPb + i) := by rw [n2 _ (by omega) (by omega), v1]
  rw [m1] at v2
  obtain ⟨c₃, k₃, e₃, hk₃, v3, n3, m3, rr3, rm3, o3⟩ := ld2_exec (P := I) (t := 6526) (r := 6526)
    (b := 5802) (ctr := 6524) c₂ e₂.wb_right (by rw [q2 _ (by unfold vscr; omega), r02]) v1'
    w5 (by omega) (by omega)
  have q3 : ∀ x, ¬ vscr x → c₃.nreg x = c.nreg x := fun x hx => by
    unfold vscr at hx; rw [n3 x (by omega) (by omega), q2 x (by unfold vscr; omega)]
  have v2' : c₃.nreg 6525 = c.nmem (HPb + i) := by rw [n3 _ (by omega) (by omega), v2]
  rw [m2, m1] at v3
  obtain ⟨c₄, k₄, e₄, hk₄, v4, n4, m4, rr4, rm4, o4⟩ := ld2_exec (P := I) (t := 6527) (r := 6527)
    (b := 5961) (ctr := 6525) c₃ e₃.wb_right (by rw [q3 _ (by unfold vscr; omega), r61]) v2'
    w6 (by omega) (by omega)
  rw [m3, m2, m1] at v4
  refine ⟨c₄, _, .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, ?_, ?_, v4,
    fun x hx => ?_, by rw [m4, m3, m2, m1], by rw [rr4, rr3, rr2, rr1],
    by rw [rm4, rm3, rm2, rm1], by rw [o4, o3, o2, o1]⟩
  · rw [n4 _ (by omega) (by omega), v2']
  · rw [n4 _ (by omega) (by omega), v3]
  · unfold vscr at hx; rw [n4 x (by omega) (by omega), q3 x (by unfold vscr; omega)]

theorem vbNFb_exec (c : Config) (hc : WordsBounded W c) {h hr t : ℕ}
    (r06 : c.nreg 5806 = 1) (r25 : c.nreg 6525 = h) (r26 : c.nreg 6526 = hr)
    (r27 : c.nreg 6527 = t) (w3 : 3 ≤ W) :
    ∃ c' k, Exec I W vbNFb c c' k ∧ k = 13 ∧ c'.nreg 6523 = nfv h hr t ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have b25 : h ≤ W := r25 ▸ hc.1 6525
  have b26 : hr ≤ W := r26 ▸ hc.1 6526
  unfold vbNFb
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r06, r25, r26, r27]; omega)
  refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
    simp (disch := omega) only [upd_other, upd_same, r06, r25, r26, r27]
    rfl
  · unfold vscr at hx
    config_simp
    simp (disch := omega) only [upd_other, upd_same]

theorem vbNF_exec (c : Config) (hc : WordsBounded W c) {i RPb HPb TTb : ℕ}
    (r20 : c.nreg 6520 = i) (r01 : c.nreg 5801 = RPb) (r02 : c.nreg 5802 = HPb)
    (r61 : c.nreg 5961 = TTb) (r06 : c.nreg 5806 = 1) (w1 : RPb + i ≤ W) (w4 : HPb + i ≤ W)
    (w5 : HPb + c.nmem (RPb + i) ≤ W) (w6 : TTb + c.nmem (HPb + i) ≤ W) (w3 : 3 ≤ W) :
    ∃ c' k, Exec I W vbNF c c' k ∧ k ≤ 21 ∧
      c'.nreg 6523 = nfv (c.nmem (HPb + i)) (c.nmem (HPb + c.nmem (RPb + i)))
        (c.nmem (TTb + c.nmem (HPb + i))) ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a5, a6, a7, n1, m1, rr1, rm1, o1⟩ := vbNFa_exec (I := I) c hc r20
    r01 r02 r61 w1 w4 w5 w6
  obtain ⟨c₂, k₂, e₂, hk₂, v2, n2, m2, rr2, rm2, o2⟩ := vbNFb_exec (I := I) c₁ e₁.wb_right
    (by rw [n1 _ (by unfold vscr; omega), r06]) a5 a6 a7 w3
  exact ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, v2, fun x hx => by rw [n2 x hx, n1 x hx],
    by rw [m2, m1], by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1]⟩

theorem nfSA_exec (c : Config) (hc : WordsBounded W c) {n HPb Y TTb : ℕ}
    (r00 : c.nreg 5800 = n) (r02 : c.nreg 5802 = HPb) (r04 : c.nreg 5804 = Y)
    (r61 : c.nreg 5961 = TTb) (w : 1 ≤ W) :
    ∃ c' t, Exec I W nfSA c c' t ∧ t = 5 ∧ c'.nreg 4630 = n ∧ c'.nreg 4631 = HPb ∧
      c'.nreg 4632 = Y ∧ c'.nreg 4633 = 1 ∧ c'.nreg 4634 = TTb ∧
      (∀ x, (x < 4630 ∨ 4634 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold nfSA
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r00, r02, r04, r61])
    try omega

/-- **Stage 6 on a record**: the flags `NF2[i] = bf (g i ∈ pcNf M Q P Hs)` at `Y + n + k + 1`. -/
theorem nfProg_rec {gid : D → ℕ} {ν : V → ℕ} {S T Q : Finset V} {x : MCall M} {m n R : ℕ}
    {g : ℕ → D} (hQ : QPar Q ν) (hd : x.2.1.Pairwise Disjoint) (c : Config)
    (hc : WordsBounded W c) (hA : RArr M gid ν S T x m n R g c.nmem) {Y : ℕ}
    (r0 : c.nreg 3100 = R) (r2 : c.nreg 3102 = x.2.1.length) (r11 : c.nreg 3111 = Y)
    (hRn : c.nmem R = n) (l0 : R + 3 + 6 * n + m ≤ Y)
    (w : Y + R + 6 * n + 2 * x.2.1.length + 20 ≤ W) :
    ∃ c' t, Exec I W nfProg c c' t ∧ t ≤ 70 * n + 7 * x.2.1.length + 40 ∧
      (∀ i < n, c'.nmem (Y + n + x.2.1.length + 1 + i) = bf (g i ∈ pcNf M Q x.1.piece x.2.1)) ∧
      (∀ a, ¬ (Y ≤ a ∧ a < Y + 2 * n + x.2.1.length + 1) → c'.nmem a = c.nmem a) ∧
      (∀ y, ¬ nfW y → c'.nreg y = c.nreg y) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a00, a01, a02, a03, a04, a06, a07, a21, a61, a62, a63, f₁, m₁, rr₁,
    rm₁, o₁⟩ := nf0_exec (I := I) c hc r0 r2 r11 hRn (by clear * - w; omega)
  have hA₁ : RArr M gid ν S T x m n R g c₁.nmem := by rw [m₁]; exact hA
  -- the core's flags
  obtain ⟨c₂, t₂, e₂, ht₂, cf2, m₂, f₂, rr₂, rm₂, o₂⟩ := cfScan_rec (P := I) hQ hd c₁ hA₁
    e₁.wb_right (OUTb := Y) a00 a01 a02 a03 a04 a06 a07 a21 (by clear * - w; omega)
    (by clear * - w; omega) l0
  have g₂ : ∀ y, ¬ vscr y → y ≠ 6522 → y ≠ 6520 → c₂.nreg y = c₁.nreg y := f₂
  -- the table, zeroed
  obtain ⟨c₃, t₃, e₃, ht₃, z3, m₃, f₃, rr₃, rm₃, o₃⟩ := zfill_exec (P := I) c₂ e₂.wb_right
    (bnd := 5963) (ob := 5961) (m := x.2.1.length + 1) (Ob := Y + n)
    ((g₂ 5963 (by unfold vscr; decide) (by decide) (by decide)).trans a63)
    ((g₂ 6521 (by unfold vscr; decide) (by decide) (by decide)).trans a21)
    ((g₂ 5961 (by unfold vscr; decide) (by decide) (by decide)).trans a61)
    (by clear * - w; omega) (by clear * - w; omega) (by unfold vscr; decide)
    (by unfold vscr; decide) (by decide) (by decide) (by decide) (by decide)
  have g₃ : ∀ y, ¬ vscr y → y ≠ 6522 → y ≠ 6520 → c₃.nreg y = c₁.nreg y := fun y h1 h2 h3 => by
    rw [f₃ y h1 h2 h3, g₂ y h1 h2 h3]
  -- the registers of the scatter-add
  obtain ⟨c₄, t₄, e₄, ht₄, s30, s31, s32, s33, s34, f₄, m₄, rr₄, rm₄, o₄⟩ := nfSA_exec (I := I) c₃
    e₃.wb_right ((g₃ 5800 (by unfold vscr; decide) (by decide) (by decide)).trans a00)
    ((g₃ 5802 (by unfold vscr; decide) (by decide) (by decide)).trans a02)
    ((g₃ 5804 (by unfold vscr; decide) (by decide) (by decide)).trans a04)
    ((g₃ 5961 (by unfold vscr; decide) (by decide) (by decide)).trans a61) (by clear * - w; omega)
  -- memory facts at `c₄`
  have mrec : ∀ a < Y, c₄.nmem a = c.nmem a := fun a ha => by
    rw [m₄, m₃ a (by clear * - ha; omega), m₂ a (by clear * - ha; omega), m₁]
  have mcf : ∀ j < n, c₄.nmem (Y + 1 * j) = bf (g j ∈ pdarts M (core M Q x.1.piece) x.2.1) :=
    fun j hj => by
      rw [one_mul, m₄, m₃ _ (by clear * - hj; omega)]
      exact cf2 j hj
  have hkey : ∀ j < n, c₄.nmem (R + 3 + 2 * n + j) = hlab x.2.1 (M.tail (g j)) := fun j hj => by
    rw [mrec _ (by clear * - hj l0; omega)]; exact hA.hp j hj
  have hsum : ∑ j ∈ range n, c₄.nmem (Y + 1 * j) ≤ n := by
    calc ∑ j ∈ range n, c₄.nmem (Y + 1 * j) ≤ ∑ _j ∈ range n, 1 :=
          sum_le_sum fun j hj => by rw [mcf j (mem_range.1 hj)]; exact bf_le_one _
      _ = n := by simp
  -- the scatter-add
  obtain ⟨c₅, t₅, e₅, ht₅, tt5, m₅, f₅, rr₅, rm₅, o₅⟩ := saProg_exec (P := I) c₄ e₄.wb_right
    (m := n) (nk := x.2.1.length + 1) s30 s31 s32 s33 s34
    (fun j hj => by rw [hkey j hj]; have := hlab_le x.2.1 (M.tail (g j)); omega)
    (fun k hk => by rw [m₄]; exact z3 k hk)
    (fun j hj => by clear * - hj l0; omega) (fun j hj => by clear * - hj; omega)
    (by clear * - w; omega) (by clear * - w; omega) (fun j hj => by clear * - w hj; omega)
    (by clear * - w; omega) (by clear * - w hsum; omega)
  have g₅ : ∀ y, ¬ vscr y → y ≠ 6522 → y ≠ 6520 → (y < 4630 ∨ 4639 < y) →
      c₅.nreg y = c₁.nreg y := fun y h1 h2 h3 h4 => by
    rw [f₅ y (by omega), f₄ y (by omega), g₃ y h1 h2 h3]
  have m5r : ∀ a, a < Y + n → c₅.nmem a = c₄.nmem a := fun a ha =>
    m₅ a (by clear * - ha; omega)
  -- the flags
  obtain ⟨c₆, t₆, e₆, ht₆, nf6, m₆, f₆, rr₆, rm₆, o₆⟩ := mapRun_exec (P := I) c₅ e₅.wb_right
    (vb := vbNF) (bnd := 5800) (ob := 5962) (m := n) (Ob := Y + n + x.2.1.length + 1) (B := 21)
    (fun i => nfv (c₅.nmem (R + 3 + 2 * n + i))
      (c₅.nmem (R + 3 + 2 * n + c₅.nmem (R + 3 + n + i)))
      (c₅.nmem (Y + n + c₅.nmem (R + 3 + 2 * n + i))))
    ((g₅ 5800 (by unfold vscr; decide) (by decide) (by decide) (by decide)).trans a00)
    ((g₅ 6521 (by unfold vscr; decide) (by decide) (by decide) (by decide)).trans a21)
    ((g₅ 5962 (by unfold vscr; decide) (by decide) (by decide) (by decide)).trans a62)
    (by clear * - w; omega) (by clear * - w; omega) (by unfold vscr; decide)
    (by unfold vscr; decide) (by decide) (by decide) (by decide) (by decide)
    (fun i hi c' hw h20 hr hm => by
      have hrp := (hA.rp i hi).1
      have e1 : c'.nmem (R + 3 + n + i) = c₅.nmem (R + 3 + n + i) :=
        hm _ (by clear * - hi l0; omega)
      rw [m5r _ (by clear * - hi l0; omega), mrec _ (by clear * - hi l0; omega)] at e1
      have hkl : c₅.nmem (R + 3 + 2 * n + i) ≤ x.2.1.length := by
        rw [m5r _ (by clear * - hi l0; omega), hkey i hi]; exact hlab_le _ _
      have e2 : c'.nmem (R + 3 + 2 * n + i) = c₅.nmem (R + 3 + 2 * n + i) :=
        hm _ (by clear * - hi l0; omega)
      have e3 : c'.nmem (R + 3 + 2 * n + c₅.nmem (R + 3 + n + i)) =
          c₅.nmem (R + 3 + 2 * n + c₅.nmem (R + 3 + n + i)) := by
        rw [m5r (R + 3 + n + i) (by clear * - hi l0; omega), mrec _ (by clear * - hi l0; omega)]
        exact hm _ (by clear * - hrp l0; omega)
      have e4 : c'.nmem (Y + n + c₅.nmem (R + 3 + 2 * n + i)) =
          c₅.nmem (Y + n + c₅.nmem (R + 3 + 2 * n + i)) := hm _ (by clear * - hkl; omega)
      have e1' : c'.nmem (R + 3 + n + i) = c₅.nmem (R + 3 + n + i) :=
        hm _ (by clear * - hi l0; omega)
      have hr5 : c₅.nmem (R + 3 + n + i) < n := by
        rw [m5r _ (by clear * - hi l0; omega), mrec _ (by clear * - hi l0; omega)]; exact hrp
      obtain ⟨c₂', k, e, hk, v, n2, m2, rr2, rm2, o2⟩ := vbNF_exec (I := I) c' hw h20
        (RPb := R + 3 + n) (HPb := R + 3 + 2 * n) (TTb := Y + n)
        (by rw [hr _ (by unfold vscr; decide) (by decide) (by decide), g₅ 5801
          (by unfold vscr; decide) (by decide) (by decide) (by decide)]; exact a01)
        (by rw [hr _ (by unfold vscr; decide) (by decide) (by decide), g₅ 5802
          (by unfold vscr; decide) (by decide) (by decide) (by decide)]; exact a02)
        (by rw [hr _ (by unfold vscr; decide) (by decide) (by decide), g₅ 5961
          (by unfold vscr; decide) (by decide) (by decide) (by decide)]; exact a61)
        (by rw [hr _ (by unfold vscr; decide) (by decide) (by decide), g₅ 5806
          (by unfold vscr; decide) (by decide) (by decide) (by decide)]; exact a06)
        (by clear * - w hi; omega) (by clear * - w hi; omega)
        (by rw [e1']; clear * - w hr5; omega) (by rw [e2]; clear * - w hkl; omega)
        (by clear * - w; omega)
      rw [e2, e1', e3, e4] at v
      exact ⟨c₂', k, e, hk, v, n2, m2, rr2, rm2, o2⟩)
  refine ⟨c₆, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), ?_, fun i hi => ?_,
    fun a ha => ?_, fun y hy => ?_, by rw [rr₆, rr₅, rr₄, rr₃, rr₂, rr₁],
    by rw [rm₆, rm₅, rm₄, rm₃, rm₂, rm₁], by rw [o₆, o₅, o₄, o₃, o₂, o₁]⟩
  · clear * - ht₁ ht₂ ht₃ ht₄ ht₅ ht₆
    omega
  · rw [nf6 i hi, nfv_eq]
    have hrp := hA.rp i hi
    have hkl : c₄.nmem (R + 3 + 2 * n + i) ≤ x.2.1.length := by
      rw [hkey i hi]; exact hlab_le _ _
    have q1 : c₅.nmem (R + 3 + 2 * n + i) = c₄.nmem (R + 3 + 2 * n + i) :=
      m5r _ (by clear * - hi l0; omega)
    have q2 : c₅.nmem (R + 3 + n + i) = c₄.nmem (R + 3 + n + i) :=
      m5r _ (by clear * - hi l0; omega)
    have q2' : c₄.nmem (R + 3 + n + i) = c.nmem (R + 3 + n + i) :=
      mrec _ (by clear * - hi l0; omega)
    have q3 : c₅.nmem (R + 3 + 2 * n + c₄.nmem (R + 3 + n + i)) =
        c₄.nmem (R + 3 + 2 * n + c₄.nmem (R + 3 + n + i)) := by
      rw [q2']; exact m5r _ (by clear * - hrp l0; omega)
    have q4 : c₅.nmem (Y + n + c₄.nmem (R + 3 + 2 * n + i)) =
        saF (fun j => c₄.nmem (R + 3 + 2 * n + j)) (fun j => c₄.nmem (Y + 1 * j)) n
          (c₄.nmem (R + 3 + 2 * n + i)) := tt5 _ (by clear * - hkl; omega)
    rw [q1, q2, q3, q4]
    have key := mem_pcNf_iff_tt (M := M) (Q := Q) hd (n := n) (g := g) hA.g_mem hA.g_surj
      (rp := fun j => c₄.nmem (R + 3 + n + j)) (hp := fun j => c₄.nmem (R + 3 + 2 * n + j))
      (cf := fun j => c₄.nmem (Y + 1 * j))
      (fun j hj => by
        rw [mrec _ (by clear * - hj l0; omega)]; exact hA.rp j hj) hkey mcf hi
    unfold bf
    by_cases hm : g i ∈ pcNf M Q x.1.piece x.2.1
    · rw [if_pos (key.1 hm), if_pos hm]
    · rw [if_neg (fun h => hm (key.2 h)), if_neg hm]
  · rw [m₆ a (by clear * - ha; omega), m₅ a (by clear * - ha; omega), m₄, m₃ a (by clear * - ha; omega),
      m₂ a (by clear * - ha; omega), m₁]
  · unfold nfW at hy
    rw [f₆ y (by unfold vscr; clear * - hy; omega) (by clear * - hy; omega)
      (by clear * - hy; omega), g₅ y (by unfold vscr; clear * - hy; omega)
      (by clear * - hy; omega) (by clear * - hy; omega) (by clear * - hy; omega),
      f₁ y (by unfold nfW; exact hy)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
