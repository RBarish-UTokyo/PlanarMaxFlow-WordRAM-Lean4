module

public import PlanarFlow.Monge.SmawkRed

/-!
# SMAWK on the machine: the interpolation of one level

At the level `s`, with the reduced list `L` of the level (at `base + k · stride`, ended by the
sentinel `n`) and the leftmost minima of the rows `2s, 4s, …` already stored, `upRows ent` finds
the leftmost minima of the rows `s, 3s, 5s, …` (rows numbered from `1`): the window of the row
`r` in `L` runs from the position `ptr` of the minimum of the row `r - s` to the last position
whose column is at most the minimum of the row `r + s` (`PlanarFlow.Monge.interp_eq`), and the
next window starts where this one ends (`PlanarFlow.Monge.interp_next`). The windows of one level
overlap only at their ends, so the level costs `O(E (len + rows))` steps.

Registers: `r60 = m`, `r61 = n`, `r62 = pb`, `r63 = 1`, `r65 = s`, `r66 = m + 1`, `r69 = base`,
`r72 = stride = 2s` (fixed); `r67 = r` the row, `r68 = ptr`, `r73 = h` the bound of the window
(one more than the minimum of the row `r + s`, or `n`), `r74` the position, `r75` its column,
`r76` the best column; `r70 = r - 1` and `r71` the arguments of the oracle; the real `r71` is the
best entry; `r77, r78, r79` addresses.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The program -/

/-- One step of the scan of a window: the position `r74`, with column `r75`. -/
def scanL (ent : Stmt) : Stmt :=
  .seq (.instr (.copyN 71 75)) <| .seq ent <|
  .ifLtR 70 71
    (block [.copyR 71 70, .copyN 76 75, .addN 74 74 63, .mulN 78 74 72, .addN 78 78 69, .loadN 75 78])
    (block [.addN 74 74 63, .mulN 78 74 72, .addN 78 78 69, .loadN 75 78])

/-- One row `r = r67` of the level. -/
def upRow (ent : Stmt) : Stmt :=
  .seq (.instr (.addN 79 67 65)) <|
  .seq (.ifLtN 79 66 (block [.addN 78 62 79, .loadN 73 78, .addN 73 73 63]) (.instr (.copyN 73 61))) <|
  .seq (block [.subN 70 67 63, .copyN 74 68, .mulN 78 74 72, .addN 78 78 69, .loadN 71 78]) <|
  .seq ent <|
  .seq (block [.copyR 71 70, .copyN 76 71, .addN 74 74 63, .mulN 78 74 72, .addN 78 78 69,
    .loadN 75 78]) <|
  .seq (.whileLtN 75 73 (scanL ent)) <|
  block [.addN 78 62 67, .storeN 78 76, .storeR 78 71, .subN 68 74 63, .addN 67 67 72]

/-- The rows `s, 3s, 5s, …` of the level `s = r65` (with `r69`, `r72` set). -/
def upRows (ent : Stmt) : Stmt :=
  .seq (block [.copyN 67 65, .constN 68 0]) (.whileLtN 67 66 (upRow ent))

/-! ### The scan -/

/-- The state of the scan of the window of the row `R` of `A` starting at the position `lo`,
from the configuration `c₁`. -/
structure ISL (W : ℕ) (A : ℕ → ℕ → ℝ) (pb K : ℕ) (L : ℕ → ℕ) (len R lo h : ℕ) (c₀ c₁ c : Config) :
    Prop where
  wb : WordsBounded W c
  agree : Agree pb K c₀ c
  nreg : ∀ r < 80, r ≠ 71 → r ≠ 74 → r ≠ 75 → r ≠ 76 → r ≠ 78 → c.nreg r = c₁.nreg r
  rreg : ∀ r < 80, r ≠ 70 → r ≠ 71 → c.rreg r = c₁.rreg r
  nmem : c.nmem = c₁.nmem
  rmem : c.rmem = c₁.rmem
  out : c.output = c₁.output
  cur : lo < c.nreg 74
  curle : c.nreg 74 ≤ len
  col : c.nreg 75 = L (c.nreg 74)
  below : ∀ i, lo ≤ i → i < c.nreg 74 → L i < h
  best : ∃ bp, IsLMin (fun i => A R (L i)) lo (c.nreg 74 - 1) bp ∧ c.nreg 76 = L bp ∧
    c.rreg 71 = A R (L bp)

variable {P : Input} {W : ℕ} {ent : Stmt} {A : ℕ → ℕ → ℝ} {E m n pb K : ℕ} {c₀ : Config}

theorem scanL_exec (hent : EntSpecK P W ent A E m n pb K c₀) {L : ℕ → ℕ} {len R lo h base stride : ℕ}
    {c₁ : Config} (hL : IsCols n L len) (hLm : ∀ k ≤ len, c₁.nmem (base + k * stride) = L k)
    (hR : R < m) (hh : h ≤ n) (h70 : c₁.nreg 70 = R) (h63 : c₁.nreg 63 = 1)
    (h69 : c₁.nreg 69 = base) (h72 : c₁.nreg 72 = stride) (h73 : c₁.nreg 73 = h)
    (hW : base + len * stride ≤ W) (hstr : 0 < stride) (c : Config) (hI : ISL W A pb K L len R lo h c₀ c₁ c)
    (hlt : c.nreg 75 < c.nreg 73) :
    ∃ c' k, Exec P W (scanL ent) c c' k ∧ ISL W A pb K L len R lo h c₀ c₁ c' ∧
      (E + 10) * (len - c'.nreg 74) + k + 2 ≤ (E + 10) * (len - c.nreg 74) := by
  have hc := hI.wb
  have g : ∀ r < 80, r ≠ 71 → r ≠ 74 → r ≠ 75 → r ≠ 76 → r ≠ 78 → c.nreg r = c₁.nreg r := hI.nreg
  rw [g 73 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h73, hI.col] at hlt
  generalize hcur : c.nreg 74 = cur at hlt
  have hcurlen : cur < len := by
    have := hI.curle; rw [hcur] at this
    rcases Nat.eq_or_lt_of_le this with e | e
    · rw [e, hL.2] at hlt; omega
    · exact e
  have hLc : L cur < n := hL.lt hcurlen
  unfold scanL
  refine spec_seq ?_
  refine spec_instr (Exec.copyN hc 71 75) fun hw₁ => ?_
  refine spec_seq ?_
  refine spec_use (hent _ hw₁ (hI.agree.of_eq (fun r hr => by config_simp; rw [upd_other _ _ _
      (by omega)]) (fun _ _ => rfl) rfl rfl rfl) (by config_simp; rw [g 70 (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), h70]; exact hR)
    (by config_simp; rw [hI.col, hcur]; exact hLc)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hv, hn₂, hr₂, hnm₂, hrm₂, ho₂⟩
  config_simp at hv
  rw [g 70 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h70, hI.col,
    hcur] at hv
  have e₂ : ∀ r < 80, r ≠ 71 → c₂.nreg r = c.nreg r := fun r hr a => by
    rw [hn₂ r hr]; config_simp; rw [upd_other _ _ _ a]
  have g63 : c₂.nreg 63 = 1 := by
    rw [e₂ 63 (by omega) (by omega), g 63 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), h63]
  have g69 : c₂.nreg 69 = base := by
    rw [e₂ 69 (by omega) (by omega), g 69 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), h69]
  have g72 : c₂.nreg 72 = stride := by
    rw [e₂ 72 (by omega) (by omega), g 72 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), h72]
  have g74 : c₂.nreg 74 = cur := by rw [e₂ 74 (by omega) (by omega), hcur]
  have hm₂ : c₂.nmem = c₁.nmem := by rw [hnm₂]; config_simp; exact hI.nmem
  have hst : (cur + 1) * stride ≤ len * stride := Nat.mul_le_mul_right _ hcurlen
  have hlenW : len ≤ len * stride := Nat.le_mul_of_pos_right _ hstr
  obtain ⟨bp, hbp, hb76, hb71⟩ := hI.best
  rw [hcur] at hbp
  have hb71' : c₂.rreg 71 = A R (L bp) := by rw [hr₂ 71 (by omega) (by omega)]; exact hb71
  have hb76' : c₂.nreg 76 = L bp := by rw [e₂ 76 (by omega) (by omega)]; exact hb76
  have hc1 : cur - 1 + 1 = cur := by have := hI.cur; omega
  -- the frame of the step
  have fin : ∀ c' : Config, WordsBounded W c' →
      (∀ r < 80, r ≠ 71 → r ≠ 74 → r ≠ 75 → r ≠ 76 → r ≠ 78 → c'.nreg r = c₂.nreg r) →
      (∀ r < 80, r ≠ 70 → r ≠ 71 → c'.rreg r = c₂.rreg r) → c'.nmem = c₂.nmem →
      c'.rmem = c₂.rmem → c'.output = c₂.output → c'.nreg 74 = cur + 1 →
      c'.nreg 75 = L (cur + 1) →
      (∃ bp', IsLMin (fun i => A R (L i)) lo cur bp' ∧ c'.nreg 76 = L bp' ∧
        c'.rreg 71 = A R (L bp')) → ISL W A pb K L len R lo h c₀ c₁ c' := by
    intro c' hw' hn' hr' hnm' hrm' ho' h74 h75 hb
    refine ⟨hw', ?_, fun r hr a b d e f => ?_, fun r hr a b => ?_, by rw [hnm', hm₂],
      by rw [hrm', hrm₂]; config_simp; exact hI.rmem, by rw [ho', ho₂]; config_simp; exact hI.out,
      by rw [h74]; have := hI.cur; omega, by rw [h74]; omega, by rw [h75, h74],
      fun i h1 h2 => ?_, by rw [h74, Nat.add_sub_cancel]; exact hb⟩
    · refine hI.agree.of_eq (fun r hr => ?_) (fun r hr => ?_) (by rw [hnm', hnm₂])
        (by rw [hrm', hrm₂]) (by rw [ho', ho₂])
      · rw [hn' r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
          e₂ r (by omega) (by omega)]
      · rw [hr' r (by omega) (by omega) (by omega), hr₂ r (by omega) (by omega)]
    · rw [hn' r hr a b d e f, e₂ r hr a]; exact g r hr a b d e f
    · rw [hr' r hr a b, hr₂ r hr a]; config_simp; exact hI.rreg r hr a b
    · rw [h74] at h2
      rcases Nat.lt_or_ge i cur with h3 | h3
      · exact hI.below i h1 (by rw [hcur]; exact h3)
      · rw [show i = cur by omega]; exact hlt
  by_cases hcmp : A R (L cur) < A R (L bp)
  · refine spec_ifLtR_true (by rw [hv, hb71']; exact hcmp) ?_
    exec_block
    · config_simp; rw [g74, g63]; omega
    · config_simp; rw [g74, g63, g72]; omega
    · config_simp; rw [g74, g63, g72, g69]; omega
    refine ⟨fin _ ‹_› (fun r hr a b d e f => ?_) (fun r hr a b => ?_) rfl rfl rfl ?_ ?_ ?_, ?_⟩
    · config_simp
      rw [upd_other _ _ _ d, upd_other _ _ _ f, upd_other _ _ _ b, upd_other _ _ _ e]
    · config_simp; rw [upd_other _ _ _ b]
    · config_simp; rw [g74, g63]
    · config_simp; rw [g74, g63, g72, g69, hm₂, Nat.add_comm, hLm _ (by omega)]
    · refine ⟨cur, ?_, ?_, ?_⟩
      · have := hbp.scan_succ_lt (by show A R (L (cur - 1 + 1)) < A R (L bp); rw [hc1]; exact hcmp)
        rwa [hc1] at this
      · config_simp; rw [hn₂ 75 (by omega)]; config_simp; rw [hI.col, hcur]
      · config_simp; exact hv
    · config_simp; rw [g74, g63]
      rw [show len - cur = len - (cur + 1) + 1 by omega, Nat.mul_add, Nat.mul_one]
      omega
  · refine spec_ifLtR_false (by rw [hv, hb71']; exact hcmp) ?_
    exec_block
    · rw [g74, g63]; omega
    · config_simp; rw [g74, g63, g72]; omega
    · config_simp; rw [g74, g63, g72, g69]; omega
    refine ⟨fin _ ‹_› (fun r hr a b d e f => ?_) (fun r hr a b => rfl) rfl rfl rfl ?_ ?_ ?_, ?_⟩
    · config_simp
      rw [upd_other _ _ _ d, upd_other _ _ _ f, upd_other _ _ _ b]
    · config_simp; rw [g74, g63]
    · config_simp; rw [g74, g63, g72, g69, hm₂, Nat.add_comm, hLm _ (by omega)]
    · refine ⟨bp, ?_, ?_, hb71'⟩
      · have := hbp.scan_succ_ge (by show ¬ A R (L (cur - 1 + 1)) < A R (L bp); rw [hc1]; exact hcmp)
        rwa [hc1] at this
      · config_simp; exact hb76'
    · config_simp; rw [g74, g63]
      rw [show len - cur = len - (cur + 1) + 1 by omega, Nat.mul_add, Nat.mul_one]
      omega

/-! ### One row -/

/-- The data of a level of the interpolation, in the configuration `cS` at its start. -/
structure UpData (W : ℕ) (A : ℕ → ℕ → ℝ) (m n pb K s len base : ℕ) (L : ℕ → ℕ) (cS : Config) :
    Prop where
  r60 : cS.nreg 60 = m
  r61 : cS.nreg 61 = n
  r62 : cS.nreg 62 = pb
  r63 : cS.nreg 63 = 1
  r65 : cS.nreg 65 = s
  r66 : cS.nreg 66 = m + 1
  r69 : cS.nreg 69 = base
  r72 : cS.nreg 72 = 2 * s
  cols : IsCols n L len
  mem : ∀ k ≤ len, cS.nmem (base + k * (2 * s)) = L k
  minL : ∀ k < m / s, ∃ v < len, L v = lmin n A (rowL s k)
  base_gt : pb + m < base
  wlen : base + len * (2 * s) ≤ W
  spos : 0 < s
  sle : s ≤ m
  w3 : pb + 3 * m ≤ W
  mK : m ≤ K

lemma UpData.minRow {W : ℕ} {A : ℕ → ℕ → ℝ} {m n pb K s len base : ℕ} {L : ℕ → ℕ} {cS : Config}
    (h : UpData W A m n pb K s len base L cS) {k : ℕ} (hk : (k + 1) * s ≤ m) :
    ∃ v < len, L v = lmin n A ((k + 1) * s - 1) :=
  h.minL k ((Nat.le_div_iff_mul_le h.spos).2 hk)

/-- The state of the rows of the level `s`: the rows divisible by `2s` and the rows `s, 3s, …`
below the current row `r67` are done, and `r68` is the position in `L` of the minimum of the row
`r67 - s`. -/
structure IU (W : ℕ) (A : ℕ → ℕ → ℝ) (m n pb K s len : ℕ) (L : ℕ → ℕ) (c₀ cS c : Config) : Prop where
  wb : WordsBounded W c
  agree : Agree pb K c₀ c
  nreg : ∀ r < 80, r ≠ 67 → r ≠ 68 → r ≠ 70 → r ≠ 71 → r ≠ 73 → r ≠ 74 → r ≠ 75 → r ≠ 76 →
    r ≠ 77 → r ≠ 78 → r ≠ 79 → c.nreg r = cS.nreg r
  rreg : ∀ r < 80, r ≠ 70 → r ≠ 71 → c.rreg r = cS.rreg r
  nmem : ∀ a, (a ≤ pb ∨ pb + m < a) → c.nmem a = cS.nmem a
  rmem : ∀ a, (a ≤ pb ∨ pb + m < a) → c.rmem a = cS.rmem a
  out : c.output = cS.output
  cur : ∃ u, c.nreg 67 = s + 2 * s * u
  curle : c.nreg 67 ≤ m + 2 * s
  ptrle : c.nreg 68 ≤ len
  ptr : c.nreg 67 ≤ m → (c.nreg 67 = s ∧ c.nreg 68 = 0) ∨
    (s < c.nreg 67 ∧ L (c.nreg 68) = lmin n A (c.nreg 67 - s - 1))
  done : ∀ r, 1 ≤ r → r ≤ m → (2 * s ∣ r ∨ (s ∣ r ∧ r < c.nreg 67)) → Done A n pb c r

lemma IU.reg {W : ℕ} {A : ℕ → ℕ → ℝ} {m n pb K s len : ℕ} {L : ℕ → ℕ} {c₀ cS c : Config}
    (h : IU W A m n pb K s len L c₀ cS c) {r : ℕ} (hr : r < 67 ∨ r = 69 ∨ r = 72) :
    c.nreg r = cS.nreg r :=
  h.nreg r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)

theorem upRow_exec (hent : EntSpecK P W ent A E m n pb K c₀) (hA : IsTotMono m n A)
    {s len base : ℕ} {L : ℕ → ℕ} {cS : Config} (hU : UpData W A m n pb K s len base L cS)
    (c : Config) (hI : IU W A m n pb K s len L c₀ cS c) (hlt : c.nreg 67 < c.nreg 66) :
    ∃ c' k, Exec P W (upRow ent) c c' k ∧ IU W A m n pb K s len L c₀ cS c' ∧
      (E + 30) * ((m + 2 * s - c'.nreg 67) / (2 * s)) + (E + 10) * (len - c'.nreg 68) + k + 2 ≤
        (E + 30) * ((m + 2 * s - c.nreg 67) / (2 * s)) + (E + 10) * (len - c.nreg 68) := by
  have hc := hI.wb
  have hs := hU.spos
  have hsm := hU.sle
  have hw3 := hU.w3
  have hwlen := hU.wlen
  have hbg := hU.base_gt
  have hn : 0 < n := by
    obtain ⟨v, hv, -⟩ := hU.minRow (k := 0) (by omega)
    have := hU.cols.lt hv; omega
  have g60 : c.nreg 60 = m := (hI.reg (by omega)).trans hU.r60
  have g61 : c.nreg 61 = n := (hI.reg (by omega)).trans hU.r61
  have g62 : c.nreg 62 = pb := (hI.reg (by omega)).trans hU.r62
  have g63 : c.nreg 63 = 1 := (hI.reg (by omega)).trans hU.r63
  have g65 : c.nreg 65 = s := (hI.reg (by omega)).trans hU.r65
  have g66 : c.nreg 66 = m + 1 := (hI.reg (by omega)).trans hU.r66
  have g69 : c.nreg 69 = base := (hI.reg (by omega)).trans hU.r69
  have g72 : c.nreg 72 = 2 * s := (hI.reg (by omega)).trans hU.r72
  rw [g66] at hlt
  generalize hr : c.nreg 67 = r at hlt
  have hrm : r ≤ m := by omega
  obtain ⟨u, hu⟩ := hI.cur
  rw [hr] at hu
  generalize hp : c.nreg 68 = ptr
  have hptr := hI.ptr
  rw [hr, hp] at hptr
  have hptrle : ptr ≤ len := hp ▸ hI.ptrle
  -- the row and its minimum in `L`
  have hrow : r = (2 * u + 1) * s := by rw [hu]; ring
  have hR : r - 1 < m := by omega
  obtain ⟨istar, histar, hLstar⟩ := hU.minRow (k := 2 * u) (by rw [← hrow]; exact hrm)
  rw [← hrow] at hLstar
  have hmem : ∀ k ≤ len, c.nmem (base + k * (2 * s)) = L k := fun k hk => by
    rw [hI.nmem _ (Or.inr (by omega))]; exact hU.mem k hk
  have hnW : n ≤ W := by rw [← hU.cols.2, ← hmem len le_rfl]; exact hc.2 _
  -- the left end of the window
  have hptrlo : L ptr ≤ L istar := by
    rcases hptr hrm with ⟨-, rfl⟩ | ⟨hsr, hL⟩
    · exact (hU.cols.le_iff histar.le (Nat.zero_le _)).2 (Nat.zero_le _)
    · rw [hL, hLstar]; exact hA.lmin_mono (by omega) hR hn
  have hptrlen : ptr < len := by
    by_contra hcon
    have : ptr = len := by omega
    rw [this, hU.cols.2] at hptrlo
    have := hU.cols.lt histar; omega
  -- the bound of the window
  generalize hhv : (if r + s ≤ m then lmin n A (r + s - 1) + 1 else n) = h
  have hhn : h ≤ n := by
    rw [← hhv]; split_ifs
    · have := lmin_lt A (r + s - 1) hn; omega
    · exact le_rfl
  have hstarh : L istar < h := by
    rw [← hhv, hLstar]; split_ifs with hrs
    · have := hA.lmin_mono (i := r - 1) (i' := r + s - 1) (by omega) (by omega) hn; omega
    · exact lmin_lt A _ hn
  unfold upRow
  refine spec_seq ?_
  refine spec_instr (Exec.addN hc 79 67 65 (by rw [hr, g65]; omega)) fun hw₁ => ?_
  refine spec_seq ?_
  -- step 2: `r73 := h`
  have step2 : ∃ c' k, Exec P W (.ifLtN 79 66 (block [.addN 78 62 79, .loadN 73 78, .addN 73 73 63])
      (.instr (.copyN 73 61))) { c with nreg := upd c.nreg 79 (c.nreg 67 + c.nreg 65) } c' k ∧
      k ≤ 4 ∧ (c'.nreg 73 = h ∧ (∀ r, r ≠ 73 → r ≠ 78 → r ≠ 79 → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
    by_cases hrs : r + s ≤ m
    · refine spec_ifLtN_true (by config_simp; rw [hr, g65, g66]; omega) ?_
      have hdone := hI.done (r + s) (by omega) hrs (Or.inl ⟨u + 1, by rw [hu]; ring⟩)
      exec_block
      · config_simp; rw [g62, hr, g65]; omega
      · config_simp; rw [g62, hr, g65, hdone.1, g63]; have := lmin_lt A (r + s - 1) hn; omega
      refine ⟨by omega, ?_, fun r' a b d => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [g62, hr, g65, hdone.1, g63, ← hhv, ite_eq_left hrs]
      · config_simp; rw [upd_other _ _ _ a, upd_other _ _ _ b, upd_other _ _ _ d]
    · refine spec_ifLtN_false (by config_simp; rw [hr, g65, g66]; omega) ?_
      refine spec_instr (Exec.copyN ‹_› 73 61) fun _ => ?_
      refine ⟨by omega, ?_, fun r' a b d => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [g61, ← hhv, ite_eq_right hrs]
      · config_simp; rw [upd_other _ _ _ a, upd_other _ _ _ d]
  refine spec_use step2 ?_
  intro c₂ k₂ hk₂ hw₂ ⟨h73₂, e₂, hr₂, hnm₂, hrm₂, ho₂⟩
  -- step 3: the first position of the window
  have hpst : ptr * (2 * s) ≤ len * (2 * s) := Nat.mul_le_mul_right _ hptrle
  refine spec_seq ?_
  exec_block
  · config_simp; rw [e₂ 68 (by omega) (by omega) (by omega), hp, e₂ 72 (by omega) (by omega)
      (by omega), g72]; omega
  · config_simp; rw [e₂ 68 (by omega) (by omega) (by omega), hp, e₂ 72 (by omega) (by omega)
      (by omega), g72, e₂ 69 (by omega) (by omega) (by omega), g69]; omega
  generalize hc₃ : (Config.mk _ _ _ _ _ _ : Config) = c₃
  have hw₃ : WordsBounded W c₃ := hc₃ ▸ ‹_›
  have e₃ : ∀ r', r' ≠ 70 → r' ≠ 71 → r' ≠ 73 → r' ≠ 74 → r' ≠ 78 → r' ≠ 79 →
      c₃.nreg r' = c.nreg r' := fun r' a b d e f g => by
    rw [← hc₃]; config_simp
    rw [upd_other _ _ _ b, upd_other _ _ _ f, upd_other _ _ _ e, upd_other _ _ _ a,
      e₂ r' d f g]
  have g70₃ : c₃.nreg 70 = r - 1 := by
    rw [← hc₃]; config_simp; rw [e₂ 67 (by omega) (by omega) (by omega), hr,
      e₂ 63 (by omega) (by omega) (by omega), g63]
  have g71₃ : c₃.nreg 71 = L ptr := by
    rw [← hc₃]; config_simp
    rw [e₂ 68 (by omega) (by omega) (by omega), hp, e₂ 72 (by omega) (by omega) (by omega), g72,
      e₂ 69 (by omega) (by omega) (by omega), g69, hnm₂, Nat.add_comm, hmem ptr hptrle]
  have g73₃ : c₃.nreg 73 = h := by rw [← hc₃]; config_simp; exact h73₂
  have g74₃ : c₃.nreg 74 = ptr := by
    rw [← hc₃]; config_simp; rw [e₂ 68 (by omega) (by omega) (by omega), hp]
  have hm₃ : c₃.nmem = c.nmem := by rw [← hc₃]; exact hnm₂
  have hrm₃ : c₃.rmem = c.rmem := by rw [← hc₃]; exact hrm₂
  have hrr₃ : c₃.rreg = c.rreg := by rw [← hc₃]; exact hr₂
  have ho₃ : c₃.output = c.output := by rw [← hc₃]; exact ho₂
  have A₃ : Agree pb K c₀ c₃ := hI.agree.of_eq (fun r' hr' => e₃ r' (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)) (fun r' _ => by rw [hrr₃]) hm₃ hrm₃ ho₃
  -- step 4: the entry at the first position
  refine spec_seq ?_
  refine spec_use (hent c₃ hw₃ A₃ (by rw [g70₃]; exact hR)
    (by rw [g71₃]; exact hU.cols.lt hptrlen)) ?_
  intro c₄ k₄ hk₄ hw₄ ⟨hv₄, hn₄, hr₄, hnm₄, hrm₄, ho₄⟩
  rw [g70₃, g71₃] at hv₄
  -- step 5: the start of the scan
  have hpst' : (ptr + 1) * (2 * s) ≤ len * (2 * s) := Nat.mul_le_mul_right _ hptrlen
  have hlenW : len ≤ len * (2 * s) := Nat.le_mul_of_pos_right _ (by omega)
  refine spec_seq ?_
  exec_block
  · config_simp; rw [hn₄ 74 (by omega), g74₃, hn₄ 63 (by omega),
      e₃ 63 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), g63]; omega
  · config_simp; rw [hn₄ 74 (by omega), g74₃, hn₄ 63 (by omega),
      e₃ 63 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), g63,
      hn₄ 72 (by omega), e₃ 72 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), g72]; omega
  · config_simp; rw [hn₄ 74 (by omega), g74₃, hn₄ 63 (by omega),
      e₃ 63 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), g63,
      hn₄ 72 (by omega), e₃ 72 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), g72, hn₄ 69 (by omega), e₃ 69 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), g69]; omega
  generalize hc₅ : (Config.mk _ _ _ _ _ _ : Config) = c₅
  have hw₅ : WordsBounded W c₅ := hc₅ ▸ ‹_›
  have e₅ : ∀ r', r' < 80 → r' ≠ 74 → r' ≠ 75 → r' ≠ 76 → r' ≠ 78 → c₅.nreg r' = c₄.nreg r' :=
    fun r' _ a b d e => by
      rw [← hc₅]; config_simp
      rw [upd_other _ _ _ b, upd_other _ _ _ e, upd_other _ _ _ a, upd_other _ _ _ d]
  have c4 : ∀ r', r' < 80 → r' ≠ 70 → r' ≠ 71 → r' ≠ 73 → r' ≠ 74 → r' ≠ 78 → r' ≠ 79 →
      c₄.nreg r' = c.nreg r' := fun r' h0 a b d e f g => by rw [hn₄ r' h0]; exact e₃ r' a b d e f g
  have g63₄ : c₄.nreg 63 = 1 := by rw [c4 63 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega), g63]
  have g72₄ : c₄.nreg 72 = 2 * s := by rw [c4 72 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega), g72]
  have g69₄ : c₄.nreg 69 = base := by rw [c4 69 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega), g69]
  have g74₅ : c₅.nreg 74 = ptr + 1 := by
    rw [← hc₅]; config_simp; rw [hn₄ 74 (by omega), g74₃, g63₄]
  have g75₅ : c₅.nreg 75 = L (ptr + 1) := by
    rw [← hc₅]; config_simp
    rw [hn₄ 74 (by omega), g74₃, g63₄, g72₄, g69₄, hnm₄, hm₃, Nat.add_comm, hmem _ hptrlen]
  have g76₅ : c₅.nreg 76 = L ptr := by
    rw [← hc₅]; config_simp; rw [hn₄ 71 (by omega), g71₃]
  have v₅ : c₅.rreg 71 = A (r - 1) (L ptr) := by rw [← hc₅]; config_simp; exact hv₄
  have hm₅ : c₅.nmem = c.nmem := by rw [← hc₅]; config_simp; rw [hnm₄, hm₃]
  have hrm₅ : c₅.rmem = c.rmem := by rw [← hc₅]; config_simp; rw [hrm₄, hrm₃]
  have ho₅ : c₅.output = c.output := by rw [← hc₅]; config_simp; rw [ho₄, ho₃]
  have hrr₅ : ∀ r' < 80, r' ≠ 70 → r' ≠ 71 → c₅.rreg r' = c.rreg r' := fun r' h0 a b => by
    rw [← hc₅]; config_simp; rw [upd_other _ _ _ b, hr₄ r' h0 a, hrr₃]
  have A₅ : Agree pb K c₀ c₅ := hI.agree.of_eq (fun r' hr' => by
      rw [e₅ r' (by omega) (by omega) (by omega) (by omega) (by omega),
        c4 r' (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)])
    (fun r' hr' => hrr₅ r' (by omega) (by omega) (by omega)) hm₅ hrm₅ ho₅
  -- step 6: the scan
  have hLm₅ : ∀ k ≤ len, c₅.nmem (base + k * (2 * s)) = L k := fun k hk => by
    rw [hm₅]; exact hmem k hk
  refine spec_seq ?_
  obtain ⟨c₆, k₆, ex₆, I₆, hn₆, hk₆⟩ := whileLtN_potential' (P := P) (W := W) (a := 75) (b := 73)
    (body := scanL ent) (ISL W A pb K L len (r - 1) ptr h c₀ c₅)
    (fun c => (E + 10) * (len - c.nreg 74)) (fun c h => h.wb)
    (fun c' hc' hlt' => scanL_exec hent hU.cols hLm₅ hR hhn
      (by rw [e₅ 70 (by omega) (by omega) (by omega) (by omega) (by omega), hn₄ 70 (by omega)]
          exact g70₃)
      (by rw [e₅ 63 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact g63₄)
      (by rw [e₅ 69 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact g69₄)
      (by rw [e₅ 72 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact g72₄)
      (by rw [e₅ 73 (by omega) (by omega) (by omega) (by omega) (by omega), hn₄ 73 (by omega)]
          exact g73₃) hwlen (by omega) c' hc' hlt')
    (c := c₅) ⟨hw₅, A₅, fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl, rfl,
      by rw [g74₅]; omega, by rw [g74₅]; omega, by rw [g75₅, g74₅],
      fun i h1 h2 => by rw [g74₅] at h2; rw [show i = ptr by omega]; omega,
      ⟨ptr, by rw [g74₅, Nat.add_sub_cancel]; exact isLMin_self _ _, g76₅, v₅⟩⟩
  refine ⟨c₆, k₆, ex₆, ?_⟩
  have hw₆ := I₆.wb
  generalize hcur : c₆.nreg 74 = cur at hk₆
  have hcur' := I₆.cur
  rw [hcur] at hcur'
  have hend : h ≤ L cur := by
    rw [not_lt, I₆.nreg 73 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      e₅ 73 (by omega) (by omega) (by omega) (by omega) (by omega), hn₄ 73 (by omega), g73₃,
      I₆.col, hcur] at hn₆
    exact hn₆
  obtain ⟨bp, hbp, hb76, hb71⟩ := I₆.best
  rw [hcur] at hbp
  obtain ⟨hbpe, hcurlen⟩ := interp_eq hU.cols histar hptrle hLstar hptrlo hstarh hhn
    (fun i h1 h2 => I₆.below i h1 (by rw [hcur]; exact h2)) hend hbp
  subst hbpe
  -- step 7: store the result, move to the next row
  have f6 : ∀ r', r' < 80 → r' ≠ 70 → r' ≠ 71 → r' ≠ 73 → r' ≠ 74 → r' ≠ 75 → r' ≠ 76 →
      r' ≠ 78 → r' ≠ 79 → c₆.nreg r' = c.nreg r' := fun r' h0 a b d e f g i j => by
    rw [I₆.nreg r' h0 b e f g i, e₅ r' h0 e f g i]
    exact c4 r' h0 a b d e i j
  have g62₆ : c₆.nreg 62 = pb := by rw [f6 62 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega), g62]
  have g67₆ : c₆.nreg 67 = r := by rw [f6 67 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega), hr]
  have g63₆ : c₆.nreg 63 = 1 := by rw [f6 63 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega), g63]
  have g72₆ : c₆.nreg 72 = 2 * s := by rw [f6 72 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega), g72]
  have hm₆ : c₆.nmem = c.nmem := by rw [I₆.nmem, hm₅]
  have hrm₆ : c₆.rmem = c.rmem := by rw [I₆.rmem, hrm₅]
  exec_block
  · config_simp; simp only [g62₆, g67₆, g72₆]; omega
  · config_simp; simp only [g62₆, g67₆, g72₆]; omega
  have hpbr : pb < pb + r ∧ pb + r ≤ pb + K := ⟨by omega, by have := hU.mK; omega⟩
  refine ⟨⟨‹_›, ?_, fun r' h0 a b d e f g i j k' l o => ?_, fun r' h0 a b => ?_, fun a ha => ?_,
    fun a ha => ?_, ?_, ?_, ?_, ?_, ?_, fun r' h1 h2 hr' => ?_⟩, ?_⟩
  · obtain ⟨a1, a2, a3, a4, a5⟩ := I₆.agree
    refine ⟨fun r' hr' => ?_, fun r' hr' => ?_, fun a ha => ?_, fun a ha => ?_, ?_⟩
    · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact a1 r' hr'
    · config_simp; exact a2 r' hr'
    · config_simp; rw [g62₆, g67₆, upd_other _ _ _ (by omega)]; exact a3 a ha
    · config_simp; rw [g62₆, g67₆, upd_other _ _ _ (by omega)]; exact a4 a ha
    · config_simp; exact a5
  · config_simp
    rw [upd_other _ _ _ a, upd_other _ _ _ b, upd_other _ _ _ l]
    rw [f6 r' h0 d e f g i j l o]; exact hI.nreg r' h0 a b d e f g i j k' l o
  · config_simp; rw [I₆.rreg r' h0 a b, hrr₅ r' h0 a b]; exact hI.rreg r' h0 a b
  · config_simp; rw [g62₆, g67₆, upd_other _ _ _ (by omega), hm₆]; exact hI.nmem a ha
  · config_simp; rw [g62₆, g67₆, upd_other _ _ _ (by omega), hrm₆]; exact hI.rmem a ha
  · config_simp; rw [I₆.out, ho₅]; exact hI.out
  · config_simp; rw [g67₆, g72₆]; exact ⟨u + 1, by rw [hu]; ring⟩
  · config_simp; rw [g67₆, g72₆]; omega
  · config_simp; rw [hcur, g63₆]; omega
  · config_simp
    rw [g67₆, g72₆, hcur, g63₆]
    intro hle
    refine Or.inr ⟨by omega, ?_⟩
    rw [show r + 2 * s - s - 1 = r + s - 1 by omega]
    have hrs : r + s ≤ m := by omega
    have e1 : (2 * u + 1 + 1) * s = r + s := by rw [hrow]; ring
    obtain ⟨q, hq, hLq⟩ := hU.minRow (k := 2 * u + 1) (by rw [e1]; exact hrs)
    rw [e1] at hLq
    have hmono : lmin n A (r - 1) ≤ lmin n A (r + s - 1) :=
      hA.lmin_mono (by omega) (by omega) hn
    have hlq : L ptr ≤ L q := by
      refine hptrlo.trans ?_
      rw [hLq, hLstar]; exact hmono
    have hnx := interp_next hU.cols hq hptrle (h := h) (by rw [hLq, ← hhv, ite_eq_left hrs]) hlq
      (fun i h1 h2 => I₆.below i h1 (by rw [hcur]; exact h2)) hend hcur'
    rw [hnx, hLq]
  · unfold Done
    config_simp
    rw [g62₆, g67₆]
    rw [g67₆, g72₆] at hr'
    by_cases hrr : r' = r
    · subst hrr
      simp only [upd_same]
      refine ⟨by rw [hb76, hLstar], by rw [hb71, hLstar]⟩
    · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), hm₆, hrm₆]
      refine hI.done r' h1 h2 ?_
      rw [hr]
      rcases hr' with hr' | ⟨hd, hr'⟩
      · exact Or.inl hr'
      · by_cases h2s : 2 * s ∣ r'
        · exact Or.inl h2s
        · refine Or.inr ⟨hd, ?_⟩
          have hr'' : r' < s + 2 * s * u + 2 * s := by rw [← hu]; exact hr'
          rw [hu] at hrr ⊢
          exact odd_mul_lt hs hd hr'' hrr h2s
  · config_simp
    rw [g67₆, g72₆, hcur, g63₆]
    have q1 : m + 2 * s - (r + 2 * s) = m - r := by omega
    have q2 : (m + 2 * s - r) / (2 * s) = (m - r) / (2 * s) + 1 := by
      rw [show m + 2 * s - r = m - r + 2 * s by omega, Nat.add_div_right _ (by omega)]
    have q3 : (E + 10) * (len - ptr) = (E + 10) * (len - (cur - 1)) + (E + 10) * (cur - 1 - ptr) := by
      rw [← Nat.mul_add]; congr 1; omega
    rw [q1, q2, q3, Nat.mul_add, Nat.mul_one]
    have q4 : (E + 10) * (len - (ptr + 1)) = (E + 10) * (len - cur) + (E + 10) * (cur - 1 - ptr) := by
      rw [← Nat.mul_add]; congr 1; omega
    have q5 : (E + 10) * (len - (cur - 1)) = (E + 10) * (len - cur) + (E + 10) := by
      rw [show len - (cur - 1) = len - cur + 1 by omega, Nat.mul_add, Nat.mul_one]
    beta_reduce at hk₆
    rw [g74₅, q4] at hk₆
    omega

/-! ### One level -/

/-- **The interpolation of one level on the machine.** With the rows divisible by `2s` done and
the reduced list `L` of the level in memory, `upRows ent` does the rows divisible by `s`, within
`(E + 30) ⌊(m + s) / 2s⌋ + (E + 10) len + 4` steps. -/
theorem upRows_exec (hent : EntSpecK P W ent A E m n pb K c₀) (hA : IsTotMono m n A)
    {s len base : ℕ} {L : ℕ → ℕ} {cS : Config} (hU : UpData W A m n pb K s len base L cS)
    (hw : WordsBounded W cS) (hag : Agree pb K c₀ cS)
    (hdone : ∀ r, 1 ≤ r → r ≤ m → 2 * s ∣ r → Done A n pb cS r) :
    ∃ c' k, Exec P W (upRows ent) cS c' k ∧
      k ≤ (E + 30) * ((m + s) / (2 * s)) + (E + 10) * len + 4 ∧
      (Agree pb K c₀ c' ∧
        (∀ r < 80, r ≠ 67 → r ≠ 68 → r ≠ 70 → r ≠ 71 → r ≠ 73 → r ≠ 74 → r ≠ 75 → r ≠ 76 →
          r ≠ 77 → r ≠ 78 → r ≠ 79 → c'.nreg r = cS.nreg r) ∧
        (∀ r < 80, r ≠ 70 → r ≠ 71 → c'.rreg r = cS.rreg r) ∧
        (∀ a, (a ≤ pb ∨ pb + m < a) → c'.nmem a = cS.nmem a) ∧
        (∀ a, (a ≤ pb ∨ pb + m < a) → c'.rmem a = cS.rmem a) ∧ c'.output = cS.output ∧
        ∀ r, 1 ≤ r → r ≤ m → s ∣ r → Done A n pb c' r) := by
  have hs := hU.spos
  have hsm := hU.sle
  have hw3 := hU.w3
  unfold upRows
  refine spec_seq ?_
  exec_block
  · omega
  refine spec_while (IU W A m n pb K s len L c₀ cS)
    (fun c => (E + 30) * ((m + 2 * s - c.nreg 67) / (2 * s)) + (E + 10) * (len - c.nreg 68))
    (fun c h => h.wb) (fun c' hc' hlt' => upRow_exec hent hA hU c' hc' hlt')
    ⟨‹_›, hag.of_eq (fun r hr => by config_simp; upd_tac) (fun _ _ => rfl) rfl rfl rfl,
      fun r _ a b _ _ _ _ _ _ _ _ _ => by config_simp; upd_tac, fun _ _ _ _ => rfl,
      fun _ _ => rfl, fun _ _ => rfl, rfl, ⟨0, by config_simp; rw [hU.r65]; ring⟩,
      by config_simp; rw [hU.r65]; omega, by config_simp; omega,
      fun _ => Or.inl ⟨by config_simp; rw [hU.r65], by config_simp⟩,
      fun r h1 h2 hr => ?_⟩ ?_
  · config_simp at hr
    rw [hU.r65] at hr
    rcases hr with hr | ⟨hd, hr⟩
    · obtain ⟨d1, d2⟩ := hdone r h1 h2 hr
      exact ⟨d1, d2⟩
    · obtain ⟨v, rfl⟩ := hd
      rcases Nat.eq_zero_or_pos v with hv | hv
      · rw [hv] at h1; omega
      · have : s * 1 ≤ s * v := Nat.mul_le_mul_left _ hv
        omega
  intro c₂ k₂ hI₂ hn₂ hk₂
  have g66 : c₂.nreg 66 = m + 1 := (hI₂.reg (by omega)).trans hU.r66
  rw [g66] at hn₂
  refine ⟨?_, hI₂.agree, hI₂.nreg, hI₂.rreg, hI₂.nmem, hI₂.rmem, hI₂.out,
    fun r h1 h2 hr => hI₂.done r h1 h2 ?_⟩
  · beta_reduce at hk₂
    config_simp at hk₂
    rw [hU.r65, Nat.sub_zero, show m + 2 * s - s = m + s by omega] at hk₂
    omega
  · by_cases h2s : 2 * s ∣ r
    · exact Or.inl h2s
    · exact Or.inr ⟨hr, by omega⟩

end Monge

end PlanarFlow
