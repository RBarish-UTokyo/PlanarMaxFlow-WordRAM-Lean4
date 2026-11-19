module

public import PlanarFlow.BKMNW.MbBaseB

/-!
# Miller's base, stage C: the keys, the marks, the flags and the labels

`mbC := mbP6 ; tks ; mbP7 ; mzFill ; mbP8 ; kmk ; mbP9 ; lbl ; mbFin`: the keys of the compacted
darts `TKc[RK[i]] := TK[i]` at `Hb + 7 n` (`tks`), `KM` zeroed at `Hb + 12 n` (`mzFill`), the marks
of the cycle codes (`kmk`, codes at `Hb + 8 n`, reverses at `Hb + 4 n`), the new-hole flags at
`NHb` and the labels at `ITEMb` (`lbl`, face marks at `Hb + 11 n`, `z = r643`,
`one = [r644 = 1]`), then `r4970 := 1`, `r4944 := 3`, `r4943 := NHb`, `r4502 := ITEMb`.

* `mbP6` … `mbP9`, `mbFin`, **`mbC`**, the block lemmas, **`mbC_exec`** (`83 n + 17 k + 70`
  steps).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- The registers of the scatter of the keys. -/
def mbP6 : Stmt :=
  block [.copyN 5110 5000, .copyN 5111 4841, .copyN 5112 5004, .constN 5214 6,
    .mulN 5215 5000 5214, .addN 5113 4841 5215, .constN 5214 7, .mulN 5215 5000 5214,
    .addN 5114 5004 5215]

/-- The registers of the zeroing of `KM`. -/
def mbP7 : Stmt :=
  block [.copyN 5030 5000, .constN 5214 12, .mulN 5215 5000 5214, .addN 5031 5004 5215]

/-- The registers of the marks. -/
def mbP8 : Stmt :=
  block [.copyN 5130 641, .constN 5214 8, .mulN 5215 5000 5214, .addN 5131 5004 5215,
    .copyN 5132 5114, .constN 5214 4, .mulN 5215 5000 5214, .addN 5133 5004 5215,
    .copyN 5134 5031]

/-- The registers of the labels (`one = 1 - ((r644 - 1) + (1 - r644))`). -/
def mbP9 : Stmt :=
  block [.copyN 5150 5000, .copyN 5151 4841, .copyN 5152 5113, .copyN 5153 5031,
    .copyN 5154 5004, .constN 5214 11, .mulN 5215 5000 5214, .addN 5155 5004 5215,
    .copyN 5156 4843, .copyN 5157 4956, .copyN 5158 4955, .copyN 5159 643, .constN 5214 1,
    .subN 5215 644 5214, .subN 5216 5214 644, .addN 5215 5215 5216, .subN 5160 5214 5215]

/-- The result registers of the base. -/
def mbFin : Stmt := block [.constN 4970 1, .constN 4944 3, .copyN 4943 4956, .copyN 4502 4955]

/-- **Stage C of Miller's base.** -/
def mbC : Stmt :=
  .seq mbP6 (.seq tks (.seq mbP7 (.seq mzFill (.seq mbP8 (.seq kmk (.seq mbP9 (.seq lbl mbFin)))))))

/-- The registers stage C keeps. -/
def MbCFr (x : ℕ) : Prop :=
  x < 4502 ∨ (4502 < x ∧ x < 4943) ∨ (4944 < x ∧ x < 4970) ∨ (4970 < x ∧ x < 5030) ∨
    (5035 < x ∧ x < 5110) ∨ (5120 < x ∧ x < 5130) ∨ (5142 < x ∧ x < 5150) ∨
    (5182 < x ∧ x < 5214) ∨ 5216 < x

section Exec

variable {P : Input} {W : ℕ}

theorem mbP6_exec (c : Config) (hc : WordsBounded W c) {n b Hb : ℕ}
    (r0 : c.nreg 5000 = n) (r41 : c.nreg 4841 = b) (r4 : c.nreg 5004 = Hb)
    (w : b + 6 * n ≤ W ∧ Hb + 7 * n ≤ W ∧ 7 ≤ W) :
    ∃ c' t, Exec P W mbP6 c c' t ∧ t = 9 ∧ c'.nreg 5110 = n ∧ c'.nreg 5111 = b ∧
      c'.nreg 5112 = Hb ∧ c'.nreg 5113 = b + 6 * n ∧ c'.nreg 5114 = Hb + 7 * n ∧
      c'.nmem = c.nmem ∧ (∀ x, (x < 5110 ∨ (5114 < x ∧ x < 5214) ∨ 5215 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨w1, w2, w3⟩ := w
  have h6 : n * 6 = 6 * n := by ring
  have h7 : n * 7 = 7 * n := by ring
  unfold mbP6
  exec_block
  all_goals try (config_simp; (try simp only [r0, r41, r4, h6, h7]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r0, r41, r4, h6, h7]); done)
  all_goals try (config_simp; (try simp only [r0, r41, r4, h6, h7]); omega)
  · config_simp; simp (disch := omega) only [upd_other]

theorem mbP7_exec (c : Config) (hc : WordsBounded W c) {n Hb : ℕ}
    (r0 : c.nreg 5000 = n) (r4 : c.nreg 5004 = Hb) (w : Hb + 12 * n ≤ W ∧ 12 ≤ W) :
    ∃ c' t, Exec P W mbP7 c c' t ∧ t = 4 ∧ c'.nreg 5030 = n ∧ c'.nreg 5031 = Hb + 12 * n ∧
      c'.nmem = c.nmem ∧
      (∀ x, x ≠ 5030 → x ≠ 5031 → x ≠ 5214 → x ≠ 5215 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨w1, w2⟩ := w
  have h12 : n * 12 = 12 * n := by ring
  unfold mbP7
  exec_block
  all_goals try (config_simp; (try simp only [r0, r4, h12]); omega)
  refine ⟨rfl, ?_, ?_, rfl, fun x a1 a2 a3 a4 => ?_, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r0, r4, h12]); done)
  all_goals try (config_simp; (try simp only [r0, r4, h12]); omega)
  · config_simp; simp (disch := omega) only [upd_other]

theorem mbP8_exec (c : Config) (hc : WordsBounded W c) {n Hb k : ℕ}
    (r0 : c.nreg 5000 = n) (r4 : c.nreg 5004 = Hb) (r41 : c.nreg 641 = k)
    (r14 : c.nreg 5114 = Hb + 7 * n) (r31 : c.nreg 5031 = Hb + 12 * n)
    (w : Hb + 8 * n ≤ W ∧ 8 ≤ W) :
    ∃ c' t, Exec P W mbP8 c c' t ∧ t = 9 ∧ c'.nreg 5130 = k ∧ c'.nreg 5131 = Hb + 8 * n ∧
      c'.nreg 5132 = Hb + 7 * n ∧ c'.nreg 5133 = Hb + 4 * n ∧ c'.nreg 5134 = Hb + 12 * n ∧
      c'.nmem = c.nmem ∧ (∀ x, (x < 5130 ∨ (5134 < x ∧ x < 5214) ∨ 5215 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨w1, w2⟩ := w
  have h8 : n * 8 = 8 * n := by ring
  have h4 : n * 4 = 4 * n := by ring
  unfold mbP8
  exec_block
  all_goals try (config_simp; (try simp only [r0, r4, r41, r14, r31, h8, h4]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r0, r4, r41, r14, r31, h8, h4]); done)
  all_goals try (config_simp; (try simp only [r0, r4, r41, r14, r31, h8, h4]); omega)
  · config_simp; simp (disch := omega) only [upd_other]

theorem mbP9_exec (c : Config) (hc : WordsBounded W c) {n b Hb NHb ITb z z44 : ℕ}
    (r0 : c.nreg 5000 = n) (r41 : c.nreg 4841 = b) (r43 : c.nreg 4843 = b + 2 * n)
    (r4 : c.nreg 5004 = Hb) (r13 : c.nreg 5113 = b + 6 * n) (r31 : c.nreg 5031 = Hb + 12 * n)
    (r56 : c.nreg 4956 = NHb) (r55 : c.nreg 4955 = ITb) (r643 : c.nreg 643 = z)
    (r644 : c.nreg 644 = z44) (w : Hb + 11 * n ≤ W ∧ 11 ≤ W) :
    ∃ c' t, Exec P W mbP9 c c' t ∧ t = 17 ∧ c'.nreg 5150 = n ∧ c'.nreg 5151 = b ∧
      c'.nreg 5152 = b + 6 * n ∧ c'.nreg 5153 = Hb + 12 * n ∧ c'.nreg 5154 = Hb ∧
      c'.nreg 5155 = Hb + 11 * n ∧ c'.nreg 5156 = b + 2 * n ∧ c'.nreg 5157 = NHb ∧
      c'.nreg 5158 = ITb ∧ c'.nreg 5159 = z ∧
      c'.nreg 5160 = 1 - ((z44 - 1) + (1 - z44)) ∧
      c'.nmem = c.nmem ∧ (∀ x, (x < 5150 ∨ (5160 < x ∧ x < 5214) ∨ 5216 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨w1, w2⟩ := w
  have h11 : n * 11 = 11 * n := by ring
  have hz44 : z44 ≤ W := by rw [← r644]; exact hc.1 _
  unfold mbP9
  exec_block
  all_goals try (config_simp; (try simp only [r0, r41, r43, r4, r13, r31, r56, r55, r643, r644, h11]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r0, r41, r43, r4, r13, r31, r56, r55, r643, r644, h11]); done)
  all_goals try (config_simp; (try simp only [r0, r41, r43, r4, r13, r31, r56, r55, r643, r644, h11]); omega)
  · config_simp; simp (disch := omega) only [upd_other]

theorem mbFin_exec (c : Config) (hc : WordsBounded W c) {NHb ITb : ℕ}
    (r56 : c.nreg 4956 = NHb) (r55 : c.nreg 4955 = ITb) (w : 3 ≤ W) :
    ∃ c' t, Exec P W mbFin c c' t ∧ t = 4 ∧ c'.nreg 4970 = 1 ∧ c'.nreg 4944 = 3 ∧
      c'.nreg 4943 = NHb ∧ c'.nreg 4502 = ITb ∧ c'.nmem = c.nmem ∧
      (∀ x, x ≠ 4970 → x ≠ 4944 → x ≠ 4943 → x ≠ 4502 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold mbFin
  exec_block
  all_goals try (config_simp; (try simp only [r56, r55]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, fun x a1 a2 a3 a4 => ?_, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r56, r55]); done)
  · config_simp; simp (disch := omega) only [upd_other]

set_option maxHeartbeats 1600000 in
/-- **Stage C**: from the flags `NF` at `b`, the reverses at `b + 2n`, the keys `TK` at `b + 6n`,
the ranks at `Hb` (injective on the flagged indices, onto `[0, mN)`), the compacted reverses at
`Hb + 4n`, the `k` cycle codes at `Hb + 8n` and the face marks at `Hb + 11n`, within
`83 n + 17 k + 70` steps: the memory `m₂` after the scatter (keys `TKc` at `Hb + 7n`), the marks
`KM` at `Hb + 12 n` (`kmHit` on `m₂`), the flags `NH[i] = KM[TK[i]]`, the labels `lbV …`
(flagged) or `0` at `ITEMb`; `r4970 = 1`, `r4944 = 3`, `r4943 = NHb`, `r4502 = ITEMb`; memory
below `Hb + 7n` off the two outputs kept; registers `MbCFr` kept. -/
theorem mbC_exec (c : Config) (hc : WordsBounded W c) {n b Hb k z z44 ITb NHb mN : ℕ}
    (r00 : c.nreg 5000 = n) (r41 : c.nreg 4841 = b) (r43 : c.nreg 4843 = b + 2 * n)
    (r04 : c.nreg 5004 = Hb) (r641 : c.nreg 641 = k) (r643 : c.nreg 643 = z)
    (r644 : c.nreg 644 = z44) (r55 : c.nreg 4955 = ITb) (r56 : c.nreg 4956 = NHb)
    (lay : b + 7 * n ≤ ITb ∧ ITb + n ≤ NHb ∧ NHb + n ≤ Hb ∧ Hb + 13 * n ≤ W ∧ k ≤ 3 * n ∧
      mN ≤ n ∧ 12 ≤ W)
    (hTK : ∀ i < n, c.nmem (b + 6 * n + i) < n) (hRV : ∀ i < n, c.nmem (b + 2 * n + i) < n)
    (hRK : ∀ i < n, c.nmem (b + i) ≠ 0 →
      c.nmem (Hb + i) < mN ∧ c.nmem (Hb + c.nmem (b + 2 * n + i)) < mN)
    (hinj : ∀ i < n, ∀ j < n, c.nmem (b + i) ≠ 0 → c.nmem (b + j) ≠ 0 →
      c.nmem (Hb + i) = c.nmem (Hb + j) → i = j)
    (hsurj : ∀ q < mN, ∃ i < n, c.nmem (b + i) ≠ 0 ∧ c.nmem (Hb + i) = q)
    (hCY : ∀ l < k, c.nmem (Hb + 8 * n + l) < 3 * mN)
    (hCR : ∀ q < mN, c.nmem (Hb + 4 * n + q) < mN) :
    ∃ c' t, Exec P W mbC c c' t ∧ t ≤ 83 * n + 17 * k + 70 ∧
      (∃ m₂ : ℕ → ℕ, (∀ i < n, c.nmem (b + i) ≠ 0 →
          m₂ (Hb + 7 * n + c.nmem (Hb + i)) = c.nmem (b + 6 * n + i)) ∧
        (∀ a, (a < Hb + 7 * n ∨ (Hb + 7 * n + mN ≤ a ∧ a < Hb + 12 * n)) → m₂ a = c.nmem a) ∧
        (∀ x < n, (c'.nmem (Hb + 12 * n + x) ≠ 0 ↔
          ∃ l < k, kmHit m₂ (Hb + 8 * n) (Hb + 7 * n) (Hb + 4 * n) l x))) ∧
      (∀ i < n, c'.nmem (NHb + i) = c'.nmem (Hb + 12 * n + c.nmem (b + 6 * n + i))) ∧
      (∀ i < n, c'.nmem (ITb + i) = if c.nmem (b + i) ≠ 0 then
          lbV (c'.nmem (Hb + 12 * n + c.nmem (b + 6 * n + i)))
            (c.nmem (Hb + 11 * n + c.nmem (Hb + i)))
            (c'.nmem (Hb + 12 * n + c.nmem (b + 6 * n + c.nmem (b + 2 * n + i))))
            (c.nmem (Hb + 11 * n + c.nmem (Hb + c.nmem (b + 2 * n + i)))) z
            (1 - ((z44 - 1) + (1 - z44)))
        else 0) ∧
      (∀ a, a < Hb + 7 * n → ¬ (ITb ≤ a ∧ a < ITb + n) → ¬ (NHb ≤ a ∧ a < NHb + n) →
        c'.nmem a = c.nmem a) ∧
      c'.nreg 4970 = 1 ∧ c'.nreg 4944 = 3 ∧ c'.nreg 4943 = NHb ∧ c'.nreg 4502 = ITb ∧
      (∀ x, MbCFr x → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := lay
  set m := c.nmem with hm
  -- the scatter
  obtain ⟨c₁, t₁, e₁, ht₁, a10, a11, a12, a13, a14, am₁, an₁, ar₁, arm₁, ao₁⟩ :=
    mbP6_exec (P := P) c hc r00 r41 r04 ⟨by omega, by omega, by omega⟩
  have hw₁ := e₁.wb_right
  obtain ⟨c₂, t₂, e₂, ht₂, g1, gm₂, gn₂, gr₂, grm₂, go₂⟩ :=
    tks_exec (P := P) c₁ hw₁ (m := mN) a10 a11 a12 a13 a14
      ⟨by omega, by omega, by omega, by omega, by omega⟩
      (fun i hi h => by rw [am₁] at h ⊢; exact (hRK i hi h).1)
      (fun i hi j hj h1 h2 h3 => by rw [am₁] at h1 h2 h3; exact hinj i hi j hj h1 h2 h3)
  have hw₂ := e₂.wb_right
  rw [am₁] at g1 gm₂
  -- zeroing `KM`
  have q2 : ∀ x, (x < 5110 ∨ (5120 < x ∧ x < 5214) ∨ 5215 < x) → c₂.nreg x = c.nreg x :=
    fun x hx => by rw [gn₂ x (by omega), an₁ x (by omega)]
  obtain ⟨c₃, t₃, e₃, ht₃, b30, b31, bm₃, bn₃, br₃, brm₃, bo₃⟩ :=
    mbP7_exec (P := P) c₂ hw₂ (n := n) (Hb := Hb) (by rw [q2 _ (by omega), r00])
      (by rw [q2 _ (by omega), r04]) ⟨by omega, by omega⟩
  have hw₃ := e₃.wb_right
  obtain ⟨c₄, t₄, e₄, ht₄, z1, zm₄, zn₄, zr₄, zrm₄, zo₄⟩ :=
    mzFill_exec (P := P) c₃ hw₃ b30 b31 (by omega) (by omega)
  have hw₄ := e₄.wb_right
  have hm₂a : ∀ a, (a < Hb + 7 * n ∨ Hb + 7 * n + mN ≤ a) → ¬ (Hb + 12 * n ≤ a ∧ a < Hb + 13 * n) →
      c₄.nmem a = m a := fun a h1 h2 => by
    rw [zm₄ a (by omega), bm₃, gm₂ a h1]
  have hm₂t : ∀ i < n, m (b + i) ≠ 0 → c₄.nmem (Hb + 7 * n + m (Hb + i)) = m (b + 6 * n + i) :=
    fun i hi h => by
      have := (hRK i hi h).1
      rw [zm₄ _ (by omega), bm₃, g1 i hi h]
  have q4 : ∀ x, MbCFr x → c₄.nreg x = c.nreg x := fun x hx => by
    unfold MbCFr at hx
    rw [zn₄ x (by omega), bn₃ x (by omega) (by omega) (by omega) (by omega), q2 x (by omega)]
  -- the marks
  obtain ⟨c₅, t₅, e₅, ht₅, d30, d31, d32, d33, d34, dm₅, dn₅, dr₅, drm₅, do₅⟩ :=
    mbP8_exec (P := P) c₄ hw₄ (n := n) (Hb := Hb) (k := k)
      (by rw [q4 _ (by unfold MbCFr; omega), r00]) (by rw [q4 _ (by unfold MbCFr; omega), r04])
      (by rw [q4 _ (by unfold MbCFr; omega), r641])
      (by rw [zn₄ _ (by omega), bn₃ _ (by omega) (by omega) (by omega) (by omega),
        gn₂ _ (by omega), a14])
      (by rw [zn₄ _ (by omega), b31]) ⟨by omega, by omega⟩
  have hw₅ := e₅.wb_right
  obtain ⟨c₆, t₆, e₆, ht₆, kM, km₆, kn₆, kr₆, krm₆, ko₆⟩ :=
    kmk_exec (P := P) c₅ hw₅ (m := mN) (n := n) d30 d31 d32 d33 d34
      ⟨by omega, by omega, by omega, by omega, by omega⟩
      (fun l hl => by rw [dm₅, hm₂a _ (Or.inr (by omega)) (by omega)]; exact hCY l hl)
      (fun q hq => by rw [dm₅, hm₂a _ (Or.inl (by omega)) (by omega)]; exact hCR q hq)
      (fun q hq => by
        obtain ⟨i, hi, hf, rfl⟩ := hsurj q hq
        rw [dm₅, hm₂t i hi hf]; exact hTK i hi)
      (fun x hx => by rw [dm₅, z1 x hx])
  have hw₆ := e₆.wb_right
  rw [dm₅] at kM
  -- the labels
  have q6 : ∀ x, MbCFr x → (x < 5130 ∨ 5142 < x) → c₆.nreg x = c.nreg x := fun x hx h => by
    rw [kn₆ x (by omega), dn₅ x (by unfold MbCFr at hx; omega), q4 x hx]
  obtain ⟨c₇, t₇, e₇, ht₇, p50, p51, p52, p53, p54, p55, p56, p57, p58, p59, p60, pm₇, pn₇, pr₇,
      prm₇, po₇⟩ :=
    mbP9_exec (P := P) c₆ hw₆ (n := n) (b := b) (Hb := Hb) (NHb := NHb) (ITb := ITb) (z := z)
      (z44 := z44)
      (by rw [q6 _ (by unfold MbCFr; omega) (by omega), r00])
      (by rw [q6 _ (by unfold MbCFr; omega) (by omega), r41])
      (by rw [q6 _ (by unfold MbCFr; omega) (by omega), r43])
      (by rw [q6 _ (by unfold MbCFr; omega) (by omega), r04])
      (by rw [kn₆ _ (by omega), dn₅ _ (by omega), zn₄ _ (by omega),
        bn₃ _ (by omega) (by omega) (by omega) (by omega), gn₂ _ (by omega), a13])
      (by rw [kn₆ _ (by omega), dn₅ _ (by omega), zn₄ _ (by omega), b31])
      (by rw [q6 _ (by unfold MbCFr; omega) (by omega), r56])
      (by rw [q6 _ (by unfold MbCFr; omega) (by omega), r55])
      (by rw [q6 _ (by unfold MbCFr; omega) (by omega), r643])
      (by rw [q6 _ (by unfold MbCFr; omega) (by omega), r644]) ⟨by omega, by omega⟩
  have hw₇ := e₇.wb_right
  -- the memory before the labels
  have hm₆ : ∀ a, (a < Hb + 7 * n ∨ (Hb + 7 * n + mN ≤ a ∧ a < Hb + 12 * n)) →
      c₇.nmem a = m a := fun a ha => by
    rw [pm₇, km₆ a (by omega), dm₅, hm₂a a (by omega) (by omega)]
  have hKM : ∀ x, x < n → c₇.nmem (Hb + 12 * n + x) = c₆.nmem (Hb + 12 * n + x) :=
    fun x _ => by rw [pm₇]
  obtain ⟨c₈, t₈, e₈, ht₈, f1, f2, fm₈, fn₈, fr₈, frm₈, fo₈⟩ :=
    lbl_exec (P := P) c₇ hw₇ (m := mN) p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega, by omega⟩
      (fun i hi => by rw [hm₆ _ (by omega)]; exact hTK i hi)
      (fun i hi => by rw [hm₆ _ (by omega)]; exact hRV i hi)
      (fun i hi h => by
        rw [hm₆ _ (by omega)] at h
        obtain ⟨h1, h2⟩ := hRK i hi h
        have hr := hRV i hi
        rw [hm₆ (Hb + i) (by omega), hm₆ (b + 2 * n + i) (by omega),
          hm₆ (Hb + m (b + 2 * n + i)) (by omega)]
        exact ⟨h1, h2⟩)
  have hw₈ := e₈.wb_right
  have q8 : c₈.nreg 4956 = NHb := by
    rw [fn₈ _ (by omega), pn₇ _ (by omega), q6 _ (by unfold MbCFr; omega) (by omega), r56]
  have q8' : c₈.nreg 4955 = ITb := by
    rw [fn₈ _ (by omega), pn₇ _ (by omega), q6 _ (by unfold MbCFr; omega) (by omega), r55]
  obtain ⟨c₉, t₉, e₉, ht₉, u70, u44, u43, u02, um₉, un₉, ur₉, urm₉, uo₉⟩ :=
    mbFin_exec (P := P) c₈ hw₈ q8 q8' (by omega)
  -- the final memory
  have hfin : ∀ x < n, c₉.nmem (Hb + 12 * n + x) = c₇.nmem (Hb + 12 * n + x) := fun x hx => by
    rw [um₉, fm₈ _ (by omega) (by omega)]
  refine ⟨c₉, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + (t₇ + (t₈ + t₉))))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ e₉))))))),
    by omega, ⟨c₄.nmem, hm₂t, fun a ha => ?_, fun x hx => ?_⟩, fun i hi => ?_, fun i hi => ?_,
    fun a ha h1 h2 => ?_, u70, u44, u43, u02, fun x hx => ?_, ?_, ?_, ?_⟩
  · exact hm₂a a (by omega) (by omega)
  · rw [hfin x hx, hKM x hx]; exact kM x hx
  · have ht := hTK i hi
    rw [hfin _ ht, um₉, f1 i hi, hm₆ (b + 6 * n + i) (by omega)]
  · have ht := hTK i hi
    have hr := hRV i hi
    have ht' := hTK _ hr
    rw [hfin _ ht, hfin _ ht', um₉, f2 i hi, hm₆ (b + i) (by omega)]
    split_ifs with hF
    · obtain ⟨h1, h2⟩ := hRK i hi hF
      rw [hm₆ (b + 6 * n + i) (by omega), hm₆ (Hb + i) (by omega),
        hm₆ (Hb + 11 * n + m (Hb + i)) (by omega), hm₆ (b + 2 * n + i) (by omega),
        hm₆ (b + 6 * n + m (b + 2 * n + i)) (by omega), hm₆ (Hb + m (b + 2 * n + i)) (by omega),
        hm₆ (Hb + 11 * n + m (Hb + m (b + 2 * n + i))) (by omega)]
    · rfl
  · rw [um₉, fm₈ a h1 h2, hm₆ a (Or.inl ha)]
  · unfold MbCFr at hx
    rw [un₉ x (by omega) (by omega) (by omega) (by omega), fn₈ x (by omega), pn₇ x (by omega),
      q6 x (by unfold MbCFr; omega) (by omega)]
  · rw [ur₉, fr₈, pr₇, kr₆, dr₅, zr₄, br₃, gr₂, ar₁]
  · rw [urm₉, frm₈, prm₇, krm₆, drm₅, zrm₄, brm₃, grm₂, arm₁]
  · rw [uo₉, fo₈, po₇, ko₆, do₅, zo₄, bo₃, go₂, ao₁]

end Exec

end BKMNW

end PlanarFlow
