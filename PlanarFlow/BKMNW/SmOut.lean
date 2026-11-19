module

public import PlanarFlow.BKMNW.SmDsp

/-!
# One step of `smD` on the machine: the output scan

With the words of the split `s = (a, a', up, lpm, v1, v2, t1, t2)` in `5364 … 5371`
(`SmDsp.lean`), one scan `smO` over `i < n` writes, from the eight words `w` of `i` (`SmW`,
loaded by `smA1`):

* `LP[i]` at `Ob + i` (`smLPw`: a dart of the left child), `PD[i]` at `Ob + n + i` (`smPDw`: a
  dart of the path), `CV[i]` at `Ob + 2 n + i` (`smCVw`: the tail on the path);

and sums, over the darts of the left child, the bits of the child's own classification: `B'`
(`smB2w`), `X'` (`smX2w`), `Y'` (`smY2w`), inside a child hole (`smJ2w`), in `5377 … 5380`, and
`#LP` in `5376`. Registers: `5306 = Ob`, `5308 = Ob + n`, `5309 = Ob + 2 n`; written `5314`,
`5334 … 5353`, `5376 … 5399`.

* `SmW`, `smW`, `smW_congr`, `SmSV`, the arithmetic `smEaa`, `smCVf`, `smHMf` and the values
  `smLPw` … `smJ2w`;
* the blocks `smO2a` … `smO2d`, `smO3`, **`smOBody_exec`**, **`smO_exec`** (`(141 + 2) n + 8`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- The eight words of an index: its flag, its reverse, the hole labels, ranks and vertex numbers
of its tail and its head. -/
structure SmW where
  p0 : ℕ
  ri : ℕ
  t : ℕ
  h : ℕ
  kr : ℕ
  kh : ℕ
  vt : ℕ
  vh : ℕ

/-- The words of the index `i` in the memory `m`. -/
def smW (m : ℕ → ℕ) (PFb RVb THb KRb VTb i : ℕ) : SmW :=
  ⟨m (PFb + i), m (RVb + i), m (THb + i), m (THb + m (RVb + i)), m (KRb + i),
    m (KRb + m (RVb + i)), m (VTb + i), m (VTb + m (RVb + i))⟩

lemma smW_congr {m m' : ℕ → ℕ} {PFb RVb THb KRb VTb n Ob i : ℕ} (hi : i < n)
    (hrv : m (RVb + i) < n) (h1 : PFb + n ≤ Ob) (h2 : RVb + n ≤ Ob) (h3 : THb + n ≤ Ob)
    (h4 : KRb + n ≤ Ob) (h5 : VTb + n ≤ Ob) (h : ∀ a < Ob, m' a = m a) :
    smW m' PFb RVb THb KRb VTb i = smW m PFb RVb THb KRb VTb i := by
  have e : m' (RVb + i) = m (RVb + i) := h _ (by omega)
  unfold smW
  rw [h (PFb + i) (by omega), e, h (THb + i) (by omega), h _ (by omega), h (KRb + i) (by omega),
    h _ (by omega), h (VTb + i) (by omega), h _ (by omega)]

/-- The words of the split. -/
structure SmSV where
  a : ℕ
  a' : ℕ
  up : ℕ
  lpm : ℕ
  v1 : ℕ
  v2 : ℕ
  t1 : ℕ
  t2 : ℕ

/-- `i ∈ {a, a'}`. -/
abbrev smEaa (i a a' : ℕ) : ℕ := smSg (smEq i a + smEq i a')

/-- A vertex number on the path. -/
abbrev smCVf (v v1 v2 up : ℕ) : ℕ := smSg (smEq v v1 + smAnd up (smEq v v2))

/-- A hole label of a hole met by the path. -/
abbrev smHMf (t t1 t2 up : ℕ) : ℕ := smAnd (smSg t) (smSg (smEq t t1 + smAnd up (smEq t t2)))

/-- `LP`: a dart of the left child. -/
abbrev smLPw (w : SmW) (s : SmSV) (i : ℕ) : ℕ :=
  (smSg w.p0 - smAnd s.lpm (smInn w.t w.h)) - smAnd (1 - s.lpm) (smEaa i s.a s.a')

/-- `PD`: a dart of the path. -/
abbrev smPDw (s : SmSV) (i : ℕ) : ℕ := smAnd s.up (smEaa i s.a s.a')

/-- `CV`: the tail on the path. -/
abbrev smCVw (w : SmW) (s : SmSV) : ℕ := smCVf w.vt s.v1 s.v2 s.up

/-- The head on the path. -/
abbrev smCHw (w : SmW) (s : SmSV) : ℕ := smCVf w.vh s.v1 s.v2 s.up

/-- The tail in a hole met by the path. -/
abbrev smHTw (w : SmW) (s : SmSV) : ℕ := smHMf w.t s.t1 s.t2 s.up

/-- The head in a hole met by the path. -/
abbrev smHHw (w : SmW) (s : SmSV) : ℕ := smHMf w.h s.t1 s.t2 s.up

/-- Inside a hole of the children. -/
abbrev smI2w (w : SmW) (s : SmSV) : ℕ :=
  smSg (smAnd (smSg (smCVw w s + smHTw w s)) (smSg (smCHw w s + smHHw w s)) +
    smAnd (smInn w.t w.h) (1 - smHTw w s))

/-- `B'`. -/
abbrev smB2w (w : SmW) (s : SmSV) (i : ℕ) : ℕ :=
  smAnd (smAnd (smLPw w s i) (1 - smI2w w s)) (smAnd (w.kr - 2) (1 - smCVw w s))

/-- `X'`. -/
abbrev smX2w (w : SmW) (s : SmSV) (i : ℕ) : ℕ :=
  smAnd (smB2w w s i) (smSg (smSg w.h + smCHw w s))

/-- `Y'`. -/
abbrev smY2w (w : SmW) (s : SmSV) (i : ℕ) : ℕ := smAnd (smLPw w s i) (smSg (smSg w.t + smCVw w s))

/-- A dart of the left child inside a hole of the children. -/
abbrev smJ2w (w : SmW) (s : SmSV) (i : ℕ) : ℕ := smAnd (smLPw w s i) (smI2w w s)

/-! ### The program -/

def smO2a : Stmt :=
  block [.subN 5384 5314 5364, .subN 5381 5364 5314, .addN 5384 5384 5381, .subN 5381 5310 5384,
    .subN 5384 5314 5365, .subN 5382 5365 5314, .addN 5384 5384 5382, .subN 5382 5310 5384,
    .addN 5383 5381 5382, .subN 5384 5383 5310, .subN 5383 5383 5384, .subN 5385 5310 5345,
    .subN 5384 5367 5385, .subN 5385 5310 5367, .subN 5381 5310 5383, .subN 5385 5385 5381,
    .subN 5386 5335 5384, .subN 5386 5386 5385, .subN 5384 5310 5383, .subN 5387 5366 5384]

def smO2b : Stmt :=
  block [.subN 5384 5341 5368, .subN 5388 5368 5341, .addN 5384 5384 5388, .subN 5388 5310 5384,
    .subN 5384 5341 5369, .subN 5381 5369 5341, .addN 5384 5384 5381, .subN 5381 5310 5384,
    .subN 5384 5310 5381, .subN 5381 5366 5384, .addN 5388 5388 5381, .subN 5384 5388 5310,
    .subN 5388 5388 5384, .subN 5384 5342 5368, .subN 5389 5368 5342, .addN 5384 5384 5389,
    .subN 5389 5310 5384, .subN 5384 5342 5369, .subN 5381 5369 5342, .addN 5384 5384 5381,
    .subN 5381 5310 5384, .subN 5384 5310 5381, .subN 5381 5366 5384, .addN 5389 5389 5381,
    .subN 5384 5389 5310, .subN 5389 5389 5384]

def smO2c : Stmt :=
  block [.subN 5384 5337 5370, .subN 5390 5370 5337, .addN 5384 5384 5390, .subN 5390 5310 5384,
    .subN 5384 5337 5371, .subN 5381 5371 5337, .addN 5384 5384 5381, .subN 5381 5310 5384,
    .subN 5384 5310 5381, .subN 5381 5366 5384, .addN 5390 5390 5381, .subN 5384 5390 5310,
    .subN 5390 5390 5384, .subN 5384 5310 5390, .subN 5390 5343 5384, .subN 5384 5338 5370,
    .subN 5391 5370 5338, .addN 5384 5384 5391, .subN 5391 5310 5384, .subN 5384 5338 5371,
    .subN 5381 5371 5338, .addN 5384 5384 5381, .subN 5381 5310 5384, .subN 5384 5310 5381,
    .subN 5381 5366 5384, .addN 5391 5391 5381, .subN 5384 5391 5310, .subN 5391 5391 5384,
    .subN 5384 5310 5391, .subN 5391 5344 5384]

def smO2d : Stmt :=
  block [.addN 5392 5388 5390, .subN 5384 5392 5310, .subN 5392 5392 5384, .addN 5393 5389 5391,
    .subN 5384 5393 5310, .subN 5393 5393 5384, .subN 5384 5310 5393, .subN 5394 5392 5384,
    .subN 5381 5310 5390, .subN 5384 5310 5381, .subN 5381 5345 5384, .addN 5394 5394 5381,
    .subN 5384 5394 5310, .subN 5394 5394 5384, .subN 5381 5310 5388, .subN 5384 5310 5381,
    .subN 5395 5346 5384, .subN 5381 5310 5394, .subN 5384 5310 5381, .subN 5396 5386 5384,
    .subN 5384 5310 5395, .subN 5396 5396 5384, .addN 5381 5344 5389, .subN 5384 5381 5310,
    .subN 5381 5381 5384, .subN 5384 5310 5381, .subN 5397 5396 5384, .addN 5381 5343 5388,
    .subN 5384 5381 5310, .subN 5381 5381 5384, .subN 5384 5310 5381, .subN 5398 5386 5384,
    .subN 5384 5310 5394, .subN 5399 5386 5384]

/-- The stores and the sums. -/
def smO3 : Stmt :=
  block [.addN 5384 5306 5314, .storeN 5384 5386, .addN 5384 5308 5314, .storeN 5384 5387,
    .addN 5384 5309 5314, .storeN 5384 5388, .addN 5376 5376 5386, .addN 5377 5377 5396,
    .addN 5378 5378 5397, .addN 5379 5379 5398, .addN 5380 5380 5399, .addN 5314 5314 5310]

/-- One index of the output scan. -/
def smOBody : Stmt :=
  .seq smA1 (.seq smA2a (.seq smO2a (.seq smO2b (.seq smO2c (.seq smO2d smO3)))))

/-- **The output scan.** -/
def smO : Stmt :=
  .seq (block [.constN 5314 0, .constN 5376 0, .constN 5377 0, .constN 5378 0, .constN 5379 0,
    .constN 5380 0]) (.whileLtN 5314 5300 smOBody)

section O

variable {P : Input} {W : ℕ}

theorem smO2a_exec (c : Config) (hc : WordsBounded W c) {w : SmW} {s : SmSV} {i : ℕ}
    (r10 : c.nreg 5310 = 1) (r14 : c.nreg 5314 = i) (r35 : c.nreg 5335 = smSg w.p0)
    (r45 : c.nreg 5345 = smInn w.t w.h) (r64 : c.nreg 5364 = s.a) (r65 : c.nreg 5365 = s.a')
    (r66 : c.nreg 5366 = s.up) (r67 : c.nreg 5367 = s.lpm) (hW : 2 ≤ W) :
    ∃ c' t, Exec P W smO2a c c' t ∧ t = 20 ∧ c'.nreg 5383 = smEaa i s.a s.a' ∧
      c'.nreg 5386 = smLPw w s i ∧ c'.nreg 5387 = smPDw s i ∧
      (∀ x, (x < 5381 ∨ 5387 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have b14 := hc.1 5314; have b64 := hc.1 5364; have b65 := hc.1 5365
  rw [r14] at b14; rw [r64] at b64; rw [r65] at b65
  unfold smO2a
  exec_block
  all_goals try (config_simp; (try simp only [r10, r14, r35, r45, r64, r65, r66, r67]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r10, r14, r35, r45, r64, r65, r66, r67]); done)
  · config_simp; simp (disch := omega) only [upd_other]

theorem smO2b_exec (c : Config) (hc : WordsBounded W c) {w : SmW} {s : SmSV}
    (r10 : c.nreg 5310 = 1) (r41 : c.nreg 5341 = w.vt) (r42 : c.nreg 5342 = w.vh)
    (r66 : c.nreg 5366 = s.up) (r68 : c.nreg 5368 = s.v1) (r69 : c.nreg 5369 = s.v2)
    (hW : 2 ≤ W) (hup : s.up ≤ 1) :
    ∃ c' t, Exec P W smO2b c c' t ∧ t = 26 ∧ c'.nreg 5388 = smCVw w s ∧
      c'.nreg 5389 = smCHw w s ∧
      (∀ x, (x < 5381 ∨ (5381 < x ∧ x < 5384) ∨ (5384 < x ∧ x < 5388) ∨ 5389 < x) →
        c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have b1 := hc.1 5341; have b2 := hc.1 5342; have b3 := hc.1 5368; have b4 := hc.1 5369
  rw [r41] at b1; rw [r42] at b2; rw [r68] at b3; rw [r69] at b4
  unfold smO2b
  exec_block
  all_goals try (config_simp; (try simp only [r10, r41, r42, r66, r68, r69]); omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r10, r41, r42, r66, r68, r69]); done)
  · config_simp; simp (disch := omega) only [upd_other]

theorem smO2c_exec (c : Config) (hc : WordsBounded W c) {w : SmW} {s : SmSV}
    (r10 : c.nreg 5310 = 1) (r37 : c.nreg 5337 = w.t) (r38 : c.nreg 5338 = w.h)
    (r43 : c.nreg 5343 = smSg w.t) (r44 : c.nreg 5344 = smSg w.h)
    (r66 : c.nreg 5366 = s.up) (r70 : c.nreg 5370 = s.t1) (r71 : c.nreg 5371 = s.t2)
    (hW : 2 ≤ W) (hup : s.up ≤ 1) :
    ∃ c' t, Exec P W smO2c c c' t ∧ t = 30 ∧ c'.nreg 5390 = smHTw w s ∧
      c'.nreg 5391 = smHHw w s ∧
      (∀ x, (x < 5381 ∨ (5381 < x ∧ x < 5384) ∨ (5384 < x ∧ x < 5390) ∨ 5391 < x) →
        c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have b1 := hc.1 5337; have b2 := hc.1 5338; have b3 := hc.1 5370; have b4 := hc.1 5371
  rw [r37] at b1; rw [r38] at b2; rw [r70] at b3; rw [r71] at b4
  unfold smO2c
  exec_block
  all_goals try (config_simp; (try simp only [r10, r37, r38, r43, r44, r66, r70, r71]); omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r10, r37, r38, r43, r44, r66, r70, r71]); done)
  · config_simp; simp (disch := omega) only [upd_other]

theorem smO2d_exec (c : Config) (hc : WordsBounded W c) {w : SmW} {s : SmSV} {i : ℕ}
    (r10 : c.nreg 5310 = 1) (r43 : c.nreg 5343 = smSg w.t) (r44 : c.nreg 5344 = smSg w.h)
    (r45 : c.nreg 5345 = smInn w.t w.h) (r46 : c.nreg 5346 = w.kr - 2)
    (r86 : c.nreg 5386 = smLPw w s i) (r88 : c.nreg 5388 = smCVw w s)
    (r89 : c.nreg 5389 = smCHw w s) (r90 : c.nreg 5390 = smHTw w s)
    (r91 : c.nreg 5391 = smHHw w s) (hW : 2 ≤ W) :
    ∃ c' t, Exec P W smO2d c c' t ∧ t = 34 ∧ c'.nreg 5396 = smB2w w s i ∧
      c'.nreg 5397 = smX2w w s i ∧ c'.nreg 5398 = smY2w w s i ∧ c'.nreg 5399 = smJ2w w s i ∧
      (∀ x, (x < 5381 ∨ (5381 < x ∧ x < 5384) ∨ (5384 < x ∧ x < 5392) ∨ 5399 < x) →
        c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have k1 : smCVw w s ≤ 1 := by unfold smCVw smCVf smSg; omega
  have k2 : smCHw w s ≤ 1 := by unfold smCHw smCVf smSg; omega
  have k3 : smHTw w s ≤ 1 := by unfold smHTw smHMf smAnd smSg; omega
  have k4 : smHHw w s ≤ 1 := by unfold smHHw smHMf smAnd smSg; omega
  have k5 : smSg w.t ≤ 1 := by unfold smSg; omega
  have k6 : smSg w.h ≤ 1 := by unfold smSg; omega
  have k7 : smInn w.t w.h ≤ 1 := by unfold smInn smAnd smSg; omega
  unfold smO2d
  exec_block
  all_goals try (config_simp; (try simp only [r10, r43, r44, r45, r46, r86, r88, r89, r90, r91]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r10, r43, r44, r45, r46, r86, r88, r89, r90, r91]); done)
  · config_simp; simp (disch := omega) only [upd_other]

theorem smO3_exec (c : Config) (hc : WordsBounded W c) {Ob n i LP PD CV L B X Y J b x y j : ℕ}
    (r06 : c.nreg 5306 = Ob) (r08 : c.nreg 5308 = Ob + n) (r09 : c.nreg 5309 = Ob + 2 * n)
    (r10 : c.nreg 5310 = 1) (r14 : c.nreg 5314 = i) (r86 : c.nreg 5386 = LP)
    (r87 : c.nreg 5387 = PD) (r88 : c.nreg 5388 = CV) (r96 : c.nreg 5396 = b)
    (r97 : c.nreg 5397 = x) (r98 : c.nreg 5398 = y) (r99 : c.nreg 5399 = j)
    (r76 : c.nreg 5376 = L) (r77 : c.nreg 5377 = B) (r78 : c.nreg 5378 = X)
    (r79 : c.nreg 5379 = Y) (r80 : c.nreg 5380 = J)
    (w1 : Ob + 2 * n + i ≤ W) (w2 : L + LP ≤ W) (w3 : B + b ≤ W) (w4 : X + x ≤ W)
    (w5 : Y + y ≤ W) (w6 : J + j ≤ W) (w7 : i + 1 ≤ W) :
    ∃ c' t, Exec P W smO3 c c' t ∧ t = 12 ∧ c'.nreg 5314 = i + 1 ∧ c'.nreg 5376 = L + LP ∧
      c'.nreg 5377 = B + b ∧ c'.nreg 5378 = X + x ∧ c'.nreg 5379 = Y + y ∧
      c'.nreg 5380 = J + j ∧
      c'.nmem = upd (upd (upd c.nmem (Ob + i) LP) (Ob + n + i) PD) (Ob + 2 * n + i) CV ∧
      (∀ z, (z < 5314 ∨ (5314 < z ∧ z < 5376) ∨ (5380 < z ∧ z ≠ 5384)) → c'.nreg z = c.nreg z) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold smO3
  exec_block
  all_goals try (config_simp; (try simp only [r06, r08, r09, r10, r14, r86, r87, r88, r96, r97,
    r98, r99, r76, r77, r78, r79, r80]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun z hz => ?_, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r06, r08, r09, r10, r14, r86, r87, r88, r96, r97,
    r98, r99, r76, r77, r78, r79, r80]); done)
  · config_simp; simp (disch := omega) only [upd_other]

set_option maxHeartbeats 1600000 in
/-- **One index of the output scan.** -/
theorem smOBody_exec (c : Config) (hc : WordsBounded W c) {PFb RVb THb KRb VTb Ob n i : ℕ}
    (r1 : c.nreg 5301 = PFb) (r2 : c.nreg 5302 = RVb) (r3 : c.nreg 5303 = THb)
    (r4 : c.nreg 5304 = KRb) (r5 : c.nreg 5305 = VTb) (r06 : c.nreg 5306 = Ob)
    (r08 : c.nreg 5308 = Ob + n) (r09 : c.nreg 5309 = Ob + 2 * n) (r10 : c.nreg 5310 = 1)
    (r11 : c.nreg 5311 = 2) (r14 : c.nreg 5314 = i) (hup : c.nreg 5366 ≤ 1) (hW : 2 ≤ W)
    (w1 : PFb + i ≤ W) (w2 : RVb + i ≤ W) (w3 : THb + i ≤ W) (w4 : KRb + i ≤ W)
    (w5 : VTb + i ≤ W) (w6 : THb + c.nmem (RVb + i) ≤ W) (w7 : KRb + c.nmem (RVb + i) ≤ W)
    (w8 : VTb + c.nmem (RVb + i) ≤ W) (w9 : Ob + 2 * n + i ≤ W) (w10 : c.nreg 5376 + 1 ≤ W)
    (w11 : c.nreg 5377 + 1 ≤ W) (w12 : c.nreg 5378 + 1 ≤ W) (w13 : c.nreg 5379 + 1 ≤ W)
    (w14 : c.nreg 5380 + 1 ≤ W) (w15 : i + 1 ≤ W) :
    ∃ c' t, Exec P W smOBody c c' t ∧ t ≤ 157 ∧ c'.nreg 5314 = i + 1 ∧
      c'.nreg 5376 = c.nreg 5376 + smLPw (smW c.nmem PFb RVb THb KRb VTb i)
        ⟨c.nreg 5364, c.nreg 5365, c.nreg 5366, c.nreg 5367, c.nreg 5368, c.nreg 5369,
          c.nreg 5370, c.nreg 5371⟩ i ∧
      c'.nreg 5377 = c.nreg 5377 + smB2w (smW c.nmem PFb RVb THb KRb VTb i)
        ⟨c.nreg 5364, c.nreg 5365, c.nreg 5366, c.nreg 5367, c.nreg 5368, c.nreg 5369,
          c.nreg 5370, c.nreg 5371⟩ i ∧
      c'.nreg 5378 = c.nreg 5378 + smX2w (smW c.nmem PFb RVb THb KRb VTb i)
        ⟨c.nreg 5364, c.nreg 5365, c.nreg 5366, c.nreg 5367, c.nreg 5368, c.nreg 5369,
          c.nreg 5370, c.nreg 5371⟩ i ∧
      c'.nreg 5379 = c.nreg 5379 + smY2w (smW c.nmem PFb RVb THb KRb VTb i)
        ⟨c.nreg 5364, c.nreg 5365, c.nreg 5366, c.nreg 5367, c.nreg 5368, c.nreg 5369,
          c.nreg 5370, c.nreg 5371⟩ i ∧
      c'.nreg 5380 = c.nreg 5380 + smJ2w (smW c.nmem PFb RVb THb KRb VTb i)
        ⟨c.nreg 5364, c.nreg 5365, c.nreg 5366, c.nreg 5367, c.nreg 5368, c.nreg 5369,
          c.nreg 5370, c.nreg 5371⟩ i ∧
      c'.nmem = upd (upd (upd c.nmem (Ob + i) (smLPw (smW c.nmem PFb RVb THb KRb VTb i)
        ⟨c.nreg 5364, c.nreg 5365, c.nreg 5366, c.nreg 5367, c.nreg 5368, c.nreg 5369,
          c.nreg 5370, c.nreg 5371⟩ i)) (Ob + n + i)
          (smPDw ⟨c.nreg 5364, c.nreg 5365, c.nreg 5366, c.nreg 5367, c.nreg 5368, c.nreg 5369,
            c.nreg 5370, c.nreg 5371⟩ i)) (Ob + 2 * n + i)
          (smCVw (smW c.nmem PFb RVb THb KRb VTb i)
            ⟨c.nreg 5364, c.nreg 5365, c.nreg 5366, c.nreg 5367, c.nreg 5368, c.nreg 5369,
              c.nreg 5370, c.nreg 5371⟩) ∧
      (∀ x, (x < 5314 ∨ (5353 < x ∧ x < 5376) ∨ 5399 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, l35, l36, l37, l38, l39, l40, l41, l42, n₁, m₁, rr₁, rm₁, o₁⟩ :=
    smA1_exec (P := P) c hc r1 r2 r3 r4 r5 r14 w1 w2 w3 w4 w5 w6 w7 w8
  have hw₁ := e₁.wb_right
  have q₁ : ∀ x, (x < 5334 ∨ 5342 < x) → c₁.nreg x = c.nreg x := n₁
  obtain ⟨c₂, t₂, e₂, ht₂, f35, f43, f44, f45, f46, f47, n₂, m₂, rr₂, rm₂, o₂⟩ :=
    smA2a_exec (P := P) c₁ hw₁ hW (by rw [q₁ _ (by omega), r10]) (by rw [q₁ _ (by omega), r11])
      l35 l37 l38 l39 l40
  have hw₂ := e₂.wb_right
  have q₂ : ∀ x, (x < 5335 ∨ (5335 < x ∧ x < 5343) ∨ (5348 < x ∧ x < 5353) ∨ 5353 < x) →
      c₂.nreg x = c₁.nreg x := n₂
  set w := smW c.nmem PFb RVb THb KRb VTb i with hw
  set s : SmSV := ⟨c.nreg 5364, c.nreg 5365, c.nreg 5366, c.nreg 5367, c.nreg 5368, c.nreg 5369,
    c.nreg 5370, c.nreg 5371⟩ with hs
  have s₂ : ∀ x, (x < 5334 ∨ 5353 < x) → c₂.nreg x = c.nreg x := fun x hx => by
    rw [q₂ _ (by omega), q₁ _ (by omega)]
  obtain ⟨c₃, t₃, e₃, ht₃, g83, g86, g87, n₃, m₃, rr₃, rm₃, o₃⟩ :=
    smO2a_exec (P := P) c₂ hw₂ (w := w) (s := s) (i := i) (by rw [s₂ _ (by omega), r10])
      (by rw [s₂ _ (by omega), r14]) f35 f45 (s₂ _ (by omega)) (s₂ _ (by omega))
      (s₂ _ (by omega)) (s₂ _ (by omega)) hW
  have hw₃ := e₃.wb_right
  have q₃ : ∀ x, (x < 5381 ∨ 5387 < x) → c₃.nreg x = c₂.nreg x := n₃
  have s₃ : ∀ x, (x < 5334 ∨ (5353 < x ∧ x < 5381) ∨ 5387 < x) → c₃.nreg x = c.nreg x :=
    fun x hx => by rw [q₃ _ (by omega), s₂ _ (by omega)]
  obtain ⟨c₄, t₄, e₄, ht₄, g88, g89, n₄, m₄, rr₄, rm₄, o₄⟩ :=
    smO2b_exec (P := P) c₃ hw₃ (w := w) (s := s) (by rw [s₃ _ (by omega), r10])
      (by rw [q₃ _ (by omega), q₂ _ (by omega)]; exact l41)
      (by rw [q₃ _ (by omega), q₂ _ (by omega)]; exact l42)
      (s₃ _ (by omega)) (s₃ _ (by omega)) (s₃ _ (by omega)) hW hup
  have hw₄ := e₄.wb_right
  have q₄ : ∀ x, (x < 5381 ∨ (5381 < x ∧ x < 5384) ∨ (5384 < x ∧ x < 5388) ∨ 5389 < x) →
      c₄.nreg x = c₃.nreg x := n₄
  obtain ⟨c₅, t₅, e₅, ht₅, g90, g91, n₅, m₅, rr₅, rm₅, o₅⟩ :=
    smO2c_exec (P := P) c₄ hw₄ (w := w) (s := s)
      (by rw [q₄ _ (by omega), s₃ _ (by omega), r10])
      (by rw [q₄ _ (by omega), q₃ _ (by omega), q₂ _ (by omega)]; exact l37)
      (by rw [q₄ _ (by omega), q₃ _ (by omega), q₂ _ (by omega)]; exact l38)
      (by rw [q₄ _ (by omega), q₃ _ (by omega)]; exact f43)
      (by rw [q₄ _ (by omega), q₃ _ (by omega)]; exact f44)
      (by rw [q₄ _ (by omega), s₃ _ (by omega)]) (by rw [q₄ _ (by omega), s₃ _ (by omega)])
      (by rw [q₄ _ (by omega), s₃ _ (by omega)]) hW hup
  have hw₅ := e₅.wb_right
  have q₅ : ∀ x, (x < 5381 ∨ (5381 < x ∧ x < 5384) ∨ (5384 < x ∧ x < 5390) ∨ 5391 < x) →
      c₅.nreg x = c₄.nreg x := n₅
  obtain ⟨c₆, t₆, e₆, ht₆, g96, g97, g98, g99, n₆, m₆, rr₆, rm₆, o₆⟩ :=
    smO2d_exec (P := P) c₅ hw₅ (w := w) (s := s) (i := i)
      (by rw [q₅ _ (by omega), q₄ _ (by omega), s₃ _ (by omega), r10])
      (by rw [q₅ _ (by omega), q₄ _ (by omega), q₃ _ (by omega)]; exact f43)
      (by rw [q₅ _ (by omega), q₄ _ (by omega), q₃ _ (by omega)]; exact f44)
      (by rw [q₅ _ (by omega), q₄ _ (by omega), q₃ _ (by omega)]; exact f45)
      (by rw [q₅ _ (by omega), q₄ _ (by omega), q₃ _ (by omega)]; exact f46)
      (by rw [q₅ _ (by omega), q₄ _ (by omega)]; exact g86)
      (by rw [q₅ _ (by omega)]; exact g88) (by rw [q₅ _ (by omega)]; exact g89) g90 g91 hW
  have hw₆ := e₆.wb_right
  have q₆ : ∀ x, (x < 5381 ∨ (5381 < x ∧ x < 5384) ∨ (5384 < x ∧ x < 5392) ∨ 5399 < x) →
      c₆.nreg x = c₅.nreg x := n₆
  have s₆ : ∀ x, (x < 5334 ∨ (5353 < x ∧ x < 5381) ∨ 5399 < x) → c₆.nreg x = c.nreg x :=
    fun x hx => by rw [q₆ _ (by omega), q₅ _ (by omega), q₄ _ (by omega), s₃ _ (by omega)]
  have hLP : smLPw w s i ≤ 1 := by unfold smLPw smSg; omega
  have hB2 : smB2w w s i ≤ 1 := by unfold smB2w smAnd; have := hLP; omega
  have hX2 : smX2w w s i ≤ 1 := by unfold smX2w smAnd; have := hB2; omega
  have hY2 : smY2w w s i ≤ 1 := by unfold smY2w smAnd; have := hLP; omega
  have hJ2 : smJ2w w s i ≤ 1 := by unfold smJ2w smAnd; have := hLP; omega
  obtain ⟨c₇, t₇, e₇, ht₇, a14, a76, a77, a78, a79, a80, m₇, n₇, rr₇, rm₇, o₇⟩ :=
    smO3_exec (P := P) c₆ hw₆ (Ob := Ob) (n := n) (i := i) (LP := smLPw w s i)
      (PD := smPDw s i) (CV := smCVw w s) (L := c.nreg 5376) (B := c.nreg 5377)
      (X := c.nreg 5378) (Y := c.nreg 5379) (J := c.nreg 5380) (b := smB2w w s i)
      (x := smX2w w s i) (y := smY2w w s i) (j := smJ2w w s i)
      (by rw [s₆ _ (by omega), r06]) (by rw [s₆ _ (by omega), r08])
      (by rw [s₆ _ (by omega), r09]) (by rw [s₆ _ (by omega), r10])
      (by rw [s₆ _ (by omega), r14])
      (by rw [q₆ _ (by omega), q₅ _ (by omega), q₄ _ (by omega)]; exact g86)
      (by rw [q₆ _ (by omega), q₅ _ (by omega), q₄ _ (by omega)]; exact g87)
      (by rw [q₆ _ (by omega), q₅ _ (by omega)]; exact g88) g96 g97 g98 g99
      (s₆ _ (by omega)) (s₆ _ (by omega)) (s₆ _ (by omega)) (s₆ _ (by omega)) (s₆ _ (by omega))
      w9 (by omega) (by omega) (by omega) (by omega) (by omega) w15
  have hm : c₆.nmem = c.nmem := by rw [m₆, m₅, m₄, m₃, m₂, m₁]
  refine ⟨c₇, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + t₇))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))))), by omega, a14, a76, a77,
    a78, a79, a80, by rw [m₇, hm], fun x hx => ?_, by rw [rr₇, rr₆, rr₅, rr₄, rr₃, rr₂, rr₁],
    by rw [rm₇, rm₆, rm₅, rm₄, rm₃, rm₂, rm₁], by rw [o₇, o₆, o₅, o₄, o₃, o₂, o₁]⟩
  rw [n₇ x (by omega), s₆ x (by omega)]


/-- **The output of the output scan up to the index `i`**, for the words `s` of the split. -/
structure SmOOut (m₀ : ℕ → ℕ) (PFb RVb THb KRb VTb Ob n : ℕ) (s : SmSV) (i : ℕ) (c : Config) :
    Prop where
  mem : ∀ a, (a < Ob ∨ Ob + 3 * n ≤ a) → c.nmem a = m₀ a
  lp : ∀ j < i, c.nmem (Ob + j) = smLPw (smW m₀ PFb RVb THb KRb VTb j) s j
  pd : ∀ j < i, c.nmem (Ob + n + j) = smPDw s j
  cv : ∀ j < i, c.nmem (Ob + 2 * n + j) = smCVw (smW m₀ PFb RVb THb KRb VTb j) s
  sl : c.nreg 5376 = ∑ j ∈ range i, smLPw (smW m₀ PFb RVb THb KRb VTb j) s j
  sb : c.nreg 5377 = ∑ j ∈ range i, smB2w (smW m₀ PFb RVb THb KRb VTb j) s j
  sx : c.nreg 5378 = ∑ j ∈ range i, smX2w (smW m₀ PFb RVb THb KRb VTb j) s j
  sy : c.nreg 5379 = ∑ j ∈ range i, smY2w (smW m₀ PFb RVb THb KRb VTb j) s j
  sj : c.nreg 5380 = ∑ j ∈ range i, smJ2w (smW m₀ PFb RVb THb KRb VTb j) s j
  bl : c.nreg 5376 ≤ i
  bb : c.nreg 5377 ≤ i
  bx : c.nreg 5378 ≤ i
  bY : c.nreg 5379 ≤ i
  bj : c.nreg 5380 ≤ i

set_option maxHeartbeats 1600000 in
/-- **The output scan**: within `159 n + 10` steps, `SmOOut` up to `n` for the words of the
split in `5364 … 5371`. -/
theorem smO_exec (c : Config) (hc : WordsBounded W c) {n PFb RVb THb KRb VTb Ob : ℕ}
    (r0 : c.nreg 5300 = n) (r1 : c.nreg 5301 = PFb) (r2 : c.nreg 5302 = RVb)
    (r3 : c.nreg 5303 = THb) (r4 : c.nreg 5304 = KRb) (r5 : c.nreg 5305 = VTb)
    (r06 : c.nreg 5306 = Ob) (r08 : c.nreg 5308 = Ob + n) (r09 : c.nreg 5309 = Ob + 2 * n)
    (r10 : c.nreg 5310 = 1) (r11 : c.nreg 5311 = 2) (hup : c.nreg 5366 ≤ 1) (hW : 2 ≤ W)
    (w1 : PFb + n ≤ Ob) (w2 : RVb + n ≤ Ob) (w3 : THb + n ≤ Ob) (w4 : KRb + n ≤ Ob)
    (w5 : VTb + n ≤ Ob) (w6 : Ob + 3 * n ≤ W) (w7 : n + 1 ≤ W)
    (hrv : ∀ i < n, c.nmem (RVb + i) < n) :
    ∃ c' t, Exec P W smO c c' t ∧ t ≤ 159 * n + 10 ∧
      SmOOut c.nmem PFb RVb THb KRb VTb Ob n ⟨c.nreg 5364, c.nreg 5365, c.nreg 5366,
        c.nreg 5367, c.nreg 5368, c.nreg 5369, c.nreg 5370, c.nreg 5371⟩ n c' ∧
      (∀ x, (x < 5314 ∨ (5353 < x ∧ x < 5376) ∨ 5399 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold smO
  obtain ⟨c₁, k₁, e₁, hk₁, g14, g76, g77, g78, g79, g80, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 5314 0, .constN 5376 0, .constN 5377 0, .constN 5378 0,
        .constN 5379 0, .constN 5380 0]) c c₁ k₁ ∧ k₁ = 6 ∧ c₁.nreg 5314 = 0 ∧
      c₁.nreg 5376 = 0 ∧ c₁.nreg 5377 = 0 ∧ c₁.nreg 5378 = 0 ∧ c₁.nreg 5379 = 0 ∧
      c₁.nreg 5380 = 0 ∧
      (∀ x, (x < 5314 ∨ (5314 < x ∧ x < 5376) ∨ 5380 < x) → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try (config_simp; omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; done)
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, (x < 5314 ∨ (5314 < x ∧ x < 5376) ∨ 5380 < x) → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  set s : SmSV := ⟨c.nreg 5364, c.nreg 5365, c.nreg 5366, c.nreg 5367, c.nreg 5368, c.nreg 5369,
    c.nreg 5370, c.nreg 5371⟩ with hs
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 5314 ∨ (5353 < x ∧ x < 5376) ∨ 5399 < x) → c'.nreg x = c₁.nreg x) ∧
    SmOOut m₀ PFb RVb THb KRb VTb Ob n s i c' ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  have j0 : J 0 c₁ := ⟨fun _ _ => rfl,
    ⟨fun a _ => by rw [gm₁], fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
      fun j hj => absurd hj (by omega), by rw [g76]; rfl, by rw [g77]; rfl, by rw [g78]; rfl,
      by rw [g79]; rfl, by rw [g80]; rfl, by omega, by omega, by omega, by omega, by omega⟩,
    rfl, rfl, rfl⟩
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h14, j1, j2, j4, j5, j6⟩ := tgRange (P := P)
    (a := 5314) (b := 5300) (body := smOBody) J (B := 157) c₁ hw₁ g14
    (by rw [q _ (by omega), r0]) (Nat.zero_le n) j0
    (fun i c' hlo hhi hw h14 h00 ⟨j1, j2, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 5314 ∨ (5353 < x ∧ x < 5376) ∨ 5399 < x) → c'.nreg x = c₁.nreg x := j1
      have hlow : ∀ a < Ob, c'.nmem a = m₀ a := fun a ha => j2.mem a (Or.inl ha)
      have hrvi : c'.nmem (RVb + i) < n := by rw [hlow _ (by omega)]; exact hrv i hhi
      have hsv : (⟨c'.nreg 5364, c'.nreg 5365, c'.nreg 5366, c'.nreg 5367, c'.nreg 5368,
          c'.nreg 5369, c'.nreg 5370, c'.nreg 5371⟩ : SmSV) = s := by
        simp (disch := omega) only [hs, f, q]
      have hwv : smW c'.nmem PFb RVb THb KRb VTb i = smW m₀ PFb RVb THb KRb VTb i :=
        smW_congr hhi (hrv i hhi) w1 w2 w3 w4 w5 hlow
      obtain ⟨c'', t, ex, ht, b14, b76, b77, b78, b79, b80, bm, bn, br, brm, bo⟩ :=
        smOBody_exec (P := P) c' hw (PFb := PFb) (RVb := RVb) (THb := THb) (KRb := KRb)
          (VTb := VTb) (Ob := Ob) (n := n) (i := i)
          (by rw [f _ (by omega), q _ (by omega), r1]) (by rw [f _ (by omega), q _ (by omega), r2])
          (by rw [f _ (by omega), q _ (by omega), r3]) (by rw [f _ (by omega), q _ (by omega), r4])
          (by rw [f _ (by omega), q _ (by omega), r5]) (by rw [f _ (by omega), q _ (by omega), r06])
          (by rw [f _ (by omega), q _ (by omega), r08])
          (by rw [f _ (by omega), q _ (by omega), r09])
          (by rw [f _ (by omega), q _ (by omega), r10])
          (by rw [f _ (by omega), q _ (by omega), r11]) h14
          (by rw [f _ (by omega), q _ (by omega)]; exact hup) hW
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by have := j2.bl; omega) (by have := j2.bb; omega)
          (by have := j2.bx; omega) (by have := j2.bY; omega) (by have := j2.bj; omega)
          (by omega)
      rw [hsv, hwv] at b76 b77 b78 b79 b80 bm
      have hLP : smLPw (smW m₀ PFb RVb THb KRb VTb i) s i ≤ 1 := by unfold smLPw smSg; omega
      have hB2 : smB2w (smW m₀ PFb RVb THb KRb VTb i) s i ≤ 1 := by
        unfold smB2w smAnd; have := hLP; omega
      have hX2 : smX2w (smW m₀ PFb RVb THb KRb VTb i) s i ≤ 1 := by
        unfold smX2w smAnd; have := hB2; omega
      have hY2 : smY2w (smW m₀ PFb RVb THb KRb VTb i) s i ≤ 1 := by
        unfold smY2w smAnd; have := hLP; omega
      have hJ2 : smJ2w (smW m₀ PFb RVb THb KRb VTb i) s i ≤ 1 := by
        unfold smJ2w smAnd; have := hLP; omega
      refine ⟨c'', t, ex, by omega, b14, by rw [bn _ (by omega)]; exact h00,
        fun x hx => by rw [bn x hx, f x hx], ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_⟩, by rw [br, j4], by rw [brm, j5], by rw [bo, j6]⟩
      · intro a ha
        rw [bm, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
        exact j2.mem a ha
      · intro j hj
        rw [bm, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j2.lp j hj
        · rw [upd_same]
      · intro j hj
        rw [bm, upd_other _ _ _ (by omega)]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact j2.pd j hj
        · rw [upd_same]
      · intro j hj
        rw [bm]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
            upd_other _ _ _ (by omega)]; exact j2.cv j hj
        · rw [upd_same]
      · rw [b76, j2.sl, sum_range_succ]
      · rw [b77, j2.sb, sum_range_succ]
      · rw [b78, j2.sx, sum_range_succ]
      · rw [b79, j2.sy, sum_range_succ]
      · rw [b80, j2.sj, sum_range_succ]
      · rw [b76]; have := j2.bl; omega
      · rw [b77]; have := j2.bb; omega
      · rw [b78]; have := j2.bx; omega
      · rw [b79]; have := j2.bY; omega
      · rw [b80]; have := j2.bj; omega)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2,
    fun x hx => by rw [j1 x hx, q x (by omega)], by rw [j4, gr₁], by rw [j5, grm₁],
    by rw [j6, go₁]⟩


end O

end BKMNW

end PlanarFlow
