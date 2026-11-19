module

public import PlanarFlow.NegSSSP.LinGlue
public import PlanarFlow.Klein.ExecNat

/-!
# Reading Klein's answers at a node on natural words

`NegSSSP.rdProg` (`PlanarFlow/NegSSSP/ReadGlue.lean`) reads the answers of Klein's program on
the *perturbed* lengths, with real registers and a real-side binary search. Klein's program on
natural words with the isolating lengths (`Klein.kleinMemNDC`) leaves its answers already
divided and cut off, as natural words (`Klein.kOutNK`): a reach flag and the distance. Here they
are read into the layout of `NegSSSP.bfStartP` **on natural words**, the real values written as
residues modulo the node's modulus `M` at the natural cells simulating the node's real memory:

* `rdProgN`: one loop over `e < b²` (`s = e / b`, `t = e % b` by `divN`, `modN`): the flag
  `[f = 1]` of the pair (`f` Klein's reach word at `RBb + σ s · k + σ t`) at `Fb + e`, and
  `[f = 1] · ((v + δ'(ν t) + M - δ'(ν s)) mod M)` at `L0 + e`, `v` the answer word at
  `OUTb + σ s · k + σ t`, `δ'` the residues of the potentials at `D0 + ν`.
* `rdProgN_exec`: within `40 b² + 6` steps; the natural memory changes only at the two output
  regions, the registers only at `310 … 325`, the reals and the output are kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- The data of the reading: `b` pairs per row, `k` the row length of Klein's arrays, `w` the
length of the potentials, the bases of the arrays (`Sg` the positions `σ` on the face, `Nb` the
vertex numbers `ν`, `D0` the residues of the potentials, `RBb` the reach words, `OUTb` the
answers, `Fb` the output flags, `L0` the output residues) and the modulus `M`. -/
structure RdN where
  b : ℕ
  k : ℕ
  w : ℕ
  Sg : ℕ
  Nb : ℕ
  D0 : ℕ
  RBb : ℕ
  OUTb : ℕ
  Fb : ℕ
  L0 : ℕ
  M : ℕ
  σ : ℕ → ℕ
  ν : ℕ → ℕ

/-- The address of the answer of the pair `(s, t)` in Klein's arrays. -/
def RdN.ad (R : RdN) (s t : ℕ) : ℕ := R.σ s * R.k + R.σ t

/-- The output flag of the pair `(s, t)`, from the memory of `c`. -/
def RdN.flag (R : RdN) (c : Config) (s t : ℕ) : ℕ :=
  if c.nmem (R.RBb + R.ad s t) = 1 then 1 else 0

/-- The output residue of the pair `(s, t)`, from the memory of `c`. -/
def RdN.val (R : RdN) (c : Config) (s t : ℕ) : ℕ :=
  if c.nmem (R.RBb + R.ad s t) = 1 then
    (c.nmem (R.OUTb + R.ad s t) + c.nmem (R.D0 + R.ν t) + R.M - c.nmem (R.D0 + R.ν s)) % R.M
  else 0

/-- The registers and arrays of `rdProgN`. -/
structure RdNIn (R : RdN) (c : Config) : Prop where
  r300 : c.nreg 300 = R.b
  r301 : c.nreg 301 = R.Sg
  r302 : c.nreg 302 = R.Nb
  r303 : c.nreg 303 = R.D0
  r304 : c.nreg 304 = R.RBb
  r305 : c.nreg 305 = R.OUTb
  r306 : c.nreg 306 = R.k
  r307 : c.nreg 307 = R.Fb
  r308 : c.nreg 308 = R.L0
  r309 : c.nreg 309 = R.M
  sg : ∀ s < R.b, c.nmem (R.Sg + s) = R.σ s
  nb : ∀ s < R.b, c.nmem (R.Nb + s) = R.ν s

/-- The layout of `rdProgN`: indices in range, the two outputs apart from each other and from
the arrays read, the addresses and the values below the word bound (`Vb` bounds the answer
words, the residues are below `M`). -/
structure RdNLay (R : RdN) (Vb W : ℕ) : Prop where
  σlt : ∀ s < R.b, R.σ s < R.k
  νlt : ∀ s < R.b, R.ν s < R.w
  fl : R.Fb + R.b * R.b ≤ R.L0 ∨ R.L0 + R.b * R.b ≤ R.Fb
  fS : R.Fb + R.b * R.b ≤ R.Sg ∨ R.Sg + R.b ≤ R.Fb
  fN : R.Fb + R.b * R.b ≤ R.Nb ∨ R.Nb + R.b ≤ R.Fb
  fD : R.Fb + R.b * R.b ≤ R.D0 ∨ R.D0 + R.w ≤ R.Fb
  fR : R.Fb + R.b * R.b ≤ R.RBb ∨ R.RBb + R.k * R.k ≤ R.Fb
  fO : R.Fb + R.b * R.b ≤ R.OUTb ∨ R.OUTb + R.k * R.k ≤ R.Fb
  lS : R.L0 + R.b * R.b ≤ R.Sg ∨ R.Sg + R.b ≤ R.L0
  lN : R.L0 + R.b * R.b ≤ R.Nb ∨ R.Nb + R.b ≤ R.L0
  lD : R.L0 + R.b * R.b ≤ R.D0 ∨ R.D0 + R.w ≤ R.L0
  lR : R.L0 + R.b * R.b ≤ R.RBb ∨ R.RBb + R.k * R.k ≤ R.L0
  lO : R.L0 + R.b * R.b ≤ R.OUTb ∨ R.OUTb + R.k * R.k ≤ R.L0
  wS : R.Sg + R.b ≤ W
  wN : R.Nb + R.b ≤ W
  wD : R.D0 + R.w ≤ W
  wR : R.RBb + R.k * R.k ≤ W
  wO : R.OUTb + R.k * R.k ≤ W
  wF : R.Fb + R.b * R.b ≤ W
  wL : R.L0 + R.b * R.b ≤ W
  wb : R.b * R.b + 1 ≤ W
  wV : Vb + 2 * R.M ≤ W
  wk : R.k * R.k ≤ W

/-! ### The program -/

/-- The reads of the entry `e = r311`: `s`, `t`, `σ s`, `σ t`, the address `ad`, Klein's flag
`f` and answer `v`, the indicator `[f = 1]` (`r320`). -/
def rdNA : Stmt :=
  block [.divN 313 311 300, .modN 314 311 300, .addN 315 301 313, .loadN 315 315,
    .addN 316 301 314, .loadN 316 316, .mulN 317 315 306, .addN 317 317 316,
    .addN 318 304 317, .loadN 318 318, .addN 319 305 317, .loadN 319 319,
    .subN 320 318 312, .subN 320 312 320, .subN 321 312 318, .subN 320 320 321]

/-- The value of the entry and the two stores: `δ'(ν s)`, `δ'(ν t)`, the residue, times the
indicator; then `e := e + 1`. -/
def rdNB : Stmt :=
  block [.addN 322 302 313, .loadN 322 322, .addN 323 302 314, .loadN 323 323,
    .addN 322 303 322, .loadN 322 322, .addN 323 303 323, .loadN 323 323,
    .addN 324 319 323, .addN 324 324 309, .subN 324 324 322, .modN 324 324 309,
    .mulN 324 324 320, .addN 325 307 311, .storeN 325 320, .addN 325 308 311,
    .storeN 325 324, .addN 311 311 312]

/-- The body of the reading loop. -/
def rdNBody : Stmt := .seq rdNA rdNB

/-- **The reading of Klein's natural answers** (see the module docstring). -/
def rdProgN : Stmt :=
  .seq (block [.constN 312 1, .constN 311 0, .mulN 310 300 300]) (.whileLtN 311 310 rdNBody)

theorem rdProgN_natOnly : Klein.natOnly rdProgN = true := by kernel_rfl

theorem rdProgN_regsOK : rdProgN.regsOK (fun r => decide (r < 326)) = true := by kernel_rfl

theorem rdProgN_noInp : rdProgN.noInp = true := by kernel_rfl

theorem rdProgN_noRand : rdProgN.noRand = true := by kernel_rfl

lemma ind_eq (f : ℕ) : (1 - (f - 1)) - (1 - f) = if f = 1 then 1 else 0 := by
  split_ifs <;> omega

theorem rdNA_exec {R : RdN} {Vb : ℕ} (hL : RdNLay R Vb W) (c : Config) (hc : WordsBounded W c)
    {e : ℕ} (hI : RdNIn R c) (h311 : c.nreg 311 = e) (h312 : c.nreg 312 = 1)
    (he : e < R.b * R.b)
    (hsg : ∀ s < R.b, c.nmem (R.Sg + s) = R.σ s) :
    ∃ c' k, Exec P W rdNA c c' k ∧ k = 16 ∧
      c'.nreg 313 = e / R.b ∧ c'.nreg 314 = e % R.b ∧
      c'.nreg 317 = R.ad (e / R.b) (e % R.b) ∧
      c'.nreg 319 = c.nmem (R.OUTb + R.ad (e / R.b) (e % R.b)) ∧
      c'.nreg 320 = (if c.nmem (R.RBb + R.ad (e / R.b) (e % R.b)) = 1 then 1 else 0) ∧
      (∀ r, r < 313 ∨ 321 < r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hb : 0 < R.b := by
    rcases Nat.eq_zero_or_pos R.b with h | h
    · rw [h] at he; simp at he
    · exact h
  have hs : e / R.b < R.b := Nat.div_lt_of_lt_mul he
  have ht : e % R.b < R.b := Nat.mod_lt _ hb
  have hσs := hL.σlt _ hs
  have hσt := hL.σlt _ ht
  have had : R.σ (e / R.b) * R.k + R.σ (e % R.b) < R.k * R.k := by
    have := Nat.mul_le_mul_right R.k (show R.σ (e / R.b) + 1 ≤ R.k by omega)
    rw [Nat.add_mul, one_mul] at this
    rw [Nat.mul_comm R.k R.k] at this ⊢
    omega
  have hsk : R.σ (e / R.b) * R.k ≤ R.k * R.k :=
    Nat.mul_le_mul_right _ hσs.le
  have hwS := hL.wS; have hwR := hL.wR; have hwO := hL.wO; have hwk := hL.wk; have hwb := hL.wb
  have hdl : e / R.b ≤ e := Nat.div_le_self _ _
  have hml : e % R.b ≤ e := Nat.mod_le _ _
  have r300 := hI.r300; have r301 := hI.r301; have r304 := hI.r304; have r305 := hI.r305
  have r306 := hI.r306
  have gs := hsg _ hs
  have gt := hsg _ ht
  unfold rdNA
  exec_block
  all_goals try
    ((try config_simp); (try simp only [r300, r301, r304, r305, r306, h311, h312, gs, gt]);
      omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r300, h311]
  · config_simp; simp only [r300, h311]
  · config_simp; simp only [r300, r301, r306, h311, gs, gt]; rfl
  · config_simp; simp only [r300, r301, r305, r306, h311, gs, gt]; rfl
  · config_simp; simp only [r300, r301, r304, r306, h311, h312, gs, gt]
    rw [ind_eq]; rfl
  · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl

theorem rdNB_exec {R : RdN} {Vb : ℕ} (hL : RdNLay R Vb W) (c : Config) (hc : WordsBounded W c)
    {e s t ind v : ℕ} (hI : RdNIn R c) (h311 : c.nreg 311 = e) (h312 : c.nreg 312 = 1)
    (he : e < R.b * R.b) (h313 : c.nreg 313 = s) (h314 : c.nreg 314 = t) (hs : s < R.b)
    (ht : t < R.b) (h319 : c.nreg 319 = v) (hv : v ≤ Vb) (h320 : c.nreg 320 = ind)
    (hind : ind ≤ 1)
    (hnb : ∀ s < R.b, c.nmem (R.Nb + s) = R.ν s)
    (hδ : ∀ x < R.w, c.nmem (R.D0 + x) < R.M) :
    ∃ c' k, Exec P W rdNB c c' k ∧ k = 18 ∧
      c'.nmem = upd (upd c.nmem (R.Fb + e) ind) (R.L0 + e)
        ((v + c.nmem (R.D0 + R.ν t) + R.M - c.nmem (R.D0 + R.ν s)) % R.M * ind) ∧
      c'.nreg 311 = e + 1 ∧
      (∀ r, r < 322 ∨ 325 < r → r ≠ 311 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hνs := hL.νlt _ hs
  have hνt := hL.νlt _ ht
  have hδs := hδ _ hνs
  have hδt := hδ _ hνt
  have hwN := hL.wN; have hwD := hL.wD; have hwF := hL.wF; have hwL := hL.wL; have hwV := hL.wV
  have hwb := hL.wb
  have r302 := hI.r302; have r303 := hI.r303; have r307 := hI.r307; have r308 := hI.r308
  have r309 := hI.r309
  have gs := hnb _ hs
  have gt := hnb _ ht
  have hmod : (v + c.nmem (R.D0 + R.ν t) + R.M - c.nmem (R.D0 + R.ν s)) % R.M ≤
      v + c.nmem (R.D0 + R.ν t) + R.M - c.nmem (R.D0 + R.ν s) := Nat.mod_le _ _
  have hmul : (v + c.nmem (R.D0 + R.ν t) + R.M - c.nmem (R.D0 + R.ν s)) % R.M * ind ≤
      (v + c.nmem (R.D0 + R.ν t) + R.M - c.nmem (R.D0 + R.ν s)) % R.M := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hind with h | h <;> simp [h]
  unfold rdNB
  exec_block
  all_goals try
    ((try config_simp);
      (try simp only [r302, r303, r307, r308, r309, h311, h312, h313, h314, h319, h320, gs, gt]);
      omega)
  refine ⟨rfl, ?_, ?_, fun r hr hr' => ?_, rfl, rfl, rfl⟩
  · config_simp
    simp only [r302, r303, r307, r308, r309, h311, h312, h313, h314, h319, h320, gs, gt]
  · config_simp; simp only [h311, h312]
  · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl

/-- The state of the reading loop after the entries `e' < r311`, from `c₀`. -/
structure RdNInv (R : RdN) (W : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  regs : ∀ r, r < 310 ∨ 325 < r → c.nreg r = c₀.nreg r
  r310 : c.nreg 310 = R.b * R.b
  r312 : c.nreg 312 = 1
  done : ∀ e < c.nreg 311, c.nmem (R.Fb + e) = R.flag c₀ (e / R.b) (e % R.b) ∧
    c.nmem (R.L0 + e) = R.val c₀ (e / R.b) (e % R.b)
  keep : ∀ a, (a < R.Fb ∨ R.Fb + c.nreg 311 ≤ a) → (a < R.L0 ∨ R.L0 + c.nreg 311 ≤ a) →
    c.nmem a = c₀.nmem a
  rr : c.rreg = c₀.rreg
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output

set_option maxHeartbeats 1000000 in
theorem rdNStep_exec {R : RdN} {Vb : ℕ} (hL : RdNLay R Vb W) {c₀ : Config} (hI₀ : RdNIn R c₀)
    (hV : ∀ a < R.k * R.k, c₀.nmem (R.OUTb + a) ≤ Vb)
    (hδ : ∀ x < R.w, c₀.nmem (R.D0 + x) < R.M)
    (c : Config) (hI : RdNInv R W c₀ c) (hlt : c.nreg 311 < R.b * R.b) :
    ∃ c' k, Exec P W rdNBody c c' k ∧ RdNInv R W c₀ c' ∧ c'.nreg 311 = c.nreg 311 + 1 ∧
      k = 34 := by
  generalize he : c.nreg 311 = e at hlt
  have hb : 0 < R.b := by
    rcases Nat.eq_zero_or_pos R.b with h | h
    · rw [h] at hlt; simp at hlt
    · exact h
  have hs : e / R.b < R.b := Nat.div_lt_of_lt_mul hlt
  have ht : e % R.b < R.b := Nat.mod_lt _ hb
  have hg : ∀ r, 300 ≤ r → r ≤ 309 → c.nreg r = c₀.nreg r := fun r h1 h2 =>
    hI.regs r (by omega)
  have hIc : RdNIn R c :=
    ⟨(hg 300 le_rfl (by omega)).trans hI₀.r300, (hg 301 (by omega) (by omega)).trans hI₀.r301,
      (hg 302 (by omega) (by omega)).trans hI₀.r302, (hg 303 (by omega) (by omega)).trans hI₀.r303,
      (hg 304 (by omega) (by omega)).trans hI₀.r304, (hg 305 (by omega) (by omega)).trans hI₀.r305,
      (hg 306 (by omega) (by omega)).trans hI₀.r306, (hg 307 (by omega) (by omega)).trans hI₀.r307,
      (hg 308 (by omega) (by omega)).trans hI₀.r308, (hg 309 (by omega) le_rfl).trans hI₀.r309,
      fun s hs' => by
        have := hL.fS; have := hL.lS
        rw [hI.keep _ (by omega) (by omega)]; exact hI₀.sg s hs',
      fun s hs' => by
        have := hL.fN; have := hL.lN
        rw [hI.keep _ (by omega) (by omega)]; exact hI₀.nb s hs'⟩
  have hsg : ∀ s < R.b, c.nmem (R.Sg + s) = R.σ s := hIc.sg
  obtain ⟨c₁, k₁, e₁, hk₁, g313, g314, g317, g319, g320, gn₁, gm₁, gr₁, grm₁, go₁⟩ :=
    rdNA_exec (P := P) hL c hI.wb hIc he hI.r312 hlt hsg
  have had : R.ad (e / R.b) (e % R.b) < R.k * R.k := by
    have hσs := hL.σlt _ hs
    have hσt := hL.σlt _ ht
    have := Nat.mul_le_mul_right R.k (show R.σ (e / R.b) + 1 ≤ R.k by omega)
    rw [Nat.add_mul, one_mul] at this
    unfold RdN.ad; omega
  have hkO : c.nmem (R.OUTb + R.ad (e / R.b) (e % R.b)) =
      c₀.nmem (R.OUTb + R.ad (e / R.b) (e % R.b)) := by
    have := hL.fO; have := hL.lO
    exact hI.keep _ (by omega) (by omega)
  have hkR : c.nmem (R.RBb + R.ad (e / R.b) (e % R.b)) =
      c₀.nmem (R.RBb + R.ad (e / R.b) (e % R.b)) := by
    have := hL.fR; have := hL.lR
    exact hI.keep _ (by omega) (by omega)
  have hkD : ∀ x < R.w, c.nmem (R.D0 + x) = c₀.nmem (R.D0 + x) := fun x hx => by
    have := hL.fD; have := hL.lD
    exact hI.keep _ (by omega) (by omega)
  have hg₁ : ∀ r, 300 ≤ r → r ≤ 309 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    gn₁ r (by omega)
  have hIc₁ : RdNIn R c₁ :=
    ⟨(hg₁ 300 le_rfl (by omega)).trans hIc.r300, (hg₁ 301 (by omega) (by omega)).trans hIc.r301,
      (hg₁ 302 (by omega) (by omega)).trans hIc.r302,
      (hg₁ 303 (by omega) (by omega)).trans hIc.r303,
      (hg₁ 304 (by omega) (by omega)).trans hIc.r304,
      (hg₁ 305 (by omega) (by omega)).trans hIc.r305,
      (hg₁ 306 (by omega) (by omega)).trans hIc.r306,
      (hg₁ 307 (by omega) (by omega)).trans hIc.r307,
      (hg₁ 308 (by omega) (by omega)).trans hIc.r308, (hg₁ 309 (by omega) le_rfl).trans hIc.r309,
      fun s hs' => by rw [gm₁]; exact hIc.sg s hs', fun s hs' => by rw [gm₁]; exact hIc.nb s hs'⟩
  obtain ⟨c₂, k₂, e₂, hk₂, gm₂, g311, gn₂, gr₂, grm₂, go₂⟩ :=
    rdNB_exec (P := P) hL c₁ e₁.wb_right (e := e) (s := e / R.b) (t := e % R.b) hIc₁
      (by rw [gn₁ 311 (by omega), he]) (by rw [gn₁ 312 (by omega)]; exact hI.r312) hlt g313 g314
      hs ht g319 (by rw [hkO]; exact hV _ had) g320 (by split_ifs <;> omega)
      (fun s hs' => by rw [gm₁]; exact hIc.nb s hs')
      (fun x hx => by rw [gm₁, hkD x hx]; exact hδ x hx)
  refine ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, ⟨e₂.wb_right, fun r hr => ?_, ?_, ?_, fun e' he' => ?_,
    fun a ha ha' => ?_, by rw [gr₂, gr₁, hI.rr], by rw [grm₂, grm₁, hI.rm],
    by rw [go₂, go₁, hI.out]⟩, by rw [g311], by omega⟩
  · rw [gn₂ r (by omega) (by omega), gn₁ r (by omega)]; exact hI.regs r hr
  · rw [gn₂ 310 (by omega) (by omega), gn₁ 310 (by omega)]; exact hI.r310
  · rw [gn₂ 312 (by omega) (by omega), gn₁ 312 (by omega)]; exact hI.r312
  · rw [g311] at he'
    have hfl := hL.fl
    rw [gm₂, gm₁]
    simp only [upd_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.1 he' with he' | rfl
    · obtain ⟨d1, d2⟩ := hI.done e' (by omega)
      refine ⟨?_, ?_⟩ <;> split_ifs <;> first | omega | assumption
    · have e1 : R.Fb + e' ≠ R.L0 + e' := by
        have := hL.fl; intro h; rcases this with h' | h' <;> omega
      have hfl' : R.flag c₀ (e' / R.b) (e' % R.b) =
          if c₀.nmem (R.RBb + R.ad (e' / R.b) (e' % R.b)) = 1 then 1 else 0 := rfl
      refine ⟨?_, ?_⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false e1),
          ite_eq_left_of_eq_true _ _ (eq_true rfl), hkR, hfl']
      · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
        unfold RdN.val
        rw [hkR, hkO, hkD _ (hL.νlt _ ht), hkD _ (hL.νlt _ hs)]
        split_ifs <;> simp
  · rw [g311] at ha ha'
    rw [gm₂, gm₁]
    simp only [upd_apply]
    split_ifs <;> first | omega | exact hI.keep a (by omega) (by omega)

set_option maxHeartbeats 1000000 in
/-- **The reading on natural words** (see the module docstring): from `RdNIn`, with `RdNLay`,
the answer words bounded by `Vb` and the residues of the potentials below `M`, `rdProgN` runs
within `36 b² + 5` steps and writes, for every pair `s, t < b`, the flag `[f = 1]` at
`Fb + (s b + t)` and the residue `[f = 1] · ((v + δ'(ν t) + M - δ'(ν s)) mod M)` at
`L0 + (s b + t)` (`RdN.flag`, `RdN.val`); every other memory cell, the registers outside
`310 … 325`, the reals and the output are kept. -/
theorem rdProgN_exec {R : RdN} {Vb : ℕ} (hL : RdNLay R Vb W) (c : Config) (hc : WordsBounded W c)
    (hI : RdNIn R c) (hV : ∀ a < R.k * R.k, c.nmem (R.OUTb + a) ≤ Vb)
    (hδ : ∀ x < R.w, c.nmem (R.D0 + x) < R.M) :
    ∃ c' k, Exec P W rdProgN c c' k ∧ k ≤ 36 * (R.b * R.b) + 5 ∧
      (∀ s < R.b, ∀ t < R.b, c'.nmem (R.Fb + (s * R.b + t)) = R.flag c s t ∧
        c'.nmem (R.L0 + (s * R.b + t)) = R.val c s t) ∧
      (∀ a, (a < R.Fb ∨ R.Fb + R.b * R.b ≤ a) → (a < R.L0 ∨ R.L0 + R.b * R.b ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, r < 310 ∨ 325 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hwb := hL.wb
  have r300 := hI.r300
  unfold rdProgN
  obtain ⟨c₁, k₁, e₁, hk₁, g312, g311, g310, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 312 1, .constN 311 0, .mulN 310 300 300]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 312 = 1 ∧ c₁.nreg 311 = 0 ∧ c₁.nreg 310 = R.b * R.b ∧
      (∀ r, r < 310 ∨ 312 < r → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [r300]); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp
    · config_simp; simp only [r300]
    · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl
  have hJ0 : RdNInv R W c c₁ := ⟨e₁.wb_right, fun r hr => gn₁ r (by omega), g310, g312,
    fun e he => by rw [g311] at he; omega, fun a _ _ => by rw [gm₁], gr₁, grm₁, go₁⟩
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ₂, h₂⟩ := forLoop_exec (P := P) (a := 311) (bR := 310)
    (body := rdNBody) (fun i c' => RdNInv R W c c' ∧ c'.nreg 311 = i) (K := 34)
    (n := R.b * R.b) c₁ e₁.wb_right g311 g310 ⟨hJ0, g311⟩ (fun i c' hi hw ha hb hJ => by
      obtain ⟨c'', k, ex, hJ', h311, hk⟩ := rdNStep_exec (P := P) hL hI hV hδ c' hJ.1
        (by rw [hJ.2]; exact hi)
      exact ⟨c'', k, ex, by omega, by rw [h311, hJ.2], hJ'.r310, hJ', by rw [h311, hJ.2]⟩)
  refine ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by omega, fun s hs t ht => ?_, fun a ha ha' => ?_,
    fun r hr => hJ₂.regs r hr, hJ₂.rr, hJ₂.rm, hJ₂.out⟩
  · have hst : s * R.b + t < R.b * R.b := by
      have := Nat.mul_le_mul_right R.b (show s + 1 ≤ R.b by omega)
      rw [Nat.add_mul, one_mul] at this
      omega
    have hb : 0 < R.b := by omega
    have e1 : (s * R.b + t) / R.b = s := by
      rw [add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt ht, zero_add]
    have e2 : (s * R.b + t) % R.b = t := by
      rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
    have := hJ₂.done (s * R.b + t) (by rw [h₂]; exact hst)
    rw [e1, e2] at this
    exact this
  · exact hJ₂.keep a (by rw [h₂]; exact ha) (by rw [h₂]; exact ha')

end NegSSSP

end PlanarFlow
