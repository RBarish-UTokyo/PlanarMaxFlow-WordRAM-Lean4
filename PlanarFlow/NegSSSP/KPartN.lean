module

public import PlanarFlow.NegSSSP.KNatFace
public import PlanarFlow.NegSSSP.ReadNat

/-!
# One part of a node on natural words

`NegSSSP.kPart` (`PlanarFlow/NegSSSP/NodeRunD.lean`) runs Klein's program with real registers on
the perturbed lengths and reads its answers by a real-side binary search. `kPartN` is the same
part **on natural words**, inside the natural configuration of the node (whose reals are kept
modulo the node's modulus `M` at `βN + a`):

* `cpyNProg`, `fillNProg`: copying and clearing natural cells (`cpyNProg_exec`, `fillNProg_exec`).
* `kPartN`: the corners (`cornerProg`), the input words of Klein's encoding copied right above
  the work space (to `Kw + 1`), Klein's real image at `βK` cleared and the residues of its real
  constants copied there, the registers `< 404` cleared, Klein's program on natural words with
  the isolating lengths and the read-back by `divN` (`Klein.kleinMemNDC`), and the reading of
  the answers into the layout of `bfStartP` (`rdProgN`), the values as residues modulo `M` at
  `βN + Ys + 3 S + …`; finally the scratch registers (`< 408`, `910 … 918`) cleared.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-! ### Copying and clearing natural cells -/

/-- For `e = r915 < r910`: `nmem[r911 + e] := nmem[r912 + e]`. -/
def cpyNBody : Stmt :=
  block [.addN 917 912 915, .loadN 918 917, .addN 917 911 915, .storeN 917 918,
    .addN 915 915 916]

/-- **The copy of `len` natural cells from `Src` to `Dst`.** -/
def cpyNProg (Dst Src len : ℕ) : Stmt :=
  .seq (block [.constN 910 len, .constN 911 Dst, .constN 912 Src, .constN 916 1, .constN 915 0])
    (.whileLtN 915 910 cpyNBody)

/-- For `e = r915 < r910`: `nmem[r911 + e] := 0` (`r913 = 0`). -/
def fillNBody : Stmt := block [.addN 917 911 915, .storeN 917 913, .addN 915 915 916]

/-- **Clearing `len` natural cells from `Dst`.** -/
def fillNProg (Dst len : ℕ) : Stmt :=
  .seq (block [.constN 910 len, .constN 911 Dst, .constN 913 0, .constN 916 1, .constN 915 0])
    (.whileLtN 915 910 fillNBody)

theorem cpyNProg_natOnly (Dst Src len : ℕ) : Klein.natOnly (cpyNProg Dst Src len) = true := by
  kernel_rfl

theorem fillNProg_natOnly (Dst len : ℕ) : Klein.natOnly (fillNProg Dst len) = true := by
  kernel_rfl

theorem cpyNBody_exec (c : Config) (hc : WordsBounded W c) {Dst Src e : ℕ}
    (r911 : c.nreg 911 = Dst) (r912 : c.nreg 912 = Src) (r915 : c.nreg 915 = e)
    (r916 : c.nreg 916 = 1) (w1 : Dst + e ≤ W) (w2 : Src + e ≤ W) (w3 : e + 1 ≤ W) :
    ∃ c' k, Exec P W cpyNBody c c' k ∧ k = 5 ∧
      c'.nmem = upd c.nmem (Dst + e) (c.nmem (Src + e)) ∧ c'.nreg 915 = e + 1 ∧
      (∀ r, r ≠ 915 → r ≠ 917 → r ≠ 918 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cpyNBody
  exec_block
  all_goals try ((try config_simp); (try simp only [r911, r912, r915, r916]); omega)
  refine ⟨rfl, ?_, ?_, fun r hr1 hr2 hr3 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r911, r912, r915]
  · config_simp; simp only [r915, r916]
  · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl

theorem fillNBody_exec (c : Config) (hc : WordsBounded W c) {Dst e : ℕ}
    (r911 : c.nreg 911 = Dst) (r913 : c.nreg 913 = 0) (r915 : c.nreg 915 = e)
    (r916 : c.nreg 916 = 1) (w1 : Dst + e ≤ W) (w3 : e + 1 ≤ W) :
    ∃ c' k, Exec P W fillNBody c c' k ∧ k = 3 ∧
      c'.nmem = upd c.nmem (Dst + e) 0 ∧ c'.nreg 915 = e + 1 ∧
      (∀ r, r ≠ 915 → r ≠ 917 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fillNBody
  exec_block
  all_goals try ((try config_simp); (try simp only [r911, r913, r915, r916]); omega)
  refine ⟨rfl, ?_, ?_, fun r hr1 hr2 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r911, r913, r915]
  · config_simp; simp only [r915, r916]
  · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl

theorem cpyNProg_exec {Dst Src len : ℕ} (hd : Dst + len ≤ Src ∨ Src + len ≤ Dst)
    (hW1 : Dst + len ≤ W) (hW2 : Src + len ≤ W) (h1 : 1 ≤ W) (c : Config)
    (hc : WordsBounded W c) :
    ∃ c' k, Exec P W (cpyNProg Dst Src len) c c' k ∧ k ≤ 7 * len + 7 ∧
      (∀ e < len, c'.nmem (Dst + e) = c.nmem (Src + e)) ∧
      (∀ a, (a < Dst ∨ Dst + len ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 910 ∨ 918 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cpyNProg
  obtain ⟨c₁, k₁, e₁, hk₁, g910, g911, g912, g916, g915, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 910 len, .constN 911 Dst, .constN 912 Src, .constN 916 1,
        .constN 915 0]) c c₁ k₁ ∧ k₁ = 5 ∧ c₁.nreg 910 = len ∧ c₁.nreg 911 = Dst ∧
      c₁.nreg 912 = Src ∧ c₁.nreg 916 = 1 ∧ c₁.nreg 915 = 0 ∧
      (∀ r, r < 910 ∨ 918 < r → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> first | omega | rfl
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ e < i, c'.nmem (Dst + e) = c.nmem (Src + e)) ∧
      (∀ a, (a < Dst ∨ Dst + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 910 ∨ 918 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 911 = Dst ∧
      c'.nreg 912 = Src ∧ c'.nreg 916 = 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 915) (bR := 910) (body := cpyNBody)
    J (K := 5) (n := len) c₁ e₁.wb_right g915 g910
    ⟨fun e he => absurd he (by omega), fun a _ => by rw [gm₁], gn₁, g911, g912, g916, gr₁,
      grm₁, go₁⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j3, j911, j912, j916, jr, jrm, jo⟩ := hJ
      have hsrc : c'.nmem (Src + i) = c.nmem (Src + i) := j2 _ (by omega)
      obtain ⟨c'', k, ex, hk, hm, h915, hn, hr, hrm, ho⟩ := cpyNBody_exec (P := P) c' hw j911 j912
        ha j916 (by omega) (by omega) (by omega)
      refine ⟨c'', k, ex, by omega, h915, by rw [hn 910 (by omega) (by omega) (by omega)]; exact hb,
        fun e he => ?_, fun a h => ?_, fun r hr' => ?_, by rw [hn 911 (by omega) (by omega) (by omega)]; exact j911,
        by rw [hn 912 (by omega) (by omega) (by omega)]; exact j912, by rw [hn 916 (by omega) (by omega) (by omega)]; exact j916,
        by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩
      · rw [hm, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact j1 e he
        · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), hsrc]
      · rw [hm, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact j2 a (by omega)
      · rw [hn r (by omega) (by omega) (by omega)]; exact j3 r hr')
  obtain ⟨j1, j2, j3, -, -, -, jr, jrm, jo⟩ := hJ
  exact ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by omega, j1, j2, j3, jr, jrm, jo⟩

theorem fillNProg_exec {Dst len : ℕ} (hW1 : Dst + len ≤ W) (h1 : 1 ≤ W) (c : Config)
    (hc : WordsBounded W c) :
    ∃ c' k, Exec P W (fillNProg Dst len) c c' k ∧ k ≤ 5 * len + 7 ∧
      (∀ e < len, c'.nmem (Dst + e) = 0) ∧
      (∀ a, (a < Dst ∨ Dst + len ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 910 ∨ 918 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fillNProg
  obtain ⟨c₁, k₁, e₁, hk₁, g910, g911, g913, g916, g915, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 910 len, .constN 911 Dst, .constN 913 0, .constN 916 1,
        .constN 915 0]) c c₁ k₁ ∧ k₁ = 5 ∧ c₁.nreg 910 = len ∧ c₁.nreg 911 = Dst ∧
      c₁.nreg 913 = 0 ∧ c₁.nreg 916 = 1 ∧ c₁.nreg 915 = 0 ∧
      (∀ r, r < 910 ∨ 918 < r → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> first | omega | rfl
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ e < i, c'.nmem (Dst + e) = 0) ∧
      (∀ a, (a < Dst ∨ Dst + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 910 ∨ 918 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 911 = Dst ∧
      c'.nreg 913 = 0 ∧ c'.nreg 916 = 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 915) (bR := 910)
    (body := fillNBody) J (K := 3) (n := len) c₁ e₁.wb_right g915 g910
    ⟨fun e he => absurd he (by omega), fun a _ => by rw [gm₁], gn₁, g911, g913, g916, gr₁,
      grm₁, go₁⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j3, j911, j913, j916, jr, jrm, jo⟩ := hJ
      obtain ⟨c'', k, ex, hk, hm, h915, hn, hr, hrm, ho⟩ := fillNBody_exec (P := P) c' hw j911 j913
        ha j916 (by omega) (by omega)
      refine ⟨c'', k, ex, by omega, h915, by rw [hn 910 (by omega) (by omega)]; exact hb,
        fun e he => ?_, fun a h => ?_, fun r hr' => ?_, by rw [hn 911 (by omega) (by omega)]; exact j911,
        by rw [hn 913 (by omega) (by omega)]; exact j913, by rw [hn 916 (by omega) (by omega)]; exact j916,
        by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩
      · rw [hm, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact j1 e he
        · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      · rw [hm, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact j2 a (by omega)
      · rw [hn r (by omega) (by omega)]; exact j3 r hr')
  obtain ⟨j1, j2, j3, -, -, -, jr, jrm, jo⟩ := hJ
  exact ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by omega, j1, j2, j3, jr, jrm, jo⟩

/-! ### Residues of shifted distances -/

lemma res_shift {M : ℕ} (hM : 0 < M) {z : ℤ} (hz : 0 ≤ z) {δs δt : ℤ} {a b : ℕ}
    (ha : ModNat.Res M (δt : ℝ) a) (hb : ModNat.Res M (δs : ℝ) b) (hbM : b < M) :
    ModNat.Res M ((z + (δt - δs) : ℤ) : ℝ) ((z.toNat + a + M - b) % M) := by
  obtain ⟨z1, h1, ha'⟩ := ha
  obtain ⟨z2, h2, hb'⟩ := hb
  have e1 : z1 = δt := by exact_mod_cast h1.symm
  have e2 : z2 = δs := by exact_mod_cast h2.symm
  subst e1 e2
  refine ⟨z + (z1 - z2), rfl, ?_⟩
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  have hsub : ((z.toNat + a + M - b : ℕ) : ℤ) = z + a + M - b := by
    rw [Nat.cast_sub (by omega)]; push_cast; rw [Int.toNat_of_nonneg hz]
  rw [Int.natCast_mod, hsub]
  have hA : (a : ℤ) % M = z1 % M := by rw [ha', Int.emod_emod_of_dvd _ (dvd_refl _)]
  have hB : (b : ℤ) % M = z2 % M := by rw [hb', Int.emod_emod_of_dvd _ (dvd_refl _)]
  have : z + a + M - b = (z + (z1 - z2)) + (a - z1) + M - (b - z2) := by ring
  rw [this]
  have h3 : (M : ℤ) ∣ (a - z1) := Int.ModEq.dvd hA.symm
  have h4 : (M : ℤ) ∣ (b - z2) := Int.ModEq.dvd hB.symm
  obtain ⟨u, hu⟩ := h3
  obtain ⟨v, hv⟩ := h4
  rw [hu, hv]
  have : z + (z1 - z2) + M * u + M - M * v = z + (z1 - z2) + M * (u + 1 - v) := by ring
  rw [this, Int.add_mul_emod_self_left]

/-! ### The part -/

/-- The constants of the natural program of one part. -/
structure KPN where
  k : ℕ
  nD : ℕ
  n : ℕ
  Bw : ℕ
  len : ℕ
  β : ℕ
  RkN : ℕ
  Pb : ℕ
  Hc : ℕ
  N1 : ℕ
  Wc : ℕ
  βK : ℕ
  βN : ℕ
  M : ℕ

/-- The work space of Klein's program of a part. -/
def KPN.Kw (p : KPN) : ℕ := p.Bw + 16 * (p.n + 1)

/-- Before `rdProgN`: the data of `RdNIn` (the potentials and the outputs of residues at
`βN + …`). -/
def kpRN (k n OUTb βN M : ℕ) : Stmt :=
  block [.copyN 300 802, .copyN 301 963, .copyN 302 962, .constN 303 βN, .addN 303 303 966,
    .constN 304 n, .constN 305 OUTb, .constN 306 k, .copyN 307 964, .constN 308 βN,
    .addN 308 308 964, .constN 309 M]

/-- **One part of a node on natural words** (see the module docstring). -/
def kPartN (p : KPN) : Stmt :=
  .seq (kpC p.k p.Pb) <| .seq cornerProg <|
  .seq (cpyNProg (p.Kw + 1) p.β (p.Kw + 1)) <| .seq (fillNProg p.βK (2 * p.Kw + 2)) <|
  .seq (cpyNProg p.βK p.RkN (3 * p.nD + 3)) <| .seq (zeroRegs (List.range 404)) <|
  .seq (Klein.kleinMemNDC p.Bw p.nD p.n p.k p.k (p.Kw + 1) p.len p.Hc p.βK p.N1 p.Wc) <|
  .seq (kpRN p.k p.n (p.βK + Klein.aOUT p.nD) p.βN p.M) <| .seq rdProgN
    (zeroRegs (List.range 408 ++ List.range' 910 9))

/-- **`kPartN` has no real instruction and no real test.** -/
theorem kPartN_natOnly (p : KPN) : Klein.natOnly (kPartN p) = true := by
  have h1 : Klein.natOnly cornerProg = true := by decide +kernel
  have h2 : Klein.natOnly (zeroRegs (List.range 404)) = true := by decide +kernel
  have h3 : Klein.natOnly (kpC p.k p.Pb) = true := by kernel_rfl
  have h4 : Klein.natOnly (kpRN p.k p.n (p.βK + Klein.aOUT p.nD) p.βN p.M) = true := by
    kernel_rfl
  have h5 : Klein.natOnly (zeroRegs (List.range 408 ++ List.range' 910 9)) = true := by
    decide +kernel
  simp only [kPartN, Klein.natOnly, h1, h2, h3, h4, cpyNProg_natOnly, fillNProg_natOnly,
    Klein.kleinMemNDC_natOnly, rdProgN_natOnly, h5, Bool.and_self]

theorem kpRN_exec {k n OUTb βN M : ℕ} (c : Config) (hc : WordsBounded W c) (hk : k ≤ W)
    (hn : n ≤ W) (hO : OUTb ≤ W) (hM : M ≤ W) (hβ : βN ≤ W) (h3 : βN + c.nreg 966 ≤ W)
    (h8 : βN + c.nreg 964 ≤ W) :
    ∃ c' t, Exec P W (kpRN k n OUTb βN M) c c' t ∧ t = 12 ∧
      c'.nreg 300 = c.nreg 802 ∧ c'.nreg 301 = c.nreg 963 ∧ c'.nreg 302 = c.nreg 962 ∧
      c'.nreg 303 = βN + c.nreg 966 ∧ c'.nreg 304 = n ∧ c'.nreg 305 = OUTb ∧
      c'.nreg 306 = k ∧ c'.nreg 307 = c.nreg 964 ∧ c'.nreg 308 = βN + c.nreg 964 ∧
      c'.nreg 309 = M ∧ (∀ r, (r < 300 ∨ 309 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold kpRN
  exec_block
  all_goals try ((try config_simp); omega)
  config_simp
  intro r h1; simp (disch := omega) only [upd_other]

end NegSSSP

end PlanarFlow
