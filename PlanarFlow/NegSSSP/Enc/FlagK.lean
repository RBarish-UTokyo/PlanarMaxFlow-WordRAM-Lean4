module

public import PlanarFlow.NegSSSP.SplitRunX
public import PlanarFlow.NegSSSP.Enc.RedLenN

/-!
# The flags `bK` of the large component in the numbering of its piece map

`sdWalk_exec` reads the flags `bK[cn x] = [x.1 ∈ K]` for the darts `x` of the piece map
`kmap N K` (`flK`). `encProg` writes them at `B₀ + 5 m'`, but the separator run overwrites that
scratch. They are rebuilt after `bigProg` from what survives (`bigProg_spec'`): the flags of
`K` in the order of the piece (`F[h] ≠ 0 ↔ δ h ∈ K`, `h < m`) and the index array
`X[h] = cn (δ h)`.

`bkProg` (registers `2764 … 2775`): `OUT[j] := 0` for `j < m'`, then `OUT[X[h]] := 1` for every
`h < m` with `F[h] ≠ 0`.

* **`bkProg_exec`** (generic): within `5 m' + 13 m + 10` steps,
  `OUT[j] = [∃ h < m, F[h] ≠ 0 ∧ X[h] = j]` for `j < m'`; memory outside `[Kb, Kb + m')`,
  registers outside `[2764, 2775]`, reals, output kept.
* **`bk_flK`**: with the facts of `bigProg_spec'` (`PEnc`, the index array, the flags), that
  value at `cn x` is `[x.1 ∈ K]`: exactly the hypothesis `hKB` of `sdWalk_exec`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- `OUT[i] := 0` (`i = r2766`). -/
def bkZ : Stmt := block [.addN 2768 2765 2766, .storeN 2768 2767, .addN 2766 2766 2769]

/-- The load of `F[h]` (`h = r2766`) into `r2773`. -/
def bkL : Stmt := block [.addN 2773 2771 2766, .loadN 2773 2773]

/-- `OUT[X[h]] := 1`. -/
def bkS : Stmt := block [.addN 2774 2772 2766, .loadN 2774 2774, .addN 2774 2765 2774,
  .storeN 2774 2769]

/-- One step of the scatter. -/
def bkB : Stmt := .seq bkL (.seq (.ifLtN 2767 2773 bkS .skip) (block [.addN 2766 2766 2769]))

/-- **The flags of `K` by the numbering of the piece map** (`r2764 = m'`, `r2765 = Kb`,
`r2770 = m`, `r2771 = Fb`, `r2772 = Xb`). -/
def bkProg : Stmt :=
  .seq (block [.constN 2766 0, .constN 2767 0, .constN 2769 1]) <|
  .seq (.whileLtN 2766 2764 bkZ) <|
  .seq (block [.constN 2766 0]) (.whileLtN 2766 2770 bkB)

theorem bkProg_natOnly : Klein.natOnly bkProg = true := by kernel_rfl

/-- The value of the scatter after `i` steps. -/
def bkV (mem : ℕ → ℕ) (Fb Xb i j : ℕ) : ℕ :=
  if ∃ h < i, mem (Fb + h) ≠ 0 ∧ mem (Xb + h) = j then 1 else 0

theorem bkV_succ (mem : ℕ → ℕ) (Fb Xb i j : ℕ) :
    bkV mem Fb Xb (i + 1) j = if mem (Fb + i) ≠ 0 ∧ mem (Xb + i) = j then 1 else
      bkV mem Fb Xb i j := by
  unfold bkV
  by_cases h : mem (Fb + i) ≠ 0 ∧ mem (Xb + i) = j
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨i, by omega, h⟩), ite_eq_left_of_eq_true _ _
      (eq_true h)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
    congr 1
    apply propext
    constructor
    · rintro ⟨h', h1, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h1 | rfl
      · exact ⟨h', h1, h2⟩
      · exact absurd h2 h
    · rintro ⟨h', h1, h2⟩; exact ⟨h', by omega, h2⟩

theorem bkZ_exec (c : Config) (hc : WordsBounded W c) {Kb i : ℕ} (r65 : c.nreg 2765 = Kb)
    (r66 : c.nreg 2766 = i) (r67 : c.nreg 2767 = 0) (r69 : c.nreg 2769 = 1) (w1 : Kb + i ≤ W)
    (w2 : i + 1 ≤ W) :
    ∃ c' k, Exec P W bkZ c c' k ∧ k = 3 ∧ c'.nmem = upd c.nmem (Kb + i) 0 ∧
      c'.nreg 2766 = i + 1 ∧ (∀ r, r ≠ 2766 → r ≠ 2768 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bkZ
  exec_block
  all_goals try ((try config_simp); (try simp only [r65, r66, r67, r69]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r65, r66, r67]
  · config_simp; simp only [r66, r69]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem bkB_exec (c : Config) (hc : WordsBounded W c) {Kb Fb Xb m' h : ℕ}
    (r65 : c.nreg 2765 = Kb) (r66 : c.nreg 2766 = h) (r67 : c.nreg 2767 = 0)
    (r69 : c.nreg 2769 = 1) (r71 : c.nreg 2771 = Fb) (r72 : c.nreg 2772 = Xb)
    (w1 : Fb + h ≤ W) (w2 : Xb + h ≤ W) (w3 : h + 1 ≤ W) (w4 : Kb + m' ≤ W)
    (hX : c.nmem (Fb + h) ≠ 0 → c.nmem (Xb + h) < m') :
    ∃ c' k, Exec P W bkB c c' k ∧ k ≤ 11 ∧
      c'.nmem = (if c.nmem (Fb + h) ≠ 0 then upd c.nmem (Kb + c.nmem (Xb + h)) 1 else c.nmem) ∧
      c'.nreg 2766 = h + 1 ∧
      (∀ r, r ≠ 2766 → r ≠ 2773 → r ≠ 2774 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bkB
  obtain ⟨c₁, k₁, e₁, hk₁, g73, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁, Exec P W bkL c c₁ k₁ ∧
      k₁ = 2 ∧ c₁.nreg 2773 = c.nmem (Fb + h) ∧ (∀ r, r ≠ 2773 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold bkL
    exec_block
    all_goals try ((try config_simp); (try simp only [r66, r71]); omega)
    refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [r66, r71]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  obtain ⟨c₂, k₂, e₂, hk₂, gm₂, gn₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
      Exec P W (.ifLtN 2767 2773 bkS .skip) c₁ c₂ k₂ ∧ k₂ ≤ 5 ∧
      c₂.nmem = (if c.nmem (Fb + h) ≠ 0 then upd c.nmem (Kb + c.nmem (Xb + h)) 1 else
        c.nmem) ∧ (∀ r, r ≠ 2774 → c₂.nreg r = c₁.nreg r) ∧
      c₂.rreg = c.rreg ∧ c₂.rmem = c.rmem ∧ c₂.output = c.output := by
    by_cases hf : c.nmem (Fb + h) ≠ 0
    · have hlt : c₁.nreg 2767 < c₁.nreg 2773 := by
        rw [gn₁ 2767 (by omega), r67, g73]; omega
      obtain ⟨c₃, k₃, e₃, hk₃, h3m, h3n, h3r, h3rm, h3o⟩ : ∃ c₃ k₃, Exec P W bkS c₁ c₃ k₃ ∧
          k₃ = 4 ∧ c₃.nmem = upd c.nmem (Kb + c.nmem (Xb + h)) 1 ∧
          (∀ r, r ≠ 2774 → c₃.nreg r = c₁.nreg r) ∧ c₃.rreg = c.rreg ∧ c₃.rmem = c.rmem ∧
          c₃.output = c.output := by
        have := hX hf
        have q65 : c₁.nreg 2765 = Kb := by rw [gn₁ _ (by omega), r65]
        have q66 : c₁.nreg 2766 = h := by rw [gn₁ _ (by omega), r66]
        have q69 : c₁.nreg 2769 = 1 := by rw [gn₁ _ (by omega), r69]
        have q72 : c₁.nreg 2772 = Xb := by rw [gn₁ _ (by omega), r72]
        have hw₁ := e₁.wb_right
        unfold bkS
        exec_block
        all_goals try ((try config_simp); (try simp only [q65, q66, q69, q72, gm₁]); omega)
        refine ⟨rfl, ?_, fun r h1 => ?_, by rw [gr₁], by rw [grm₁], by rw [go₁]⟩
        · config_simp; simp only [q65, q66, q69, q72, gm₁]
        · config_simp; simp only [upd_apply]; split_ifs <;> omega
      exact ⟨c₃, k₃ + 1, .ifLtN_true hlt e₃, by omega, by rw [h3m, ite_eq_left_of_eq_true _ _ (eq_true hf)], h3n, h3r, h3rm,
        h3o⟩
    · have hlt : ¬ c₁.nreg 2767 < c₁.nreg 2773 := by
        rw [gn₁ 2767 (by omega), r67, g73]; try omega
      exact ⟨c₁, 0 + 2, .ifLtN_false hlt (.skip e₁.wb_right), by omega,
        by rw [gm₁, ite_eq_right_of_eq_false _ _ (eq_false hf)], fun _ _ => rfl, gr₁, grm₁, go₁⟩
  have hw₂ := e₂.wb_right
  have q66 : c₂.nreg 2766 = h := by rw [gn₂ _ (by omega), gn₁ _ (by omega), r66]
  have q69 : c₂.nreg 2769 = 1 := by rw [gn₂ _ (by omega), gn₁ _ (by omega), r69]
  obtain ⟨c₃, k₃, e₃, hk₃, h66, hn₃, hm₃, hr₃, hrm₃, ho₃⟩ : ∃ c₃ k₃,
      Exec P W (block [.addN 2766 2766 2769]) c₂ c₃ k₃ ∧ k₃ = 1 ∧ c₃.nreg 2766 = h + 1 ∧
      (∀ r, r ≠ 2766 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [q66, q69]); omega)
    refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [q66, q69]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, by rw [hm₃, gm₂], h66,
    fun r h1 h2 h3 => ?_, by rw [hr₃, gr₂], by rw [hrm₃, grm₂], by rw [ho₃, go₂]⟩
  rw [hn₃ r h1, gn₂ r h3, gn₁ r h2]

/-- **The scatter of the flags on the machine** (see the module docstring). -/
theorem bkProg_exec {m' m Kb Fb Xb : ℕ} (c : Config) (hc : WordsBounded W c)
    (r64 : c.nreg 2764 = m') (r65 : c.nreg 2765 = Kb) (r70 : c.nreg 2770 = m)
    (r71 : c.nreg 2771 = Fb) (r72 : c.nreg 2772 = Xb) (h1 : 1 ≤ W)
    (wK : Kb + m' ≤ W) (wF : Fb + m ≤ W) (wX : Xb + m ≤ W)
    (dF : Kb + m' ≤ Fb ∨ Fb + m ≤ Kb) (dX : Kb + m' ≤ Xb ∨ Xb + m ≤ Kb)
    (hX : ∀ h < m, c.nmem (Fb + h) ≠ 0 → c.nmem (Xb + h) < m') :
    ∃ c' k, Exec P W bkProg c c' k ∧ k ≤ 5 * m' + 13 * m + 10 ∧
      (∀ j < m', c'.nmem (Kb + j) = bkV c.nmem Fb Xb m j) ∧
      (∀ a, (a < Kb ∨ Kb + m' ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2764 ∨ 2775 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bkProg
  obtain ⟨c₁, k₁, e₁, hk₁, g66, g67, g69, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 2766 0, .constN 2767 0, .constN 2769 1]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 2766 = 0 ∧ c₁.nreg 2767 = 0 ∧ c₁.nreg 2769 = 1 ∧
      (∀ r, r ≠ 2766 → r ≠ 2767 → r ≠ 2769 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, fun r a b d => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  -- the zeros
  let J₁ : ℕ → Config → Prop := fun i c' =>
    (∀ j < i, c'.nmem (Kb + j) = 0) ∧ (∀ a, (a < Kb ∨ Kb + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 2766 → r ≠ 2767 → r ≠ 2768 → r ≠ 2769 → c'.nreg r = c.nreg r) ∧
      c'.nreg 2767 = 0 ∧ c'.nreg 2769 = 1 ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, hJ₁⟩ := forLoop_exec (P := P) (a := 2766) (bR := 2764)
    (body := bkZ) J₁ (K := 3) (n := m') c₁ e₁.wb_right g66
    (by rw [gn₁ _ (by omega) (by omega) (by omega)]; exact r64)
    ⟨fun j hj => absurd hj (by omega), fun a _ => by rw [gm₁], fun r a b _ d => gn₁ r a b d,
      g67, g69, gr₁, grm₁, go₁⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j3, j67, j69, jr, jrm, jo⟩ := hJ
      obtain ⟨c'', k, ex, hk, hm, h66, hn, hr, hrm, ho⟩ := bkZ_exec (P := P) (Kb := Kb) (i := i) c' hw
        (by rw [j3 2765 (by omega) (by omega) (by omega) (by omega)]; exact r65) ha j67 j69
        (by omega) (by omega)
      refine ⟨c'', k, ex, by omega, h66, by rw [hn 2764 (by omega) (by omega)]; exact hb,
        fun j hj => ?_, fun a h => ?_, fun r a b d e => by rw [hn r a d]; exact j3 r a b d e,
        by rw [hn _ (by omega) (by omega)]; exact j67,
        by rw [hn _ (by omega) (by omega)]; exact j69, by rw [hr, jr], by rw [hrm, jrm],
        by rw [ho, jo]⟩
      · rw [hm, upd_apply]
        split_ifs with he
        · rfl
        · exact j1 j (by omega)
      · rw [hm, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact j2 a (by omega))
  obtain ⟨z1, z2, z3, z67, z69, zr, zrm, zo⟩ := hJ₁
  -- the scatter
  obtain ⟨c₃, k₃, e₃, hk₃, h66, hn₃, hm₃, hr₃, hrm₃, ho₃⟩ : ∃ c₃ k₃,
      Exec P W (block [.constN 2766 0]) c₂ c₃ k₃ ∧ k₃ = 1 ∧ c₃.nreg 2766 = 0 ∧
      (∀ r, r ≠ 2766 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  let J₂ : ℕ → Config → Prop := fun h c' =>
    (∀ j < m', c'.nmem (Kb + j) = bkV c.nmem Fb Xb h j) ∧
      (∀ a, (a < Kb ∨ Kb + m' ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2764 ∨ 2775 < r ∨ r = 2765 ∨ r = 2770 ∨ r = 2771 ∨ r = 2772) →
        c'.nreg r = c.nreg r) ∧
      c'.nreg 2767 = 0 ∧ c'.nreg 2769 = 1 ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output
  obtain ⟨c₄, k₄, e₄, hk₄, -, hJ₂⟩ := forLoop_exec (P := P) (a := 2766) (bR := 2770)
    (body := bkB) J₂ (K := 11) (n := m) c₃ e₃.wb_right h66
    (by rw [hn₃ _ (by omega), z3 _ (by omega) (by omega) (by omega) (by omega)]; exact r70)
    ⟨fun j hj => by
        rw [hm₃, z1 j hj]; unfold bkV
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by rintro ⟨h, hh, -⟩; omega))],
      fun a h => by rw [hm₃]; exact z2 a (by omega),
      fun r h => by rw [hn₃ r (by omega)]; exact z3 r (by omega) (by omega) (by omega) (by omega),
      by rw [hn₃ _ (by omega)]; exact z67, by rw [hn₃ _ (by omega)]; exact z69,
      by rw [hr₃, zr], by rw [hrm₃, zrm], by rw [ho₃, zo]⟩
    (fun h c' hh hw ha hb hJ => by
      obtain ⟨j1, j2, j3, j67, j69, jr, jrm, jo⟩ := hJ
      have eF : c'.nmem (Fb + h) = c.nmem (Fb + h) := j2 _ (by omega)
      have eX : c'.nmem (Xb + h) = c.nmem (Xb + h) := j2 _ (by omega)
      obtain ⟨c'', k, ex, hk, hm, h66', hn, hr, hrm, ho⟩ := bkB_exec (P := P) (m' := m') (Kb := Kb) (Fb := Fb) (Xb := Xb) (h := h) c' hw
        (by rw [j3 2765 (by omega)]; exact r65) ha j67 j69 (by rw [j3 2771 (by omega)]; exact r71)
        (by rw [j3 2772 (by omega)]; exact r72) (by omega) (by omega) (by omega) wK
        (fun hf => by rw [eX]; rw [eF] at hf; exact hX h hh hf)
      refine ⟨c'', k, ex, hk, h66', by rw [hn 2770 (by omega) (by omega) (by omega)]; exact hb,
        fun j hj => ?_, fun a ha' => ?_, fun r hr' => by
          rw [hn r (by omega) (by omega) (by omega)]; exact j3 r hr',
        by rw [hn _ (by omega) (by omega) (by omega)]; exact j67,
        by rw [hn _ (by omega) (by omega) (by omega)]; exact j69,
        by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩
      · rw [hm, bkV_succ, eF, eX]
        by_cases hf : c.nmem (Fb + h) ≠ 0
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hf), upd_apply]
          by_cases hj' : c.nmem (Xb + h) = j
          · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
              ite_eq_left_of_eq_true _ _ (eq_true ⟨hf, hj'⟩)]
          · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
              ite_eq_right_of_eq_false _ _ (eq_false (fun h' => hj' h'.2)), j1 j hj]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hf), ite_eq_right_of_eq_false _ _ (eq_false (fun h' => hf h'.1)), j1 j hj]
      · rw [hm, eF]
        by_cases hf : c.nmem (Fb + h) ≠ 0
        · have := hX h hh hf
          rw [ite_eq_left_of_eq_true _ _ (eq_true hf), upd_apply, eX, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
          exact j2 a ha'
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hf)]; exact j2 a ha')
  obtain ⟨j1, j2, j3, -, -, jr, jrm, jo⟩ := hJ₂
  exact ⟨c₄, k₁ + (k₂ + (k₃ + k₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, j1, j2,
    fun r h => j3 r (by omega), jr, jrm, jo⟩

section Sem

open Orbit CombMap BKMNW PlanarSeparator

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {N : CombMap D V F}

/-- **The scattered flags are those of `K`** (the hypothesis `hKB` of `sdWalk_exec`). -/
theorem bk_flK {Pc K : Finset D} {m k m' : ℕ} {δ : ℕ → D} {α σ : ℕ → ℕ}
    (he : PEnc N Pc m k δ α σ) (hKP : K ⊆ Pc) (cn : SDart (rcl N K) ≃ Fin m')
    {mem : ℕ → ℕ} {Fb Xb : ℕ}
    (hXm : ∀ h < k, ∀ hm : δ h ∈ rcl N K, mem (Xb + h) = cn ⟨δ h, hm⟩)
    (hFm : ∀ x < m, (mem (Fb + x) ≠ 0 ↔ δ x ∈ K)) (x : SDart (rcl N K)) :
    bkV mem Fb Xb m (cn x) = if x.1 ∈ K then 1 else 0 := by
  unfold bkV
  congr 1
  apply propext
  constructor
  · rintro ⟨h, hh, hf, hx⟩
    have hK := (hFm h hh).1 hf
    have hk : h < k := by have := he.mle; omega
    rw [hXm h hk (subset_rcl K hK)] at hx
    have := cn.injective (Fin.ext hx)
    rw [← this]; exact hK
  · intro hK
    obtain ⟨h, hh, hδ⟩ := he.enumP.surj _ (hKP hK)
    have hk : h < k := by have := he.mle; omega
    refine ⟨h, hh, (hFm h hh).2 (by rw [hδ]; exact hK), ?_⟩
    rw [hXm h hk (by rw [hδ]; exact x.2)]
    congr 2
    exact Subtype.ext hδ

/-- The scatter's index bound: `X[h] < m'` for every flagged `h < m`. -/
theorem bk_idx {Pc K : Finset D} {m k m' : ℕ} {δ : ℕ → D} {α σ : ℕ → ℕ}
    (he : PEnc N Pc m k δ α σ) (cn : SDart (rcl N K) ≃ Fin m')
    {mem : ℕ → ℕ} {Fb Xb : ℕ}
    (hXm : ∀ h < k, ∀ hm : δ h ∈ rcl N K, mem (Xb + h) = cn ⟨δ h, hm⟩)
    (hFm : ∀ x < m, (mem (Fb + x) ≠ 0 ↔ δ x ∈ K)) :
    ∀ h < m, mem (Fb + h) ≠ 0 → mem (Xb + h) < m' := fun h hh hf => by
  have hk : h < k := by have := he.mle; omega
  rw [hXm h hk (subset_rcl K ((hFm h hh).1 hf))]; exact (cn _).2

end Sem

end NegSSSP

end PlanarFlow
