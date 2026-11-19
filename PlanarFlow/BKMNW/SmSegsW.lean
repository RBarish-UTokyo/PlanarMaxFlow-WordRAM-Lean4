module

public import PlanarFlow.BKMNW.SmSegsV
public import PlanarFlow.BKMNW.SmSegsD

/-!
# The small separator with the start vertices of its parts: `sepSmS'`; `SepPSpecXS'`

* **`sepSmS' = (3120 := r6500) ; sepSm ; smSegs ; smV`**, room `smRS' n m k = smRS n m k + 3 m`,
  **`sepSmS'_exec`**: the conclusion of `sepSmS_exec` with **`SegsOut'`** for `SegsOut` (the start
  vertex of each part as a frame dart index), within `560 n + 62 m + 61 k + 651` steps;
* **`SepPSpecXS'`**, **`SepPSpecXLS'`**: `SepPSpecXS` / `SepPSpecXLS` with `SegsOut'`;
  `SepPSpecXS'.toXS`, `SepPSpecXLS'.toXLS` (forget the vertices);
* `sepPXS' s sepL = sepD0 s ; if large then sepL else sepSmS'`, **`sepPXS'_spec`**:
  `SepPSpecXLS' … sepL sT sR` ⟹ `SepPSpecXS' … (sepPXS' ds.s sepL)` (steps
  `sT n k + 700 n + 70 k + 800`, room `sR n m k + smRS' n m k`); `sepPXLS'_vacuous`,
  **`sepPXS'_spec_small`**.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable {gid : D → ℕ} {ν : V → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {ds : DSys M}

/-- The small separator writing the parts with their start vertices. -/
def sepSmS' : Stmt := .seq (block [.copyN 3120 6500]) (.seq sepSm (.seq smSegs smV))

/-- The room of `sepSmS'`. -/
def smRS' (n m k : ℕ) : ℕ := smR n m k + 5 * m + 2 * k + 16

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The small separator with its parts and their start vertices** (see the module docstring). -/
theorem sepSmS'_exec {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D}
    {m n d R Sb : ℕ} {en g : ℕ → D} (c : Config) (hc : WordsBounded W c)
    (hok : CallOk M S T ((.node l r π, Hs, σ) : MCall M))
    (hL : Lay M gid u S T Z ((.node l r π, Hs, σ) : MCall M) m en d c.nmem)
    (hpR : c.nmem (d + fsz m) = R) (o2 : d + fsz m < R)
    (hA : RArr M gid ν S T ((.node l r π, Hs, σ) : MCall M) m n R g c.nmem) (hn : c.nmem R = n)
    (hsm : smD M ds.pk S T (l.piece ∪ r.piece) Hs = .node l r π)
    (hpk : PkMin gid ds.pk) (hν : Injective ν) (hloop : ∀ y, M.head y ≠ M.tail y)
    (r4 : c.nreg 3004 = d) (r50 : c.nreg 6500 = Sb) (o1 : R + 3 + 6 * n + m ≤ Sb)
    (w : Sb + smRS' n m Hs.length ≤ W) (hW : 21 ≤ W) :
    ∃ c' t, Exec I W sepSmS' c c' t ∧ t ≤ 560 * n + 62 * m + 61 * Hs.length + 651 ∧
      DRegKeep c c' ∧ (∀ a < Sb, c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧
      c'.output = c.output ∧
      (∀ i < m, c'.nmem (Sb + i) = bf (en i ∈ l.piece)) ∧
      (∀ i < m, c'.nmem (Sb + m + i) = bf (en i ∈ π.path.darts.toFinset)) ∧
      (∀ i < m, c'.nmem (Sb + 2 * m + i) = bf (M.tail (en i) ∈ π.path.mverts)) ∧
      (∀ j < Hs.length, c'.nmem (Sb + 3 * m + j) =
        bf (¬ Disjoint (Hs.getD j ∅) π.path.mverts)) ∧
      c'.nmem (Sb + 3 * m + Hs.length) = ntag l ∧ c'.nmem (Sb + 3 * m + Hs.length + 1) = ntag r ∧
      RecsOut M ds gid ν S T l r π Hs σ (Sb + 21 * m + 4 * Hs.length + 2)
        (Sb + smRS' n m Hs.length) (c'.nreg 6501) c'.nmem ∧
      SegsOut' M en m π (c'.nreg 6501 + 2 + c'.nmem (c'.nreg 6501) +
        c'.nmem (c'.nreg 6501 + 1)) (Sb + smRS' n m Hs.length) (c'.nreg 6502) c'.nmem := by
  have hR : smRS' n m Hs.length = smR n m Hs.length + 5 * m + 2 * Hs.length + 16 := rfl
  have hR' : smR n m Hs.length = 22 * m + 24 * n + 8 * Hs.length + 30 := rfl
  -- the save of `Sb`
  obtain ⟨c₀, t₀, e₀, ht₀, s0, f₀, m₀, rr₀, rm₀, o₀⟩ : ∃ c₀ t₀,
      Exec I W (block [.copyN 3120 6500]) c c₀ t₀ ∧ t₀ = 1 ∧ c₀.nreg 3120 = Sb ∧
      (∀ x, x ≠ 3120 → c₀.nreg x = c.nreg x) ∧ c₀.nmem = c.nmem ∧ c₀.rreg = c.rreg ∧
      c₀.rmem = c.rmem ∧ c₀.output = c.output := by
    exec_block
    refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals
      try config_simp
      try (simp (disch := omega) only [upd_other, upd_same, r50])
  rw [← m₀] at hL hpR hA hn
  -- `sepSm`
  obtain ⟨c₁, t₁, e₁, ht₁, dk1, low1, out1, o1a, o1b, o1c, o1d, o1e, o1f, hRec⟩ :=
    sepSm_exec (I := I) (ds := ds) c₀ e₀.wb_right hok hL hpR o2 hA hn hsm hpk hν hloop
      ((f₀ 3004 (by decide)).trans r4) ((f₀ 6500 (by decide)).trans r50) o1
      (by clear * - w hR; omega) hW
  obtain ⟨hlo, hhi, hrl, hrr⟩ := hRec
  have q1 := (Exec.wr_frame e₁ wrOK_sepSm).1
  have s1 : c₁.nreg 3120 = Sb := by rw [q1 3120 (by decide)]; exact s0
  have hdS : d + 1 ≤ Sb := by unfold fsz at o2; clear * - o2 o1; omega
  have hm1 : c₁.nmem d = m := by rw [(low1 d (by omega)).1]; exact hL.hm
  have hk1 : c₁.nmem (d + 1) = Hs.length := by rw [(low1 (d + 1) (by omega)).1]; exact hL.hk
  -- `smSegs`
  have d1 : c₁.nreg 3004 = d := by
    rw [dk1 3004 (by omega) (by omega), f₀ 3004 (by decide)]; exact r4
  obtain ⟨c₂, t₂, e₂, ht₂, g502, w0, w1, w2, w3, mfr, rfr, rr₂, rm₂, o₂⟩ :=
    smSegs_exec (I := I) c₁ e₁.wb_right rfl d1 s1 rfl rfl hm1 hk1 (by clear * - hlo; omega) hdS
      (by clear * - hhi w hR; omega)
  set Xb := c₁.nreg 6501 with hXb
  set Gb := Xb + 2 + c₁.nmem Xb + c₁.nmem (Xb + 1) with hGb
  have hSeg : Sb + 3 * m + Hs.length + 2 ≤ Xb := by clear * - hlo; omega
  have keep2 : ∀ a, a < Gb → c₂.nmem a = c₁.nmem a := fun a ha =>
    mfr a (by clear * - ha; omega)
  -- `smV`
  have v04 : c₂.nreg 3004 = d := by rw [rfr 3004 (by omega) (by omega) (by omega)]; exact d1
  have v20 : c₂.nreg 3120 = Sb := by rw [rfr 3120 (by omega) (by omega) (by omega)]; exact s1
  have hk0 : c₂.nmem (Gb + 2) ≤ 1 := by rw [w2, sgK_eq]; split_ifs <;> omega
  have hdS' : d + 4 + 6 * m ≤ Sb := by unfold fsz at o2; clear * - o2 o1; omega
  obtain ⟨c₃, t₃, e₃, ht₃, ⟨v, hv1, hv2⟩, mfr3, g502', rfr3, rr₃, rm₃, o₃⟩ :=
    smV_exec (P := I) c₂ e₂.wb_right v04 v20 g502
      ((keep2 d (by clear * - hdS' hSeg; omega)).trans hm1)
      ((keep2 (d + 1) (by clear * - hdS' hSeg; omega)).trans hk1) hk0
      (fun i hi => by rw [keep2 _ (by clear * - hi hSeg; omega), o1c i hi]; exact bf_le_one7 _)
      ⟨by clear * - hdS' hSeg; omega, by clear * - hSeg; omega, by clear * - hhi w hR hR'; omega⟩
  have k6501 : c₃.nreg 6501 = Xb := by
    rw [rfr3 6501 (by omega), rfr 6501 (by decide) (by decide) (by decide)]
  have keep : ∀ a, a < Gb → c₃.nmem a = c₁.nmem a := fun a ha => by
    rw [mfr3 a (by omega) (by omega), keep2 a ha]
  have kX0 : c₃.nmem Xb = c₁.nmem Xb := keep _ (by clear * - hGb; omega)
  have kX1 : c₃.nmem (Xb + 1) = c₁.nmem (Xb + 1) := keep _ (by clear * - hGb; omega)
  refine ⟨c₃, _, .seq e₀ (.seq e₁ (.seq e₂ e₃)), ?_, fun x a1 a2 => ?_, fun a ha => ?_, ?_,
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
  · clear * - ht₀ ht₁ ht₂ ht₃
    omega
  · rw [rfr3 x (by omega), rfr x (by omega) (by omega) (by omega), dk1 x a1 a2, f₀ x (by omega)]
  · refine ⟨?_, ?_⟩
    · rw [keep a (by clear * - ha hSeg; omega), (low1 a ha).1, m₀]
    · rw [rm₃, rm₂, (low1 a ha).2, rm₀]
  · rw [o₃, o₂, out1, o₀]
  · rw [keep _ (by clear * - hi hSeg; omega)]; exact o1a i hi
  · rw [keep _ (by clear * - hi hSeg; omega)]; exact o1b i hi
  · rw [keep _ (by clear * - hi hSeg; omega)]; exact o1c i hi
  · rw [keep _ (by clear * - hj hSeg; omega)]; exact o1d j hj
  · rw [keep _ (by clear * - hSeg; omega)]; exact o1e
  · rw [keep _ (by clear * - hSeg; omega)]; exact o1f
  · rw [k6501]
    have h0 : RecsOut M ds gid ν S T l r π Hs σ (Sb + 21 * m + 4 * Hs.length + 2) Gb Xb
        c₁.nmem := ⟨hlo, le_refl _, hrl, hrr⟩
    exact (h0.congr fun a a1 a2 => keep a a2).mono (by clear * - hhi w hR; omega)
  · rw [k6501, kX0, kX1, g502']
    refine segsOut'_sm hpk (hok.pieceInv.rev) hsm hL.en_mem hL.en_surj hL.en_mono
      (PF := fun i => c₁.nmem (Sb + m + i)) (HF := fun j => c₁.nmem (Sb + 3 * m + j))
      (VF := fun i => c₂.nmem (Sb + 2 * m + i)) (HL := fun i => c₂.nmem (d + 4 + 5 * m + i))
      (mem₀ := c₂.nmem)
      (fun i hi => o1b i hi) (fun j hj => o1d j hj)
      (fun i hi => by rw [keep2 _ (by clear * - hi hSeg; omega)]; exact o1c i hi)
      (fun i hi => by
        rw [keep2 _ (by clear * - hi hdS' hSeg; omega), (low1 _ (by clear * - hi hdS'; omega)).1]
        exact hL.hl i hi)
      (le_refl _) (by clear * - hhi w hR hR'; omega) w0 w1 w2 w3
      (fun a a1 a2 => mfr3 a (by omega) (by omega)) ⟨v, hv1, hv2⟩

end Exec

variable (M) in
/-- **`SepPSpecXS` with the start vertices of the parts** (`SegsOut'`). -/
def SepPSpecXS' (ds : DSys M) (Reach : MCall M → Prop) (gid : D → ℕ) (ν : V → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W : ℕ) (sepP : Stmt) (sT : ℕ → ℕ → ℕ)
    (sR : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (d e h Sb m : ℕ)
    (en : ℕ → D) (c : Config),
    FInLX M ds Reach gid ν u S T Z (.node l r π, Hs, σ) d e c →
    Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem → WordsBounded W c →
    c.nreg 3004 = d → c.nreg 3005 = e → c.nreg 3003 = h → c.nreg 6500 = Sb → e ≤ h → h < Sb →
    Sb + sR (l.piece ∪ r.piece).card m Hs.length ≤ W →
    ∃ c' t, Exec I W sepP c c' t ∧ t ≤ sT (l.piece ∪ r.piece).card Hs.length ∧ DRegKeep c c' ∧
      (∀ a < Sb, c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      (∀ i < m, c'.nmem (Sb + i) = bf (en i ∈ l.piece)) ∧
      (∀ i < m, c'.nmem (Sb + m + i) = bf (en i ∈ π.path.darts.toFinset)) ∧
      (∀ i < m, c'.nmem (Sb + 2 * m + i) = bf (M.tail (en i) ∈ π.path.mverts)) ∧
      (∀ j < Hs.length, c'.nmem (Sb + 3 * m + j) =
        bf (¬ Disjoint (Hs.getD j ∅) π.path.mverts)) ∧
      c'.nmem (Sb + 3 * m + Hs.length) = ntag l ∧ c'.nmem (Sb + 3 * m + Hs.length + 1) = ntag r ∧
      RecsOut M ds gid ν S T l r π Hs σ (Sb + 21 * m + 4 * Hs.length + 2)
        (Sb + sR (l.piece ∪ r.piece).card m Hs.length) (c'.nreg 6501) c'.nmem ∧
      SegsOut' M en m π (c'.nreg 6501 + 2 + c'.nmem (c'.nreg 6501) +
        c'.nmem (c'.nreg 6501 + 1)) (Sb + sR (l.piece ∪ r.piece).card m Hs.length)
        (c'.nreg 6502) c'.nmem

variable (M) in
/-- **`SepPSpecXLS` with the start vertices of the parts** (`SegsOut'`). -/
def SepPSpecXLS' (ds : DSys M) (Reach : MCall M → Prop) (gid : D → ℕ) (ν : V → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W : ℕ) (sepL : Stmt) (sT : ℕ → ℕ → ℕ)
    (sR : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (d e h Sb m : ℕ)
    (en : ℕ → D) (c : Config),
    FInLX M ds Reach gid ν u S T Z (.node l r π, Hs, σ) d e c →
    Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem →
    c.nmem (c.nmem (d + fsz m) + 1) = 0 → ds.s < c.nmem (c.nmem (d + fsz m)) →
    WordsBounded W c →
    c.nreg 3004 = d → c.nreg 3005 = e → c.nreg 3003 = h → c.nreg 6500 = Sb → e ≤ h → h < Sb →
    Sb + sR (l.piece ∪ r.piece).card m Hs.length ≤ W →
    ∃ c' t, Exec I W sepL c c' t ∧ t ≤ sT (l.piece ∪ r.piece).card Hs.length ∧ DRegKeep c c' ∧
      (∀ a < Sb, c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      (∀ i < m, c'.nmem (Sb + i) = bf (en i ∈ l.piece)) ∧
      (∀ i < m, c'.nmem (Sb + m + i) = bf (en i ∈ π.path.darts.toFinset)) ∧
      (∀ i < m, c'.nmem (Sb + 2 * m + i) = bf (M.tail (en i) ∈ π.path.mverts)) ∧
      (∀ j < Hs.length, c'.nmem (Sb + 3 * m + j) =
        bf (¬ Disjoint (Hs.getD j ∅) π.path.mverts)) ∧
      c'.nmem (Sb + 3 * m + Hs.length) = ntag l ∧ c'.nmem (Sb + 3 * m + Hs.length + 1) = ntag r ∧
      RecsOut M ds gid ν S T l r π Hs σ (Sb + 21 * m + 4 * Hs.length + 2)
        (Sb + sR (l.piece ∪ r.piece).card m Hs.length) (c'.nreg 6501) c'.nmem ∧
      SegsOut' M en m π (c'.nreg 6501 + 2 + c'.nmem (c'.nreg 6501) +
        c'.nmem (c'.nreg 6501 + 1)) (Sb + sR (l.piece ∪ r.piece).card m Hs.length)
        (c'.nreg 6502) c'.nmem

/-- **The separator program with the parts of the small separator and their start vertices.** -/
def sepPXS' (s : ℕ) (sepL : Stmt) : Stmt := .seq (sepD0 s) (.ifLtN 5611 5610 sepL sepSmS')

section Forget

variable {Reach : MCall M → Prop} {I : Input} {W : ℕ} {sT : ℕ → ℕ → ℕ} {sR : ℕ → ℕ → ℕ → ℕ}

/-- Forgetting the start vertices. -/
lemma SepPSpecXS'.toXS {sepP : Stmt} (h : SepPSpecXS' M ds Reach gid ν u S T Z I W sepP sT sR) :
    SepPSpecXS M ds Reach gid ν u S T Z I W sepP sT sR := by
  intro l r π Hs σ d e h' Sb m en c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  obtain ⟨c', t, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ :=
    h l r π Hs σ d e h' Sb m en c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  exact ⟨c', t, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13.toSegsOut⟩

/-- Forgetting the start vertices. -/
lemma SepPSpecXLS'.toXLS {sepL : Stmt}
    (h : SepPSpecXLS' M ds Reach gid ν u S T Z I W sepL sT sR) :
    SepPSpecXLS M ds Reach gid ν u S T Z I W sepL sT sR := by
  intro l r π Hs σ d e h' Sb m en c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  obtain ⟨c', t, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ :=
    h l r π Hs σ d e h' Sb m en c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  exact ⟨c', t, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13.toSegsOut⟩

end Forget

section Exec2

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **`sepPXS` meets `SepPSpecXS'`** (see the module docstring). -/
theorem sepPXS'_spec {Reach : MCall M → Prop} {sepL : Stmt} {sT : ℕ → ℕ → ℕ}
    {sR : ℕ → ℕ → ℕ → ℕ} (hsL : SepPSpecXLS' M ds Reach gid ν u S T Z I W sepL sT sR)
    (hpk : PkMin gid ds.pk) (hν : Injective ν) (hloop : ∀ y, M.head y ≠ M.tail y)
    (hsW : ds.s ≤ W) :
    SepPSpecXS' M ds Reach gid ν u S T Z I W (sepPXS' ds.s sepL)
      (fun n k => sT n k + 700 * n + 70 * k + 800) (fun n m k => sR n m k + smRS' n m k) := by
  intro l r π Hs σ d e h Sb m en c hin hLy hc r4 r5 r3 r50 heh hhS hw
  obtain ⟨hR, hok, m', en', n, g, hL', hp1, hsz, hLR⟩ := id hin
  have hmm : m' = m := hL'.card.trans hLy.card.symm
  subst hmm
  have hf : fsz m' = 4 + 7 * m' := rfl
  have hsm0 : smRS' (l.piece ∪ r.piece).card m' Hs.length =
      22 * m' + 24 * (l.piece ∪ r.piece).card + 8 * Hs.length + 30 + 5 * m' + 2 * Hs.length + 16 :=
    rfl
  have hw' : Sb + (sR (l.piece ∪ r.piece).card m' Hs.length +
      smRS' (l.piece ∪ r.piece).card m' Hs.length) ≤ W := hw
  obtain ⟨R, hRdef⟩ : ∃ R, c.nmem (d + fsz m') = R := ⟨_, rfl⟩
  rw [hRdef] at hp1 hsz hLR
  have hph2 := hLR.hph
  have hRn : c.nmem R = n := hLR.hn
  -- the phase is not that of a leaf
  have hph : c.nmem (R + 1) < 2 := by
    rcases hLR.ph with ⟨h0, -⟩ | ⟨h1, -⟩ | ⟨-, Q, hQ⟩
    · omega
    · omega
    · cases hQ
  have hA := hLR.arr hph
  have hnc : n = (l.piece ∪ r.piece).card := hA.card
  have hmn : m' ≤ n := by
    rw [hLy.card, hnc]; exact card_le_card (pdarts_subset _ _)
  have hsz' : R + (3 + 6 * n + m') ≤ e := by
    have : rszL (c.nmem (R + 1)) n m' = 3 + 6 * n + m' := by unfold rszL; rw [iteT hph]
    rw [← this]; exact hsz
  have o1 : R + 3 + 6 * n + m' ≤ Sb := by clear * - hsz' heh hhS; omega
  have hW1 : Sb + smRS' n m' Hs.length ≤ W := by rw [hnc]; clear * - hw'; omega
  have hSb : Sb ≤ W := by clear * - hW1; unfold smRS' smR at hW1; omega
  obtain ⟨c₁, t₁, e₁, ht₁, v10, v11, n1, m1, rr1, rm1, o1'⟩ := sepD0_exec (I := I) (s := ds.s) c hc
    r4 hLy.hm (by rw [show d + 7 * m' + 4 = d + fsz m' by omega]; exact hRdef) hRn rfl hph2
    (by clear * - hp1 o1 hSb hf; omega) (by clear * - o1 hSb; omega) hsW
    (by clear * - hW1; unfold smRS' smR at hW1; omega)
  have hin1 : FInLX M ds Reach gid ν u S T Z (.node l r π, Hs, σ) d e c₁ :=
    hin.stab (memEq_of_eq m1 rm1 d e)
  have hLy1 : Lay M gid u S T Z (.node l r π, Hs, σ) m' en d c₁.nmem := by rw [m1]; exact hLy
  have R1 : ∀ x, x < 5600 → c₁.nreg x = c.nreg x := fun x hx => n1 x (Or.inl hx)
  by_cases hp : c₁.nreg 5611 < c₁.nreg 5610
  · -- a large piece
    rw [v10, v11] at hp
    have hb1 : 0 < (c.nmem (R + 1) - 1) + (1 - c.nmem (R + 1)) := by
      rcases Nat.eq_zero_or_pos ((c.nmem (R + 1) - 1) + (1 - c.nmem (R + 1))) with h0 | h0
      · rw [h0] at hp; simp at hp
      · exact h0
    have hb2 : 0 < n - ds.s := by
      rcases Nat.eq_zero_or_pos (n - ds.s) with h0 | h0
      · rw [h0] at hp; simp at hp
      · exact h0
    have hph0 : c₁.nmem (c₁.nmem (d + fsz m') + 1) = 0 := by
      rw [m1, hRdef]; clear * - hb1 hph; omega
    have hlarge : ds.s < c₁.nmem (c₁.nmem (d + fsz m')) := by
      rw [m1, hRdef, hRn]; omega
    obtain ⟨c₂, t₂, e₂, ht₂, dk2, mk2, oo2, s1, s2, s3, s4, s5, s6, hRO, hSO⟩ := hsL l r π Hs σ d e h Sb
      m' en c₁ hin1 hLy1 hph0 hlarge e₁.wb_right ((R1 3004 (by decide)).trans r4)
      ((R1 3005 (by decide)).trans r5) ((R1 3003 (by decide)).trans r3)
      ((n1 6500 (Or.inr (by decide))).trans r50) heh hhS (by clear * - hw'; omega)
    refine ⟨c₂, _, .seq e₁ (.ifLtN_true (by rw [v10, v11]; exact hp) e₂), ?_,
      fun x h1 h2 => ?_, fun a ha => ?_, by rw [oo2, o1'], s1, s2,
      s3, s4, s5, s6, hRO.mono ?_, hSO.mono ?_⟩
    · show t₁ + (t₂ + 1) ≤ sT (l.piece ∪ r.piece).card Hs.length + 700 * (l.piece ∪ r.piece).card +
        70 * Hs.length + 800
      clear * - ht₁ ht₂; omega
    · rw [dk2 x h1 h2]; exact R1 x (by clear * - h2; omega)
    · rw [(mk2 a ha).1, (mk2 a ha).2, m1, rm1]; exact ⟨rfl, rfl⟩
    · show _ ≤ Sb + (sR (l.piece ∪ r.piece).card m' Hs.length +
        smRS' (l.piece ∪ r.piece).card m' Hs.length)
      clear * -; omega
    · show _ ≤ Sb + (sR (l.piece ∪ r.piece).card m' Hs.length +
        smRS' (l.piece ∪ r.piece).card m' Hs.length)
      clear * -; omega
  · -- the small decomposition
    rw [v10, v11] at hp
    have hsm : smD M ds.pk S T (l.piece ∪ r.piece) Hs = .node l r π := by
      rcases hLR.ph with ⟨h0, st, hx⟩ | ⟨h1, hx⟩ | ⟨-, Q, hQ⟩
      · have hns : n ≤ ds.s := by
          rw [h0] at hp; clear * - hp; simp at hp; omega
        have hx' : ADec.node l r π = decS M ds.spS ds.spH (smD M ds.pk S T) ds.chS ds.s
            (l.piece ∪ r.piece) Hs st (decide (c.nmem (R + 2) = 1)) := hx.1
        rw [decS_small (show (l.piece ∪ r.piece).card ≤ ds.s by rw [← hnc]; exact hns)] at hx'
        exact hx'.symm
      · exact hx.symm
      · cases hQ
    obtain ⟨c₂, t₂, e₂, ht₂, dk2, mk2, oo2, s1, s2, s3, s4, s5, s6, hRO, hSO⟩ := sepSmS'_exec
      (I := I) (ds := ds) c₁ e₁.wb_right hok hLy1 (by rw [m1]; exact hRdef) hp1
      (hA.congr fun a _ _ => by rw [m1]) (by rw [m1]; exact hRn) hsm hpk hν hloop
      ((R1 3004 (by decide)).trans r4) ((n1 6500 (Or.inr (by decide))).trans r50) o1 hW1
      (by clear * - hW1; unfold smRS' smR at hW1; omega)
    refine ⟨c₂, _, .seq e₁ (.ifLtN_false (by rw [v10, v11]; exact hp) e₂), ?_,
      fun x h1 h2 => ?_, fun a ha => ?_, by rw [oo2, o1'], s1, s2, s3, s4, s5, s6,
      hRO.mono ?_, hSO.mono ?_⟩
    · show t₁ + (t₂ + 2) ≤ sT (l.piece ∪ r.piece).card Hs.length + 700 * (l.piece ∪ r.piece).card +
        70 * Hs.length + 800
      rw [← hnc]; clear * - ht₁ ht₂ hmn; omega
    · rw [dk2 x h1 h2]; exact R1 x (by clear * - h2; omega)
    · rw [(mk2 a ha).1, (mk2 a ha).2, m1, rm1]; exact ⟨rfl, rfl⟩
    · show _ ≤ Sb + (sR (l.piece ∪ r.piece).card m' Hs.length +
        smRS' (l.piece ∪ r.piece).card m' Hs.length)
      rw [← hnc]; clear * -; omega
    · show _ ≤ Sb + (sR (l.piece ∪ r.piece).card m' Hs.length +
        smRS' (l.piece ∪ r.piece).card m' Hs.length)
      rw [← hnc]; clear * -; omega

/-- **`SepPSpecXLS'` holds vacuously when every call of `Reach` has at most `ds.s` darts.** -/
theorem sepPXLS'_vacuous {Reach : MCall M → Prop} (hsmall : ∀ x, Reach x → x.1.piece.card ≤ ds.s)
    (sepL : Stmt) (sT : ℕ → ℕ → ℕ) (sR : ℕ → ℕ → ℕ → ℕ) :
    SepPSpecXLS' M ds Reach gid ν u S T Z I W sepL sT sR := by
  intro l r π Hs σ d e h Sb m en c hin hLy hph0 hlarge
  exfalso
  obtain ⟨hR, -, m', en', n, g, hL', -, -, hLR⟩ := hin
  have hmm : m' = m := hL'.card.trans hLy.card.symm
  subst hmm
  have hA := hLR.arr (by rw [hph0]; omega)
  have hnc := hA.card
  have := hsmall _ hR
  rw [hLR.hn] at hlarge
  omega

/-- **The separator program meets `SepPSpecXS'` when every piece is small** (at most `ds.s` darts:
then every node call is a node of `smD`). -/
theorem sepPXS'_spec_small {Reach : MCall M → Prop}
    (hsmall : ∀ x, Reach x → x.1.piece.card ≤ ds.s)
    (hpk : PkMin gid ds.pk) (hν : Injective ν) (hloop : ∀ y, M.head y ≠ M.tail y)
    (hsW : ds.s ≤ W) :
    SepPSpecXS' M ds Reach gid ν u S T Z I W (sepPXS' ds.s .skip)
      (fun n k => 0 + 700 * n + 70 * k + 800) (fun n m k => 0 + smRS' n m k) :=
  sepPXS'_spec (sepPXLS'_vacuous hsmall .skip (fun _ _ => 0) (fun _ _ _ => 0)) hpk hν hloop hsW

end Exec2


end MfDrv

end BKMNW

end PlanarFlow
