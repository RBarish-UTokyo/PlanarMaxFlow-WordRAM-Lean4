module

public import PlanarFlow.Machine.Tree

/-!
# Feasibility on the machine: Bellman–Ford over the dual graph

The dual graph has the faces as vertices and an arc from `fc i` to `fc (rv i)` of length
`cp i - g i` for every dart `i`, where `g` is the base flow (`PlanarFlow.Feas.dual`). The values
start at `0` on every face; each of the `F` rounds relaxes every dart in turn. The values stay
above `-(number of relaxations) · B`, which the offset `Z` accommodates. If the dual has a
feasible potential, the in-place values after `t` rounds lie between the Bellman–Ford values
`bf F` and `bf t` (`PlanarFlow.Digraph.isPot_bf_card`, `PlanarFlow.Digraph.le_bf_succ_of_round`),
so after `F` rounds they are `bf F`, a feasible potential (`rounds_exec`). The check pass then
clears `r32` exactly when some dart violates the potential inequality (`check_exec`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Feas

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

variable {d : List ℕ} {W : ℕ}

/-- The dual graph with lengths `cp - g`, for the base flow stored in `m`. -/
def dual (he : Enc d W) (m : ℕ → ℕ) : Digraph (Fin (nf d)) (Fin (nd d)) where
  src j := ⟨fc d j, he.wf.fc_lt j j.2⟩
  dst j := ⟨fc d (rv d j), he.wf.fc_lt _ (he.wf.rv_lt j j.2)⟩
  len j := (cp d j : ℤ) - sv d m j

/-- The values of the faces, as a function on the faces. -/
def evf (d : List ℕ) (m : ℕ → ℕ) (f : Fin (nf d)) : ℤ := ev d m f

/-- The candidate block. -/
theorem cand_exec (he : Enc d W) (c : Config) (hc : WordsBounded W c) (hR : Regs d c)
    (hlt : c.nreg 20 < nd d) (hub : ∀ f < nf d, c.nmem ((nd d + 4 * nv d + f)) ≤ zz d) :
    ∃ c' k, Exec (inp d) W cand c c' k ∧ WordsBounded W c' ∧ Keeps c c' ∧
      c'.nmem = c.nmem ∧ c'.output = c.output ∧ c'.nreg 20 = c.nreg 20 ∧
      c'.nreg 26 = c.nreg 26 ∧ (∀ r, 32 ≤ r → c'.nreg r = c.nreg r) ∧
      c'.nreg 30 = c.nmem ((nd d + 4 * nv d + (fc d (c.nreg 20)))) + cp d (c.nreg 20) + zz d - c.nmem (c.nreg 20) ∧
      c'.nreg 31 = c.nmem ((nd d + 4 * nv d + (fc d (rv d (c.nreg 20))))) ∧
      c'.nreg 22 = (nd d + 4 * nv d + (fc d (rv d (c.nreg 20)))) ∧ k = 21 := by
  have hs := he.size
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, h12, h13⟩, h6⟩ := hR
  have hrv := he.wf.rv_lt _ hlt
  have hf1 := he.wf.fc_lt _ hlt
  have hf2 := he.wf.fc_lt _ hrv
  have hcap := he.cap_le _ hlt
  have hu1 : c.nmem (nd d + 4 * nv d + fc d (c.nreg 20)) ≤ zz d := hub _ hf1
  have e1 : word d (c.nreg 20 * 5 + 3 + 1) = rv d (c.nreg 20) := rfl
  have e2 : word d (c.nreg 20 * 5 + 3 + 1 + 1) = fc d (c.nreg 20) := rfl
  have e3 : word d (c.nreg 20 * 5 + 3 + 1 + 1 + 2) = cp d (c.nreg 20) := rfl
  have e4 : word d (rv d (c.nreg 20) * 5 + 3 + 1 + 1) = fc d (rv d (c.nreg 20)) := rfl
  have hK : ∀ c' : Config, (∀ r, r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 27 → r ≠ 28 → r ≠ 30 →
      r ≠ 31 → c'.nreg r = c.nreg r) → Keeps c c' := fun c' h r hr =>
    h r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  unfold cand
  exec_block
  · config_simp; rw [h5]; omega
  · config_simp; rw [h5, h13]; omega
  · config_simp; rw [h5, h13, h1]; omega
  · config_simp; exact he.word_le _
  · config_simp; rw [h5, h13, h1]; omega
  · config_simp; exact he.word_le _
  · config_simp; rw [h5, h13, h1, h12]; omega
  · config_simp; exact he.word_le _
  · config_simp; simp only [h5, h13, h1, word_inp]; rw [e1]; omega
  · config_simp; simp only [h5, h13, h1, word_inp]; rw [e1]; omega
  · config_simp; simp only [h5, h13, h1, word_inp]; rw [e1]; omega
  · config_simp; simp only [h5, h13, h1, word_inp]; rw [e1]; omega
  · config_simp; exact he.word_le _
  · config_simp; simp only [h5, h13, h1, h10, word_inp]; rw [e2]; omega
  · config_simp; simp only [h5, h13, h1, h12, h10, word_inp]; rw [e2, e3]; omega
  · config_simp; simp only [h5, h13, h1, h12, h10, h6, word_inp]; rw [e2, e3]; omega
  · config_simp; simp only [h5, h13, h1, h10, word_inp]; rw [e1, e4]; omega
  refine ⟨‹_›, hK _ fun r a b e f g l m => ?_, by config_simp, by config_simp, by config_simp,
    by config_simp, fun r hr => ?_, ?_, ?_, ?_, rfl⟩
  · config_simp; simp only [upd_apply, a, b, e, f, g, l, m, ite_false]
  · config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega
  · config_simp; simp only [h5, h13, h1, h12, h10, h6, word_inp]; rw [e2, e3]
  · config_simp; simp only [h5, h13, h1, h10, word_inp]; rw [e1, e4]
  · config_simp; simp only [h5, h13, h1, h10, word_inp]; rw [e1, e4]


/-- The dual graph has a feasible potential. -/
def HasPot (he : Enc d W) (m : ℕ → ℕ) : Prop := ∃ p, (dual he m).IsPot p

lemma card_fin_nf : Fintype.card (Fin (nf d)) = nf d := Fintype.card_fin _

/-- The bound used to keep the stored candidates nonnegative. -/
lemma mul_bsum_le {t : ℕ} (ht : t ≤ nf d * nd d) : t * bsum d ≤ zz d := by
  unfold zz
  calc t * bsum d ≤ (nf d * nd d + 1) * (bsum d + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
    _ = _ := rfl

/-- The state of a round of relaxations: round `k`, the base flow stored in `m₂`, `ok` the
result of the root check. -/
structure JB (he : Enc d W) (m₂ : ℕ → ℕ) (ok k : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : Regs d c
  out : c.output = []
  r26 : c.nreg 26 = k
  k_lt : k < nf d
  r20 : c.nreg 20 ≤ nd d
  r32 : c.nreg 32 = ok
  frame : ∀ a < nd d + 4 * nv d, c.nmem a = m₂ a
  ub : ∀ f < nf d, c.nmem ((nd d + 4 * nv d + f)) ≤ zz d
  lb : ∀ f < nf d, -(((k * nd d + c.nreg 20) * bsum d : ℕ) : ℤ) ≤ ev d c.nmem f
  bf : HasPot he m₂ → (∀ f, (dual he m₂).bf (nf d) f ≤ evf d c.nmem f ∧
      evf d c.nmem f ≤ (dual he m₂).bf k f) ∧
    ∀ j : Fin (nd d), (j : ℕ) < c.nreg 20 →
      evf d c.nmem ((dual he m₂).dst j) ≤ (dual he m₂).bf k ((dual he m₂).src j) + (dual he m₂).len j

/-- One relaxation, on the memory. -/
theorem JB.relax (he : Enc d W) {m₂ : ℕ → ℕ} (hg : ∀ j < nd d, |sv d m₂ j| ≤ bsum d)
    {ok k : ℕ} {c c' : Config} (hJ : JB he m₂ ok k c) (hlt : c.nreg 20 < nd d)
    (hw : WordsBounded W c') (hR : Regs d c') (hout : c'.output = c.output)
    (h26 : c'.nreg 26 = c.nreg 26) (h20 : c'.nreg 20 = c.nreg 20 + 1) (h32 : c'.nreg 32 = c.nreg 32)
    (hmem : c'.nmem = if c.nmem ((nd d + 4 * nv d + (fc d (c.nreg 20)))) + cp d (c.nreg 20) + zz d -
        c.nmem (c.nreg 20) < c.nmem ((nd d + 4 * nv d + (fc d (rv d (c.nreg 20))))) then
      upd c.nmem ((nd d + 4 * nv d + (fc d (rv d (c.nreg 20))))) (c.nmem ((nd d + 4 * nv d + (fc d (c.nreg 20)))) +
        cp d (c.nreg 20) + zz d - c.nmem (c.nreg 20)) else c.nmem) :
    JB he m₂ ok k c' := by
  have hk := hJ.k_lt
  generalize hi : c.nreg 20 = i at hlt hmem h20
  have hJ20 := hJ.r20
  have hlb := hJ.lb
  rw [hi] at hlb
  generalize hs : fc d i = s at hmem
  generalize ht : fc d (rv d i) = t at hmem
  have hsn : s < nf d := hs ▸ he.wf.fc_lt i hlt
  have htn : t < nf d := ht ▸ he.wf.fc_lt _ (he.wf.rv_lt i hlt)
  have hgi : c.nmem i = m₂ i := hJ.frame i (by omega)
  have hgb := abs_le.1 (hg i hlt)
  have hgv : (m₂ i : ℤ) = sv d m₂ i + zz d := by unfold sv; ring
  have hev : ∀ f, (c.nmem ((nd d + 4 * nv d + f)) : ℤ) = ev d c.nmem f + zz d := by intro f; unfold ev sv; ring
  -- the bound keeping the candidate nonnegative
  have hT : (k * nd d + i + 1) * bsum d ≤ zz d := mul_bsum_le (by nlinarith)
  have hT' : (((k * nd d + i + 1) * bsum d : ℕ) : ℤ) = ((k * nd d + i) * bsum d : ℕ) + bsum d := by
    push_cast; ring
  have hTz : (((k * nd d + i + 1) * bsum d : ℕ) : ℤ) ≤ zz d := by exact_mod_cast hT
  have hls := hlb s hsn
  -- the candidate
  have hC : c.nmem (c.nreg 20) ≤ c.nmem ((nd d + 4 * nv d + s)) + cp d i + zz d := by
    rw [hi, hgi]
    have := hev s
    omega
  generalize hCdef : c.nmem ((nd d + 4 * nv d + s)) + cp d i + zz d - c.nmem i = C at hmem
  have hCv : (C : ℤ) - zz d = ev d c.nmem s + (dual he m₂).len ⟨i, hlt⟩ := by
    rw [← hCdef, Nat.cast_sub (by rw [hi] at hC; exact hC)]
    push_cast
    rw [hev s, hgi, hgv]
    simp only [dual]; ring
  have hlen : -(bsum d : ℤ) ≤ (dual he m₂).len ⟨i, hlt⟩ := by
    simp only [dual]; have := Int.natCast_nonneg (cp d i); linarith
  have hsrc : ((dual he m₂).src ⟨i, hlt⟩ : ℕ) = s := hs
  have hdst : ((dual he m₂).dst ⟨i, hlt⟩ : ℕ) = t := ht
  -- the new values
  have hupd : ∀ f, ev d (upd c.nmem (nd d + 4 * nv d + t) C) f =
      if f = t then (C : ℤ) - zz d else ev d c.nmem f := by
    intro f
    by_cases h : f = t
    · rw [h]; simp [ev, sv]
    · simp only [ev, sv, h, ite_false]
      rw [upd_other _ _ _ (by omega)]
  have hnew : ∀ f, ev d c'.nmem f = if C < c.nmem (nd d + 4 * nv d + t) ∧ f = t then
      ev d c.nmem s + (dual he m₂).len ⟨i, hlt⟩ else ev d c.nmem f := by
    intro f
    rw [hmem]
    by_cases h1 : C < c.nmem (nd d + 4 * nv d + t)
    · simp only [h1, ite_true, true_and, hupd]
      split_ifs
      · exact hCv
      · rfl
    · simp only [h1, ite_false, false_and]
  have hle : ∀ f, ev d c'.nmem f ≤ ev d c.nmem f := by
    intro f; rw [hnew]; split_ifs with h
    · obtain ⟨h1, rfl⟩ := h; have := hev f; have : (C : ℤ) < c.nmem ((nd d + 4 * nv d + f)) := by exact_mod_cast h1
      linarith [hCv]
    · exact le_rfl
  refine ⟨hw, hR, hout.trans hJ.out, h26.trans hJ.r26, hk, by omega, h32.trans hJ.r32,
    fun a ha => ?_, fun f hf => ?_, fun f hf => ?_, fun hP => ?_⟩
  · rw [hmem]; split_ifs
    · rw [upd_other _ _ _ (by omega)]; exact hJ.frame a ha
    · exact hJ.frame a ha
  · rw [hmem]; split_ifs with h1
    · rw [upd_apply]; split_ifs with h2
      · have := hJ.ub t htn; omega
      · exact hJ.ub f hf
    · exact hJ.ub f hf
  · rw [h20, show k * nd d + (i + 1) = k * nd d + i + 1 by ring, hT']
    rw [hnew]; split_ifs
    · linarith
    · have := hlb f hf; linarith [Int.natCast_nonneg (bsum d)]
  · obtain ⟨hJ1, hJ2⟩ := hJ.bf hP
    obtain ⟨p, hp⟩ := hP
    have hpot := (dual he m₂).isPot_bf_card hp
    rw [card_fin_nf] at hpot
    refine ⟨fun f => ⟨?_, (hle f).trans (hJ1 f).2⟩, fun j hj => ?_⟩
    · unfold evf; rw [hnew]; split_ifs with h
      · obtain ⟨-, hft⟩ := h
        have h1 := hpot ⟨i, hlt⟩
        have h2 := (hJ1 ((dual he m₂).src ⟨i, hlt⟩)).1
        have hf : f = (dual he m₂).dst ⟨i, hlt⟩ := Fin.ext (by rw [hdst]; exact hft)
        rw [hf]; unfold evf at h2; rw [hsrc] at h2; linarith
      · exact (hJ1 f).1
    · rw [h20] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact (hle _).trans (hJ2 j (by rw [hi]; exact hj))
      · have hji : j = ⟨i, hlt⟩ := Fin.ext hj
        subst hji
        unfold evf
        rw [hdst, hnew]
        have h2 := (hJ1 ((dual he m₂).src ⟨i, hlt⟩)).2
        unfold evf at h2; rw [hsrc] at h2
        split_ifs with h
        · linarith
        · have h3 : ¬ (C : ℤ) < c.nmem ((nd d + 4 * nv d + t)) := fun h' => h ⟨by exact_mod_cast h', rfl⟩
          have := hev t
          linarith [hCv]

theorem relaxStep_exec (he : Enc d W) {m₂ : ℕ → ℕ} (hg : ∀ j < nd d, |sv d m₂ j| ≤ bsum d)
    {ok k : ℕ} (c : Config) (hJ : JB he m₂ ok k c) (hlt : c.nreg 20 < c.nreg 4) :
    ∃ c' k', Exec (inp d) W relaxStep c c' k' ∧ JB he m₂ ok k c' ∧
      (nd d - c'.nreg 20) * 26 + k' + 2 ≤ (nd d - c.nreg 20) * 26 := by
  have hc := hJ.wb
  have hs := he.size
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, h12, h13⟩, h6⟩ := hJ.regs
  rw [h4] at hlt
  unfold relaxStep
  refine spec_seq ?_
  obtain ⟨c₁, k₁, e₁, hw₁, hK₁, hm₁, ho₁, h20₁, h26₁, h32₁, h30₁, h31₁, h22₁, rfl⟩ :=
    cand_exec he c hc hJ.regs hlt hJ.ub
  refine ⟨c₁, 21, e₁, ?_⟩
  have hR₁ := regs_of hJ.regs hK₁
  have h1' := hR₁.1.2.1
  refine spec_seq ?_
  by_cases hcmp : c₁.nreg 30 < c₁.nreg 31
  · refine spec_ifLtN_true hcmp ?_
    refine spec_instr (Exec.storeN hw₁ _ _) fun hw₂ => ?_
    refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h20₁, h1']; omega)) fun hw₃ => ?_
    refine ⟨JB.relax he hg hJ hlt hw₃ (regs_of hR₁ fun r hr => by
        config_simp; rw [upd_other _ _ _ (by omega)]) (by config_simp; exact ho₁)
      (by config_simp; exact h26₁) ?_ ?_ ?_, ?_⟩
    · config_simp; rw [h20₁, h1']
    · config_simp; exact h32₁ 32 le_rfl
    · config_simp
      rw [h30₁, h31₁] at hcmp
      rw [ite_eq_left_of_eq_true _ _ (eq_true hcmp), h22₁, h30₁, hm₁]
    · config_simp; rw [h20₁, h1']; omega
  · refine spec_ifLtN_false hcmp ?_
    refine spec_skip hw₁ ?_
    refine spec_instr (Exec.addN hw₁ _ _ _ (by rw [h20₁, h1']; omega)) fun hw₃ => ?_
    refine ⟨JB.relax he hg hJ hlt hw₃ (regs_of hR₁ fun r hr => by
        config_simp; rw [upd_other _ _ _ (by omega)]) (by config_simp; exact ho₁) ?_ ?_ ?_ ?_, ?_⟩
    · config_simp; exact h26₁
    · config_simp; rw [h20₁, h1']
    · config_simp; exact h32₁ 32 le_rfl
    · config_simp
      rw [h30₁, h31₁] at hcmp
      rw [ite_eq_right_of_eq_false _ _ (eq_false hcmp), hm₁]
    · config_simp; rw [h20₁, h1']; omega

/-- The state between rounds. -/
structure IB (he : Enc d W) (m₂ : ℕ → ℕ) (ok : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : Regs d c
  out : c.output = []
  r26 : c.nreg 26 ≤ nf d
  r32 : c.nreg 32 = ok
  frame : ∀ a < nd d + 4 * nv d, c.nmem a = m₂ a
  ub : ∀ f < nf d, c.nmem (nd d + 4 * nv d + f) ≤ zz d
  lb : ∀ f < nf d, -((c.nreg 26 * nd d * bsum d : ℕ) : ℤ) ≤ ev d c.nmem f
  bf : HasPot he m₂ → ∀ f, (dual he m₂).bf (nf d) f ≤ evf d c.nmem f ∧
    evf d c.nmem f ≤ (dual he m₂).bf (c.nreg 26) f

theorem round_exec (he : Enc d W) {m₂ : ℕ → ℕ} (hg : ∀ j < nd d, |sv d m₂ j| ≤ bsum d)
    {ok : ℕ} (c : Config) (hI : IB he m₂ ok c) (hlt : c.nreg 26 < c.nreg 3) :
    ∃ c' k, Exec (inp d) W round c c' k ∧ IB he m₂ ok c' ∧
      (nf d - c'.nreg 26) * (26 * nd d + 6) + k + 2 ≤ (nf d - c.nreg 26) * (26 * nd d + 6) := by
  have hc := hI.wb
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, h12, h13⟩, h6⟩ := hI.regs
  rw [h3] at hlt
  have e₁ := Exec.copyN (P := inp d) hc 20 0
  have hJ : JB he m₂ ok (c.nreg 26) { c with nreg := upd c.nreg 20 (c.nreg 0) } := by
    refine ⟨e₁.wb_right, regs_of hI.regs fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)],
      hI.out, by config_simp, hlt, by config_simp; omega, by config_simp; exact hI.r32,
      hI.frame, hI.ub, fun f hf => ?_, fun hP => ⟨hI.bf hP, fun j hj => ?_⟩⟩
    · config_simp; rw [h0, Nat.add_zero]; exact hI.lb f hf
    · config_simp at hj; omega
  obtain ⟨c₂, k₂, e₂, hJ₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 20)
    (b := 4) (body := relaxStep) (JB he m₂ ok (c.nreg 26)) (fun c => (nd d - c.nreg 20) * 26)
    (fun c h => h.wb) (fun c hc hlt => relaxStep_exec he hg c hc hlt) hJ
  have h4₂ := hJ₂.regs.1.2.2.2.2.1
  have h20 : c₂.nreg 20 = nd d := by have := hJ₂.r20; rw [h4₂] at hn₂; omega
  have hw₂ := hJ₂.wb
  have e₃ := Exec.addN (P := inp d) hw₂ 26 26 1 (by
    rw [hJ₂.r26, hJ₂.regs.1.2.1]; have := hI.r26; have := he.size; omega)
  refine ⟨_, _, .seq e₁ (.seq e₂ e₃), ⟨e₃.wb_right, regs_of hJ₂.regs fun r hr => by
    config_simp; rw [upd_other _ _ _ (by omega)], by config_simp; exact hJ₂.out,
    by config_simp; rw [hJ₂.r26, hJ₂.regs.1.2.1]; omega, by config_simp; exact hJ₂.r32,
    hJ₂.frame, hJ₂.ub, fun f hf => ?_, fun hP f => ?_⟩, ?_⟩
  · config_simp; rw [hJ₂.r26, hJ₂.regs.1.2.1]
    have := hJ₂.lb f hf
    rw [h20] at this
    have e : (c.nreg 26 + 1) * nd d * bsum d = (c.nreg 26 * nd d + nd d) * bsum d := by ring
    rw [e]; exact this
  · obtain ⟨hb1, hb2⟩ := hJ₂.bf hP
    refine ⟨(hb1 f).1, ?_⟩
    config_simp; rw [hJ₂.r26, hJ₂.regs.1.2.1]
    exact (dual he m₂).le_bf_succ_of_round (fun f => (hb1 f).2)
      (fun j => hb2 j (by rw [h20]; exact j.2)) f
  · beta_reduce at hk₂
    config_simp
    rw [hJ₂.r26, hJ₂.regs.1.2.1]
    simp only [upd_same] at hk₂
    rw [h0] at hk₂
    have : (nf d - c.nreg 26) * (26 * nd d + 6) = (nf d - (c.nreg 26 + 1)) * (26 * nd d + 6) +
        (26 * nd d + 6) := by
      rw [← Nat.succ_mul]; congr 1; omega
    rw [this]
    omega

/-- The state of the initialization of the values. -/
structure IE (d : List ℕ) (W : ℕ) (m₂ : ℕ → ℕ) (ok : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : Regs d c
  out : c.output = []
  r20 : c.nreg 20 ≤ nf d
  r32 : c.nreg 32 = ok
  done : ∀ f < c.nreg 20, c.nmem (nd d + 4 * nv d + f) = zz d
  frame : ∀ a < nd d + 4 * nv d, c.nmem a = m₂ a

theorem eStep_exec (he : Enc d W) {m₂ : ℕ → ℕ} {ok : ℕ} (c : Config) (hI : IE d W m₂ ok c)
    (hlt : c.nreg 20 < c.nreg 3) :
    ∃ c' k, Exec (inp d) W eStep c c' k ∧ IE d W m₂ ok c' ∧
      (nf d - c'.nreg 20) * 5 + k + 2 ≤ (nf d - c.nreg 20) * 5 := by
  have hc := hI.wb
  have hs := he.size
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, h12, h13⟩, h6⟩ := hI.regs
  rw [h3] at hlt
  unfold eStep
  exec_block
  · config_simp; rw [h10]; omega
  · config_simp; rw [h1]; omega
  refine ⟨⟨‹_›, regs_of hI.regs fun r hr => by
      config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega,
    by config_simp; exact hI.out, by config_simp; rw [h1]; omega, by config_simp; exact hI.r32,
    fun f hf => ?_, fun a ha => ?_⟩, by config_simp; rw [h1]; omega⟩
  · config_simp at hf; rw [h1] at hf; config_simp
    rw [upd_apply, h10]; split_ifs with h
    · exact h6
    · exact hI.done f (by omega)
  · config_simp; rw [upd_other _ _ _ (by rw [h10]; omega)]; exact hI.frame a ha

/-- The initialization of the values and the `F` rounds. -/
theorem rounds_exec (he : Enc d W) {m₂ : ℕ → ℕ} (hg : ∀ j < nd d, |sv d m₂ j| ≤ bsum d)
    (c : Config) (hc : WordsBounded W c) (hR : Regs d c) (ho : c.output = [])
    (hm : c.nmem = m₂) (h20 : c.nreg 20 = 0) :
    ∃ c₁ k₁ c₂ c' k₂, Exec (inp d) W (.whileLtN 20 3 eStep) c c₁ k₁ ∧
      Exec (inp d) W (.instr (.copyN 26 0)) c₁ c₂ 1 ∧
      Exec (inp d) W (.whileLtN 26 3 round) c₂ c' k₂ ∧
      WordsBounded W c' ∧ Regs d c' ∧ c'.output = [] ∧ c'.nreg 32 = c.nreg 32 ∧
      (∀ a < nd d + 4 * nv d, c'.nmem a = m₂ a) ∧
      (∀ f < nf d, c'.nmem (nd d + 4 * nv d + f) ≤ zz d) ∧
      (∀ f < nf d, -((nf d * nd d * bsum d : ℕ) : ℤ) ≤ ev d c'.nmem f) ∧
      (HasPot he m₂ → (dual he m₂).IsPot (evf d c'.nmem)) ∧
      k₁ ≤ 5 * nf d + 2 ∧ k₂ ≤ (26 * nd d + 6) * nf d + 2 := by
  obtain ⟨c₁, k₁, e₁, hI₁, hn₁, hk₁⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 20)
    (b := 3) (body := eStep) (IE d W m₂ (c.nreg 32)) (fun c => (nf d - c.nreg 20) * 5)
    (fun c h => h.wb) (fun c hc hlt => eStep_exec he c hc hlt)
    ⟨hc, hR, ho, by omega, rfl, fun f hf => by omega, fun a _ => by rw [hm]⟩
  obtain ⟨⟨g0, g1, g2, g3, g4, g5, g7, g8, g9, g10, g11, g12, g13⟩, g6⟩ := hI₁.regs
  have h20₁ : c₁.nreg 20 = nf d := by have := hI₁.r20; rw [g3] at hn₁; omega
  have hw₁ := hI₁.wb
  have e₂ := Exec.copyN (P := inp d) hw₁ 26 0
  have hzero : ∀ f < nf d, ev d c₁.nmem f = 0 := fun f hf => by
    simp [ev, sv, hI₁.done f (by omega)]
  have hI₂ : IB he m₂ (c.nreg 32) { c₁ with nreg := upd c₁.nreg 26 (c₁.nreg 0) } := by
    refine ⟨e₂.wb_right, regs_of hI₁.regs fun r hr => by
      config_simp; rw [upd_other _ _ _ (by omega)], hI₁.out, by config_simp; omega,
      by config_simp; exact hI₁.r32, hI₁.frame, fun f hf => by
        rw [hI₁.done f (by omega)], fun f hf => ?_, fun hP f => ?_⟩
    · config_simp; rw [g0, hzero f hf]; simp
    · config_simp; rw [g0]
      unfold evf; rw [hzero f f.2]
      refine ⟨(dual he m₂).bf_nonpos _ f, ?_⟩
      simp [Digraph.bf]
  obtain ⟨c₃, k₃, e₃, hI₃, hn₃, hk₃⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 26)
    (b := 3) (body := round) (IB he m₂ (c.nreg 32))
    (fun c => (nf d - c.nreg 26) * (26 * nd d + 6)) (fun c h => h.wb)
    (fun c hc hlt => round_exec he hg c hc hlt) hI₂
  have h26 : c₃.nreg 26 = nf d := by
    have := hI₃.r26; rw [hI₃.regs.1.2.2.2.1] at hn₃; omega
  refine ⟨c₁, k₁, _, c₃, k₃, e₁, e₂, e₃, hI₃.wb, hI₃.regs, hI₃.out, hI₃.r32, hI₃.frame, hI₃.ub,
    fun f hf => by have := hI₃.lb f hf; rw [h26] at this; exact this, fun hP => ?_, ?_, ?_⟩
  · -- after `F` rounds the values are `bf F`
    have hp := hI₃.bf hP
    rw [h26] at hp
    have heq : evf d c₃.nmem = (dual he m₂).bf (nf d) := funext fun f => le_antisymm (hp f).2 (hp f).1
    obtain ⟨p, hpp⟩ := hP
    have := (dual he m₂).isPot_bf_card hpp
    rw [card_fin_nf] at this
    rw [heq]; exact this
  · beta_reduce at hk₁; rw [h20] at hk₁; omega
  · beta_reduce at hk₃
    config_simp at hk₃
    rw [g0, Nat.sub_zero] at hk₃
    linarith [Nat.mul_comm (nf d) (26 * nd d + 6)]

/-- The state of the check. -/
structure IC (he : Enc d W) (m₂ m₃ : ℕ → ℕ) (ok : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : Regs d c
  out : c.output = []
  r20 : c.nreg 20 ≤ nd d
  mem : c.nmem = m₃
  r32le : c.nreg 32 ≤ 1
  r32 : c.nreg 32 = 1 ↔ ok = 1 ∧ ∀ j : Fin (nd d), (j : ℕ) < c.nreg 20 →
    evf d m₃ ((dual he m₂).dst j) ≤ evf d m₃ ((dual he m₂).src j) + (dual he m₂).len j

theorem checkStep_exec (he : Enc d W) {m₂ m₃ : ℕ → ℕ} (hg : ∀ j < nd d, |sv d m₂ j| ≤ bsum d)
    (hfr : ∀ a < nd d + 4 * nv d, m₃ a = m₂ a) (hub : ∀ f < nf d, m₃ (nd d + 4 * nv d + f) ≤ zz d)
    (hlb : ∀ f < nf d, -((nf d * nd d * bsum d : ℕ) : ℤ) ≤ ev d m₃ f)
    {ok : ℕ} (c : Config) (hI : IC he m₂ m₃ ok c) (hlt : c.nreg 20 < c.nreg 4) :
    ∃ c' k, Exec (inp d) W checkStep c c' k ∧ IC he m₂ m₃ ok c' ∧
      (nd d - c'.nreg 20) * 26 + k + 2 ≤ (nd d - c.nreg 20) * 26 := by
  have hc := hI.wb
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, h12, h13⟩, h6⟩ := hI.regs
  rw [h4] at hlt
  have hm := hI.mem
  obtain ⟨c₁, k₁, e₁, hw₁, hK₁, hm₁, ho₁, h20₁, h26₁, h32₁, h30₁, h31₁, h22₁, rfl⟩ :=
    cand_exec he c hc hI.regs hlt (by rw [hm]; exact hub)
  have hR₁ := regs_of hI.regs hK₁
  have h1' := hR₁.1.2.1
  -- the comparison
  generalize hi : c.nreg 20 = i at hlt h30₁ h31₁
  have hsn := he.wf.fc_lt i hlt
  have htn := he.wf.fc_lt _ (he.wf.rv_lt i hlt)
  have hgi : c.nmem i = m₂ i := by rw [hm]; exact hfr i (by have := he.size; omega)
  have hgb := abs_le.1 (hg i hlt)
  have hgv : (m₂ i : ℤ) = sv d m₂ i + zz d := by unfold sv; ring
  have hev : ∀ f, (m₃ (nd d + 4 * nv d + f) : ℤ) = ev d m₃ f + zz d := by
    intro f; unfold ev sv; ring
  have hT : (nf d * nd d + 1) * bsum d ≤ zz d := by
    unfold zz; exact Nat.mul_le_mul le_rfl (by omega)
  have hT' : (((nf d * nd d + 1) * bsum d : ℕ) : ℤ) = (nf d * nd d * bsum d : ℕ) + bsum d := by
    push_cast; ring
  have hTz : (((nf d * nd d + 1) * bsum d : ℕ) : ℤ) ≤ zz d := by exact_mod_cast hT
  have hls := hlb _ hsn
  have hC : c.nmem i ≤ c.nmem (nd d + 4 * nv d + fc d i) + cp d i + zz d := by
    rw [hgi, hm]; have := hev (fc d i); omega
  have hCv : ((c.nmem (nd d + 4 * nv d + fc d i) + cp d i + zz d - c.nmem i : ℕ) : ℤ) - zz d =
      ev d m₃ (fc d i) + (dual he m₂).len ⟨i, hlt⟩ := by
    rw [Nat.cast_sub hC]
    push_cast
    rw [hm, hev, ← hm, hgi, hgv]
    simp only [dual]; ring
  have hcmp : c₁.nreg 30 < c₁.nreg 31 ↔ evf d m₃ ((dual he m₂).src ⟨i, hlt⟩) +
      (dual he m₂).len ⟨i, hlt⟩ < evf d m₃ ((dual he m₂).dst ⟨i, hlt⟩) := by
    rw [h30₁, h31₁]
    show _ ↔ ev d m₃ (fc d i) + (dual he m₂).len ⟨i, hlt⟩ < ev d m₃ (fc d (rv d i))
    have key2 : (c.nmem (nd d + 4 * nv d + fc d (rv d i)) : ℤ) = ev d m₃ (fc d (rv d i)) + zz d := by
      rw [hm]; exact hev _
    rw [← Nat.cast_lt (α := ℤ)]
    constructor <;> intro h <;> linarith
  unfold checkStep
  refine spec_seq ?_
  refine ⟨c₁, 21, e₁, ?_⟩
  refine spec_seq ?_
  by_cases hv : c₁.nreg 30 < c₁.nreg 31
  · refine spec_ifLtN_true hv ?_
    refine spec_instr (Exec.copyN hw₁ _ _) fun hw₂ => ?_
    have hsz := he.size
    refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h20₁, hi, h1']; omega))
      fun hw₃ => ?_
    refine ⟨⟨hw₃, regs_of hR₁ fun r hr => by
        config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega,
      by config_simp; exact ho₁.trans hI.out, by config_simp; rw [h20₁, hi, h1']; omega,
      by config_simp; rw [hm₁, hm], by config_simp; rw [hR₁.1.1]; omega, ?_⟩, ?_⟩
    · config_simp; rw [hR₁.1.1]
      simp only [Nat.zero_ne_one, false_iff, not_and, not_forall]
      intro _
      exact ⟨⟨i, hlt⟩, by rw [h20₁, hi, h1']; simp, by have := hcmp.1 hv; omega⟩
    · config_simp; rw [h20₁, hi, h1']; omega
  · refine spec_ifLtN_false hv ?_
    refine spec_skip hw₁ ?_
    have hsz := he.size
    refine spec_instr (Exec.addN hw₁ _ _ _ (by rw [h20₁, hi, h1']; omega)) fun hw₃ => ?_
    refine ⟨⟨hw₃, regs_of hR₁ fun r hr => by
        config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega,
      by config_simp; exact ho₁.trans hI.out, by config_simp; rw [h20₁, hi, h1']; omega,
      by config_simp; rw [hm₁, hm], by config_simp; rw [h32₁ 32 le_rfl]; exact hI.r32le, ?_⟩, ?_⟩
    · config_simp; rw [h32₁ 32 le_rfl, hI.r32, h20₁, hi, h1']
      constructor
      · rintro ⟨hok, hall⟩
        refine ⟨hok, fun j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · exact hall j hj
        · have hji : j = ⟨i, hlt⟩ := Fin.ext hj
          subst hji
          exact not_lt.1 fun h => hv (hcmp.2 h)
      · rintro ⟨hok, hall⟩
        exact ⟨hok, fun j hj => hall j (by omega)⟩
    · config_simp; rw [h20₁, hi, h1']; omega

/-- **The check.** -/
theorem check_exec (he : Enc d W) {m₂ m₃ : ℕ → ℕ} (hg : ∀ j < nd d, |sv d m₂ j| ≤ bsum d)
    (hfr : ∀ a < nd d + 4 * nv d, m₃ a = m₂ a) (hub : ∀ f < nf d, m₃ (nd d + 4 * nv d + f) ≤ zz d)
    (hlb : ∀ f < nf d, -((nf d * nd d * bsum d : ℕ) : ℤ) ≤ ev d m₃ f)
    (c : Config) (hc : WordsBounded W c) (hR : Regs d c) (ho : c.output = [])
    (hm : c.nmem = m₃) (h20 : c.nreg 20 = 0) (h32 : c.nreg 32 ≤ 1) :
    ∃ c' k, Exec (inp d) W (.whileLtN 20 4 checkStep) c c' k ∧ WordsBounded W c' ∧ Regs d c' ∧
      c'.output = [] ∧ c'.nreg 32 ≤ 1 ∧
      (c'.nreg 32 = 1 ↔ c.nreg 32 = 1 ∧ (dual he m₂).IsPot (evf d m₃)) ∧
      k ≤ 26 * nd d + 2 := by
  obtain ⟨c', k, e, hI, hn, hk⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 20)
    (b := 4) (body := checkStep) (IC he m₂ m₃ (c.nreg 32)) (fun c => (nd d - c.nreg 20) * 26)
    (fun c h => h.wb) (fun c hc hlt => checkStep_exec he hg hfr hub hlb c hc hlt)
    ⟨hc, hR, ho, by omega, hm, h32, by
      constructor
      · intro h; exact ⟨h, fun j hj => by omega⟩
      · exact fun h => h.1⟩
  have h20' : c'.nreg 20 = nd d := by have := hI.r20; rw [hI.regs.1.2.2.2.2.1] at hn; omega
  refine ⟨c', k, e, hI.wb, hI.regs, hI.out, hI.r32le, ?_, ?_⟩
  · rw [hI.r32, h20']
    constructor
    · rintro ⟨hok, hall⟩
      refine ⟨hok, fun j => ?_⟩
      have := hall j j.2
      show evf d m₃ ((dual he m₂).dst j) ≤ evf d m₃ ((dual he m₂).src j) + (dual he m₂).len j
      exact this
    · rintro ⟨hok, hall⟩
      exact ⟨hok, fun j _ => hall j⟩
  · beta_reduce at hk; rw [h20] at hk; omega

end Feas

end PlanarFlow
