module

public import PlanarFlow.BKMNW.MsTourB

/-!
# The corner order on the machine, part C: the selection of the corners

Along the walk `TR[0], …, TR[per - 1]`, the position `s` is selected when the label
`l = FL[TR[s]]` of its face is marked (`FP'[l] = 1`: a face along the path) and was not seen
before (`qsel`). For each selected position, in increasing order, the program `ftS` writes its
position (`CS`), its dart (`CD`), and the number of the corner at the label (`CN'[l]`).

* `qsel`, `selL j` (the selected positions below `j`, in increasing order), `selL_succ`,
  `mem_selL`, `length_selL_le`;
* **`ftS_exec`**: within `20 per + 4` steps, `r8157 = |selL per|`, `CS[r] = (selL per)[r]`,
  `CD[r] = TR[(selL per)[r]]`, `CN'[FL[CD[r]]] = r`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-! ### The selected positions -/

/-- The position `s` of the walk is selected: its label is marked and not seen before. -/
def qsel (tr fl fp0 : ℕ → ℕ) (s : ℕ) : Bool :=
  fp0 (fl (tr s)) == 1 && (List.range s).all fun s' => fl (tr s') != fl (tr s)

lemma qsel_iff {tr fl fp0 : ℕ → ℕ} {s : ℕ} :
    qsel tr fl fp0 s = true ↔ fp0 (fl (tr s)) = 1 ∧ ∀ s' < s, fl (tr s') ≠ fl (tr s) := by
  simp [qsel]

/-- The selected positions below `j`, in increasing order. -/
def selL (tr fl fp0 : ℕ → ℕ) (j : ℕ) : List ℕ := (List.range j).filter (qsel tr fl fp0)

lemma selL_succ (tr fl fp0 : ℕ → ℕ) (j : ℕ) :
    selL tr fl fp0 (j + 1) =
      if qsel tr fl fp0 j = true then selL tr fl fp0 j ++ [j] else selL tr fl fp0 j := by
  unfold selL
  rw [List.range_succ, List.filter_append]
  by_cases h : qsel tr fl fp0 j = true
  · simp [h]
  · simp [h]

lemma mem_selL {tr fl fp0 : ℕ → ℕ} {j s : ℕ} :
    s ∈ selL tr fl fp0 j ↔ s < j ∧ qsel tr fl fp0 s = true := by
  simp [selL]

lemma length_selL_le (tr fl fp0 : ℕ → ℕ) (j : ℕ) : (selL tr fl fp0 j).length ≤ j := by
  unfold selL
  exact (List.length_filter_le _ _).trans (by simp)

lemma selL_get_lt {tr fl fp0 : ℕ → ℕ} {j r : ℕ} (hr : r < (selL tr fl fp0 j).length) :
    (selL tr fl fp0 j)[r] < j :=
  (mem_selL.1 (List.getElem_mem hr)).1

lemma selL_getD_lt {tr fl fp0 : ℕ → ℕ} {j r : ℕ} (hr : r < (selL tr fl fp0 j).length) :
    (selL tr fl fp0 j).getD r 0 < j := by
  rw [List.getD_eq_getElem _ _ hr]; exact selL_get_lt hr

lemma selL_sorted (tr fl fp0 : ℕ → ℕ) (j : ℕ) :
    (selL tr fl fp0 j).Pairwise (· < ·) :=
  List.Pairwise.filter _ (List.pairwise_lt_range)

/-! ### The program -/

def ftS0 : Stmt := block [.constN 8172 0, .constN 8157 0]

/-- `x := TR[j]`, `l := FL[x]`, `fp := FP'[l]`. -/
def ftSRd : Stmt :=
  block [.addN 8174 8164 8172, .loadN 8173 8174, .addN 8174 8159 8173, .loadN 8176 8174,
    .addN 8174 8161 8176, .loadN 8175 8174]

/-- `CD[b] := x`, `CS[b] := j`, `CN'[l] := b`, `FP'[l] := 2`, `b := b + 1`. -/
def ftSRec : Stmt :=
  block [.addN 8174 8165 8157, .storeN 8174 8173, .addN 8174 8166 8157, .storeN 8174 8172,
    .addN 8174 8167 8176, .storeN 8174 8157, .addN 8174 8161 8176, .storeN 8174 8169,
    .addN 8157 8157 8158]

def ftSBody : Stmt :=
  .seq ftSRd (.seq (.ifLtN 8175 8169 (.ifLtN 8170 8175 ftSRec .skip) .skip)
    (block [.addN 8172 8172 8158]))

/-- **The selection of the corners** along the walk. -/
def ftS : Stmt := .seq ftS0 (.whileLtN 8172 8156 ftSBody)

theorem ftSRd_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb k Pb S j x l : ℕ}
    (hR : FtRegs c m RVb RTb k Pb S) (r72 : c.nreg 8172 = j) (hj : j < m)
    (hx : c.nmem (S + 6 * m + j) = x) (hxm : x < m) (hl : c.nmem (S + m + x) = l)
    (hl1 : 1 ≤ l) (hlm : l ≤ m) (hW : S + 10 * m + 2 ≤ W) :
    ∃ c' t, Exec P W ftSRd c c' t ∧ t = 6 ∧ c'.nreg 8173 = x ∧ c'.nreg 8176 = l ∧
      c'.nreg 8175 = c.nmem (S + 3 * m - 1 + l) ∧
      (∀ r, r ≠ 8173 → r ≠ 8174 → r ≠ 8175 → r ≠ 8176 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ftSRd
  exec_block
  all_goals try ((try config_simp); (try simp only [hR.r64, hR.r59, hR.r61, r72, hx, hl]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r a b d e => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [hR.r64, hR.r59, hR.r61, r72, hx, hl]; done)
    | (simp only [upd_apply]; split_ifs <;> omega)

theorem ftSRec_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb k Pb S j x l b : ℕ}
    (hR : FtRegs c m RVb RTb k Pb S) (r72 : c.nreg 8172 = j) (r73 : c.nreg 8173 = x)
    (r76 : c.nreg 8176 = l) (r57 : c.nreg 8157 = b) (hj : j < m) (hb : b < m) (hx : x < m)
    (hl1 : 1 ≤ l) (hlm : l ≤ m) (hW : S + 10 * m + 2 ≤ W) :
    ∃ c' t, Exec P W ftSRec c c' t ∧ t = 9 ∧ c'.nreg 8157 = b + 1 ∧
      c'.nmem = upd (upd (upd (upd c.nmem (S + 7 * m + b) x) (S + 8 * m + b) j)
        (S + 9 * m - 1 + l) b) (S + 3 * m - 1 + l) 2 ∧
      (∀ r, r ≠ 8157 → r ≠ 8174 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ftSRec
  exec_block
  all_goals try ((try config_simp); (try simp only [hR.r65, hR.r66, hR.r67, hR.r61, hR.r69, hR.r58, r72, r73, r76, r57]); omega)
  refine ⟨rfl, ?_, ?_, fun r a d => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [hR.r65, hR.r66, hR.r67, hR.r61, hR.r69, hR.r58, r72, r73, r76, r57]; done)
    | (simp only [upd_apply]; split_ifs <;> omega)

/-- The invariant of the selection after `j` positions. -/
def SInv (tr fl fp0 : ℕ → ℕ) (m S : ℕ) (c₀ : Config) (j : ℕ) (c : Config) : Prop :=
  (∀ r, r ≠ 8157 → (r < 8172 ∨ 8176 < r) → c.nreg r = c₀.nreg r) ∧
  c.nreg 8157 = (selL tr fl fp0 j).length ∧
  (∀ r < (selL tr fl fp0 j).length, c.nmem (S + 8 * m + r) = (selL tr fl fp0 j).getD r 0 ∧
    c.nmem (S + 7 * m + r) = tr ((selL tr fl fp0 j).getD r 0) ∧
    c.nmem (S + 9 * m - 1 + fl (tr ((selL tr fl fp0 j).getD r 0))) = r) ∧
  (∀ l, 1 ≤ l → l ≤ m → c.nmem (S + 3 * m - 1 + l) =
    if fp0 l = 1 ∧ ∃ s < j, fl (tr s) = l then 2 else fp0 l) ∧
  (∀ a, (a < S + 3 * m ∨ S + 4 * m ≤ a) → (a < S + 7 * m ∨ S + 10 * m ≤ a) →
    c.nmem a = c₀.nmem a) ∧
  c.rreg = c₀.rreg ∧ c.rmem = c₀.rmem ∧ c.output = c₀.output

lemma getElem_append_one {l : List ℕ} {a r : ℕ} (h : r < (l ++ [a]).length) :
    (l ++ [a])[r] = if h' : r < l.length then l[r] else a := by
  split_ifs with h'
  · exact List.getElem_append_left h'
  · have : r = l.length := by simp at h; omega
    subst this; simp

/-- One position of the selection. -/
theorem ftSBody_step {tr fl fp0 : ℕ → ℕ} {m RVb RTb k Pb S per j : ℕ} {c₀ c : Config}
    (hc : WordsBounded W c) (hR : FtRegs c₀ m RVb RTb k Pb S) (hper : per ≤ m) (hj : j < per)
    (htr : ∀ s < per, c₀.nmem (S + 6 * m + s) = tr s ∧ tr s < m)
    (hfl : ∀ x < m, c₀.nmem (S + m + x) = fl x ∧ 1 ≤ fl x ∧ fl x ≤ m)
    (hfp : ∀ l, 1 ≤ l → l ≤ m → fp0 l ≤ 1) (hW : S + 10 * m + 2 ≤ W)
    (r72 : c.nreg 8172 = j) (hI : SInv tr fl fp0 m S c₀ j c) :
    ∃ c' u, Exec P W ftSBody c c' u ∧ u ≤ 18 ∧ c'.nreg 8172 = j + 1 ∧
      SInv tr fl fp0 m S c₀ (j + 1) c' := by
  obtain ⟨iR, i57, iL, iF, iM, irr, irm, io⟩ := hI
  have hRc : FtRegs c m RVb RTb k Pb S :=
    hR.of fun r h1 h2 h3 h4 => iR r h4 (by omega)
  obtain ⟨etr, htrm⟩ := htr j hj
  obtain ⟨efl, hl1, hlm⟩ := hfl (tr j) htrm
  set l := fl (tr j) with hl
  have hLj := length_selL_le tr fl fp0 j
  set L := selL tr fl fp0 j with hL
  have e1 : c.nmem (S + 6 * m + j) = tr j := by rw [iM _ (by omega) (by omega), etr]
  have e2 : c.nmem (S + m + tr j) = l := by rw [iM _ (by omega) (by omega), efl]
  obtain ⟨c₁, k₁, e₁, hk₁, a73, a76, a75, aR, am, ar, arm, ao⟩ :=
    ftSRd_exec (P := P) c hc hRc r72 (by omega) e1 htrm e2 hl1 hlm hW
  have hR₁ : FtRegs c₁ m RVb RTb k Pb S := hRc.of fun r h1 h2 _ _ => aR r (by omega)
    (by omega) (by omega) (by omega)
  have hfpv := iF l hl1 hlm
  have hfp0 := hfp l hl1 hlm
  -- the increment, from any configuration
  have inc : ∀ d : Config, WordsBounded W d → d.nreg 8172 = j → d.nreg 8158 = 1 →
      ∃ d' k, Exec P W (block [.addN 8172 8172 8158]) d d' k ∧ k = 1 ∧ d'.nreg 8172 = j + 1 ∧
        (∀ x, x ≠ 8172 → d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem ∧ d'.rreg = d.rreg ∧
        d'.rmem = d.rmem ∧ d'.output = d.output := fun d hd s72 s58 => by
    exec_block
    all_goals try ((try config_simp); (try simp only [s72, s58]); omega)
    refine ⟨rfl, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [s58, s72]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have q72 : c₁.nreg 8172 = j := by rw [aR _ (by omega) (by omega) (by omega) (by omega), r72]
  by_cases hsel : fp0 l = 1 ∧ ¬ ∃ s < j, fl (tr s) = l
  · -- the position is selected
    have hq : qsel tr fl fp0 j = true := by
      rw [qsel_iff]; exact ⟨hsel.1, fun s' hs' h => hsel.2 ⟨s', hs', h⟩⟩
    have hv1 : c.nmem (S + 3 * m - 1 + l) = 1 := by
      rw [hfpv]; simp only [hsel.2, and_false, ↓reduceIte, hsel.1]
    have t1 : c₁.nreg 8175 < c₁.nreg 8169 := by rw [a75, hv1, hR₁.r69]; omega
    have t2 : c₁.nreg 8170 < c₁.nreg 8175 := by rw [a75, hv1, hR₁.r70]; omega
    have hb : L.length < m := by omega
    obtain ⟨c₂, k₂, e₂, hk₂, b57, bm, bR, br, brm, bo⟩ := ftSRec_exec (P := P) c₁ e₁.wb_right
      hR₁ q72 a73 a76 (by rw [aR _ (by omega) (by omega) (by omega) (by omega), i57])
      (by omega) hb htrm hl1 hlm hW
    obtain ⟨c₃, k₃, e₃, hk₃, d72, dR, dm, dr, drm, dout⟩ := inc c₂ e₂.wb_right
      (by rw [bR _ (by omega) (by omega), q72]) (by rw [bR _ (by omega) (by omega), hR₁.r58])
    have hL' : selL tr fl fp0 (j + 1) = L ++ [j] := by rw [selL_succ, iteT hq]
    refine ⟨c₃, k₁ + ((k₂ + 1 + 1) + k₃),
      .seq e₁ (.seq (.ifLtN_true t1 (.ifLtN_true t2 e₂)) e₃), by omega, d72,
      fun r h57 hr => ?_, ?_, fun r hr => ?_, fun l' h1 h2 => ?_, fun a ha ha' => ?_,
      by rw [dr, br, ar, irr], by rw [drm, brm, arm, irm], by rw [dout, bo, ao, io]⟩
    · rw [dR r (by omega), bR r h57 (by omega), aR r (by omega) (by omega) (by omega)
        (by omega), iR r h57 hr]
    · rw [dR _ (by omega), b57, hL']
      simp
    · rw [hL'] at hr ⊢
      rw [dm, bm]
      have hlen : (L ++ [j]).length = L.length + 1 := by simp
      by_cases hrL : r < L.length
      · obtain ⟨f1, f2, f3⟩ := iL r hrL
        have hlt : L.getD r 0 < j := selL_getD_lt hrL
        have hne : fl (tr (L.getD r 0)) ≠ l := fun h => hsel.2 ⟨L.getD r 0, hlt, h⟩
        rw [List.getD_append _ _ _ _ hrL]
        refine ⟨?_, ?_, ?_⟩
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
            upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), am]; exact f1
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
            upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), am]; exact f2
        · obtain ⟨-, h1, h2⟩ := hfl _ (htr (L.getD r 0) (by omega)).2
          rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
            upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), am]; exact f3
      · have hr' : r = L.length := by rw [hlen] at hr; omega
        subst hr'
        rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
        simp only [List.getD_cons_zero]
        refine ⟨?_, ?_, ?_⟩
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_same]
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
            upd_other _ _ _ (by omega), upd_same]
        · rw [upd_other _ _ _ (by omega), upd_same]
    · rw [dm, bm]
      have hiff : (∃ s < j + 1, fl (tr s) = l') ↔ (∃ s < j, fl (tr s) = l') ∨ l = l' := by
        constructor
        · rintro ⟨s, hs, e⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
          · exact Or.inl ⟨s, hs, e⟩
          · exact Or.inr e
        · rintro (⟨s, hs, e⟩ | e)
          · exact ⟨s, by omega, e⟩
          · exact ⟨j, by omega, e⟩
      by_cases hll : l = l'
      · subst hll
        rw [upd_same]; simp only [hiff, or_true, and_true, hsel.1, ↓reduceIte]
      · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
          upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), am, iF l' h1 h2]
        simp only [hiff, hll, or_false]
    · rw [dm, bm, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
        upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), am]
      exact iM a ha ha'
  · -- the position is not selected
    have hq : qsel tr fl fp0 j = false := by
      cases h : qsel tr fl fp0 j
      · rfl
      · rw [qsel_iff] at h
        exact absurd ⟨h.1, fun ⟨s, hs, e⟩ => h.2 s hs e⟩ hsel
    have hL' : selL tr fl fp0 (j + 1) = L := by rw [selL_succ]; simp [hq, hL]
    -- the test fails
    have hskip : ∃ c₂ k₂, Exec P W (.ifLtN 8175 8169 (.ifLtN 8170 8175 ftSRec .skip) .skip)
        c₁ c₂ k₂ ∧ k₂ ≤ 4 ∧ c₂ = c₁ := by
      by_cases h0 : fp0 l = 1
      · have hseen : ∃ s < j, fl (tr s) = l := by
          by_contra h'; exact hsel ⟨h0, h'⟩
        have hv2 : c.nmem (S + 3 * m - 1 + l) = 2 := by
          rw [hfpv]; simp only [h0, hseen, and_self, ↓reduceIte]
        have t1 : ¬ c₁.nreg 8175 < c₁.nreg 8169 := by rw [a75, hv2, hR₁.r69]; omega
        exact ⟨c₁, 0 + 2, .ifLtN_false t1 (.skip e₁.wb_right), by omega, rfl⟩
      · have hv0 : c.nmem (S + 3 * m - 1 + l) = 0 := by
          rw [hfpv]; simp only [h0, false_and, ↓reduceIte]; omega
        have t1 : c₁.nreg 8175 < c₁.nreg 8169 := by rw [a75, hv0, hR₁.r69]; omega
        have t2 : ¬ c₁.nreg 8170 < c₁.nreg 8175 := by rw [a75, hv0, hR₁.r70]; omega
        exact ⟨c₁, 0 + 2 + 1, .ifLtN_true t1 (.ifLtN_false t2 (.skip e₁.wb_right)), by omega,
          rfl⟩
    obtain ⟨c₂, k₂, e₂, hk₂, rfl⟩ := hskip
    obtain ⟨c₃, k₃, e₃, hk₃, d72, dR, dm, dr, drm, dout⟩ := inc c₂ e₁.wb_right q72 hR₁.r58
    refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, d72,
      fun r h57 hr => ?_, ?_, fun r hr => ?_, fun l' h1 h2 => ?_, fun a ha ha' => ?_,
      by rw [dr, ar, irr], by rw [drm, arm, irm], by rw [dout, ao, io]⟩
    · rw [dR r (by omega), aR r (by omega) (by omega) (by omega) (by omega), iR r h57 hr]
    · rw [dR _ (by omega), aR _ (by omega) (by omega) (by omega) (by omega), i57, hL']
    · rw [hL'] at hr ⊢; rw [dm, am]; exact iL r hr
    · rw [dm, am, iF l' h1 h2]
      have hiff : (∃ s < j + 1, fl (tr s) = l') ↔ (∃ s < j, fl (tr s) = l') ∨ l = l' := by
        constructor
        · rintro ⟨s, hs, e⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
          · exact Or.inl ⟨s, hs, e⟩
          · exact Or.inr e
        · rintro (⟨s, hs, e⟩ | e)
          · exact ⟨s, by omega, e⟩
          · exact ⟨j, by omega, e⟩
      by_cases hll : l = l'
      · subst hll
        by_cases h0 : fp0 l = 1
        · have hseen : ∃ s < j, fl (tr s) = l := by
            by_contra h'; exact hsel ⟨h0, h'⟩
          simp only [hiff, h0, hseen, true_or, and_self, ↓reduceIte]
        · simp only [h0, false_and, ↓reduceIte]
      · simp only [hiff, hll, or_false]
    · rw [dm, am]; exact iM a ha ha'

/-- **The selection of the corners**: from `r8156 = per ≤ m`, the walk `TR[s] = tr s < m`
(`s < per`), labels `FL[x] = fl x ∈ [1, m]` and marks `FP'[l] = fp0 l ≤ 1`, within
`20 per + 4` steps `r8157 = |selL per|` and for `r < |selL per|`: `CS[r] = (selL per)[r]`,
`CD[r] = tr (selL per)[r]`, `CN'[fl (tr (selL per)[r])] = r`; memory outside `FP`, `CD`, `CS`,
`CN` and registers outside `8157`, `8172 … 8176` kept. -/
theorem ftS_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb k Pb S per : ℕ}
    (hR : FtRegs c m RVb RTb k Pb S) {tr fl fp0 : ℕ → ℕ} (r56 : c.nreg 8156 = per)
    (hper : per ≤ m) (htr : ∀ s < per, c.nmem (S + 6 * m + s) = tr s ∧ tr s < m)
    (hfl : ∀ x < m, c.nmem (S + m + x) = fl x ∧ 1 ≤ fl x ∧ fl x ≤ m)
    (hfp : ∀ l, 1 ≤ l → l ≤ m → c.nmem (S + 3 * m - 1 + l) = fp0 l ∧ fp0 l ≤ 1)
    (hW : S + 10 * m + 2 ≤ W) :
    ∃ c' u, Exec P W ftS c c' u ∧ u ≤ 20 * per + 4 ∧
      c'.nreg 8157 = (selL tr fl fp0 per).length ∧
      (∀ r < (selL tr fl fp0 per).length,
        c'.nmem (S + 8 * m + r) = (selL tr fl fp0 per).getD r 0 ∧
        c'.nmem (S + 7 * m + r) = tr ((selL tr fl fp0 per).getD r 0) ∧
        c'.nmem (S + 9 * m - 1 + fl (tr ((selL tr fl fp0 per).getD r 0))) = r) ∧
      (∀ a, (a < S + 3 * m ∨ S + 4 * m ≤ a) → (a < S + 7 * m ∨ S + 10 * m ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 8157 → (r < 8172 ∨ 8176 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ftS
  obtain ⟨c₁, k₁, e₁, hk₁, g72, g57, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W ftS0 c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 8172 = 0 ∧ c₁.nreg 8157 = 0 ∧
      (∀ x, x ≠ 8172 → x ≠ 8157 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold ftS0
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  have hfp' : ∀ l, 1 ≤ l → l ≤ m → fp0 l ≤ 1 := fun l h1 h2 => (hfp l h1 h2).2
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h72, hI⟩ := lnRange (P := P) (a := 8172) (b := 8156)
    (body := ftSBody) (fun j d => SInv tr fl fp0 m S c j d) (B := 18) c₁ e₁.wb_right g72
    (by rw [gn₁ _ (by omega) (by omega), r56]) (Nat.zero_le per)
    ⟨fun r h57 hr => gn₁ r (by omega) h57, by rw [g57]; simp [selL],
      fun r hr => absurd hr (by simp [selL]), fun l h1 h2 => by
        rw [gm₁, (hfp l h1 h2).1]; simp, fun a _ _ => by rw [gm₁], gr₁, grm₁, go₁⟩
    (fun j d hlo hhi hw h72 h56 hI => by
      obtain ⟨d', u, ex, hu, h72', hI'⟩ := ftSBody_step (P := P) hw hR hper hhi htr hfl hfp'
        hW h72 hI
      exact ⟨d', u, ex, hu, h72', by rw [hI'.1 _ (by omega) (by omega), r56], hI'⟩)
  obtain ⟨iR, i57, iL, -, iM, irr, irm, io⟩ := hI
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by norm_num at hk₂; omega, i57, iL, iM, iR, irr, irm, io⟩

end MsEnc

end BKMNW

end PlanarFlow
