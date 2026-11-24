module

public import PlanarFlow.NegSSSP.LinGlue
public import PlanarFlow.MSSP.IsoTree
public import Mathlib.Data.List.GetD

/-!
# The isolating weights of a spanning tree of the dual graph, on the machine

The isolating weight `MSSP.treeW C` of a rooted spanning tree `C` of the dual graph
(`PlanarFlow/MSSP/IsoTree.lean`: `tsz y` on `rev (par y)`, `- tsz y` on `par y`, `0` off the
tree) is an isolating weight with the exceptional face `C.root`, of absolute value at most `#F`
(`MSSP.treeW_isoW`, `MSSP.abs_treeW_le`). Here a program on **natural words only** writes the
words `B + treeW C d` (`B ≥ #F`, so that they are natural numbers, at most `B + #F`) from the
arrays of Klein's input (`Klein.kRegs`): the faces `FC[σ d] = φ (face d)`, the reverses
`RV[σ d] = σ (rev d)` and the parent darts `CS[i] = σ (par cs[i])` of the cotree in its order
`cs` (non-root faces of nondecreasing depth, `Klein.Orders`):

1. `SZ[x] := 1` for the `nN` face numbers;
2. for `i = lc - 1, …, 0`: `SZ[FC[CS i]] += SZ[FC[RV[CS i]]]` (the size of the face `cs[i]`
   added to that of its parent; `MSSP.szFold_eq_tsz`);
3. `WT[x] := B` for the `nD` darts;
4. for `i < lc`: `WT[CS i] := B - SZ[y]`, `WT[RV[CS i]] := B + SZ[y]`, `y = FC[RV[CS i]]`.

* `iwProg_exec`: the program on index functions, within `5 nN + 5 nD + 38 lc + 20` steps
  (`izFold`: the sizes of phase 2; the words of phase 4 when the targets `CS i`, `RV (CS i)` are
  distinct).
* `iwProg_treeW`: **on the arrays of a tree**, the word at `Wb + σ d` is `B + treeW C d` for
  every dart `d`; `treeW C` is an isolating weight (`MSSP.treeW_isoW`), so the lengths
  `MSSP.isoLen` can be formed from these words.

Registers: natural `1700 … 1708` (inputs `nN`, `nD`, `lc`, `Fb`, `Rb`, `Cb`, `Zb`, `Wb`, `B`),
`1710 … 1718` (scratch). No real register or real memory is touched.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The program -/

/-- `SZ[x] := 1` for `x < nN` (`r1710 = 1`). -/
def iwInit : Stmt :=
  .seq (block [.constN 1710 1, .constN 1711 0])
    (.whileLtN 1711 1700 (block [.addN 1712 1706 1711, .storeN 1712 1710, .addN 1711 1711 1710]))

/-- The reads of the parent dart number `i = r1712`: `r1713 = CS i`, `r1714 = RV (CS i)`,
`r1715 = FC (RV (CS i))`. -/
def iwRd : Stmt := block [.addN 1713 1705 1712, .loadN 1713 1713, .addN 1714 1704 1713,
  .loadN 1714 1714, .addN 1715 1703 1714, .loadN 1715 1715]

/-- One step of phase 2 at the counter `j = r1711`: `i = lc - (j + 1)`,
`SZ[FC (CS i)] += SZ[FC (RV (CS i))]`. -/
def iwSzBody : Stmt :=
  .seq (block [.addN 1712 1711 1710, .subN 1712 1702 1712]) <|
  .seq iwRd <|
  block [.addN 1716 1703 1713, .loadN 1716 1716, .addN 1715 1706 1715, .loadN 1717 1715,
    .addN 1716 1706 1716, .loadN 1718 1716, .addN 1718 1718 1717, .storeN 1716 1718,
    .addN 1711 1711 1710]

/-- Phase 2. -/
def iwSz : Stmt := .seq (block [.constN 1711 0]) (.whileLtN 1711 1702 iwSzBody)

/-- `WT[x] := B` for `x < nD`. -/
def iwWInit : Stmt := .seq (block [.constN 1711 0])
  (.whileLtN 1711 1701 (block [.addN 1712 1707 1711, .storeN 1712 1708, .addN 1711 1711 1710]))

/-- One step of phase 4 at `i = r1711`: `WT[CS i] := B - s`, `WT[RV (CS i)] := B + s`,
`s = SZ[FC (RV (CS i))]`. -/
def iwWBody : Stmt :=
  .seq (block [.copyN 1712 1711]) <|
  .seq iwRd <|
  block [.addN 1715 1706 1715, .loadN 1717 1715, .subN 1718 1708 1717, .addN 1712 1707 1713,
    .storeN 1712 1718, .addN 1718 1708 1717, .addN 1712 1707 1714, .storeN 1712 1718,
    .addN 1711 1711 1710]

/-- Phase 4. -/
def iwW : Stmt := .seq (block [.constN 1711 0]) (.whileLtN 1711 1702 iwWBody)

/-- **The program.** -/
def iwProg : Stmt := .seq iwInit (.seq iwSz (.seq iwWInit iwW))

/-! ### The data -/

/-- The registers and the input arrays of `iwProg`. -/
structure IwIn (nN nD lc Fb Rb Cb Zb Wb B : ℕ) (FC RV CS : ℕ → ℕ) (c : Config) : Prop where
  r00 : c.nreg 1700 = nN
  r01 : c.nreg 1701 = nD
  r02 : c.nreg 1702 = lc
  r03 : c.nreg 1703 = Fb
  r04 : c.nreg 1704 = Rb
  r05 : c.nreg 1705 = Cb
  r06 : c.nreg 1706 = Zb
  r07 : c.nreg 1707 = Wb
  r08 : c.nreg 1708 = B
  fc : ∀ i < nD, c.nmem (Fb + i) = FC i
  rv : ∀ i < nD, c.nmem (Rb + i) = RV i
  cs : ∀ i < lc, c.nmem (Cb + i) = CS i

/-- The layout of `iwProg`: the indices in range, the scratch `SZ = [Zb, Zb + nN)` and the
output `WT = [Wb, Wb + nD)` apart from each other and from the inputs, the addresses below the
word bound. -/
structure IwLay (nN nD lc Fb Rb Cb Zb Wb W : ℕ) (FC RV CS : ℕ → ℕ) : Prop where
  fclt : ∀ i < nD, FC i < nN
  rvlt : ∀ i < nD, RV i < nD
  cslt : ∀ i < lc, CS i < nD
  zF : Zb + nN ≤ Fb ∨ Fb + nD ≤ Zb
  zR : Zb + nN ≤ Rb ∨ Rb + nD ≤ Zb
  zC : Zb + nN ≤ Cb ∨ Cb + lc ≤ Zb
  wF : Wb + nD ≤ Fb ∨ Fb + nD ≤ Wb
  wR : Wb + nD ≤ Rb ∨ Rb + nD ≤ Wb
  wC : Wb + nD ≤ Cb ∨ Cb + lc ≤ Wb
  zW : Zb + nN ≤ Wb ∨ Wb + nD ≤ Zb
  bF : Fb + nD ≤ W
  bR : Rb + nD ≤ W
  bC : Cb + lc ≤ W
  bZ : Zb + nN ≤ W
  bW : Wb + nD ≤ W
  bN : nN + 1 ≤ W
  bD : nD + 1 ≤ W
  bL : lc + 1 ≤ W

/-- One step of phase 2: the size of the face of `RV (CS i)` added to that of `CS i`. -/
def izStep (FC RV CS : ℕ → ℕ) (i : ℕ) (z : ℕ → ℕ) : ℕ → ℕ :=
  Function.update z (FC (CS i)) (z (FC (CS i)) + z (FC (RV (CS i))))

/-- The sizes after the steps of a list (from its end). -/
def izFold (FC RV CS : ℕ → ℕ) (l : List ℕ) : ℕ → ℕ := l.foldr (izStep FC RV CS) fun _ => 1

variable {P : Input} {W : ℕ} {nN nD lc Fb Rb Cb Zb Wb B : ℕ} {FC RV CS : ℕ → ℕ}

lemma IwIn.mono {c : Config} (hI : IwIn nN nD lc Fb Rb Cb Zb Wb B FC RV CS c) {c' : Config}
    (hn : ∀ r, r < 1710 → c'.nreg r = c.nreg r)
    (hf : ∀ i < nD, c'.nmem (Fb + i) = c.nmem (Fb + i))
    (hr : ∀ i < nD, c'.nmem (Rb + i) = c.nmem (Rb + i))
    (hc : ∀ i < lc, c'.nmem (Cb + i) = c.nmem (Cb + i)) :
    IwIn nN nD lc Fb Rb Cb Zb Wb B FC RV CS c' :=
  ⟨(hn 1700 (by omega)).trans hI.r00, (hn 1701 (by omega)).trans hI.r01,
    (hn 1702 (by omega)).trans hI.r02, (hn 1703 (by omega)).trans hI.r03,
    (hn 1704 (by omega)).trans hI.r04, (hn 1705 (by omega)).trans hI.r05,
    (hn 1706 (by omega)).trans hI.r06, (hn 1707 (by omega)).trans hI.r07,
    (hn 1708 (by omega)).trans hI.r08, fun i hi => (hf i hi).trans (hI.fc i hi),
    fun i hi => (hr i hi).trans (hI.rv i hi), fun i hi => (hc i hi).trans (hI.cs i hi)⟩

/-- `IwIn` is kept by a run changing the registers `≥ 1710` and the memory in `SZ`, `WT`
only. -/
lemma IwIn.keep (hL : IwLay nN nD lc Fb Rb Cb Zb Wb W FC RV CS) {c : Config}
    (hI : IwIn nN nD lc Fb Rb Cb Zb Wb B FC RV CS c) {c' : Config}
    (hn : ∀ r, r < 1710 → c'.nreg r = c.nreg r)
    (hm : ∀ a, (a < Zb ∨ Zb + nN ≤ a) → (a < Wb ∨ Wb + nD ≤ a) → c'.nmem a = c.nmem a) :
    IwIn nN nD lc Fb Rb Cb Zb Wb B FC RV CS c' := by
  have := hL.zF; have := hL.zR; have := hL.zC; have := hL.wF; have := hL.wR; have := hL.wC
  exact hI.mono hn (fun i hi => hm _ (by omega) (by omega)) (fun i hi => hm _ (by omega) (by omega))
    (fun i hi => hm _ (by omega) (by omega))

/-! ### The phases -/

theorem iwInit_exec (hL : IwLay nN nD lc Fb Rb Cb Zb Wb W FC RV CS) (c : Config)
    (hc : WordsBounded W c) (hI : IwIn nN nD lc Fb Rb Cb Zb Wb B FC RV CS c) :
    ∃ c' k, Exec P W iwInit c c' k ∧ k ≤ 5 * nN + 4 ∧
      ((∀ x < nN, c'.nmem (Zb + x) = 1) ∧
        (∀ a, (a < Zb ∨ Zb + nN ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 1710 ∨ 1718 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 1710 = 1 ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.bZ; have := hL.bN
  unfold iwInit
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x < i, c'.nmem (Zb + x) = 1) ∧ (∀ a, (a < Zb ∨ Zb + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1710 ∨ 1718 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 1710 = 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 1711) (bR := 1700)
    (body := block [.addN 1712 1706 1711, .storeN 1712 1710, .addN 1711 1711 1710]) J (K := 3)
    (n := nN) _ ‹_› (by config_simp) (by config_simp; rw [hI.r00]) ?_
    (fun i c₁ hi hw ha hb ⟨g0, gm, gn, g410, gr, grm, go⟩ => by
      have e406 : c₁.nreg 1706 = Zb := (gn 1706 (by omega)).trans hI.r06
      exec_block
      all_goals try ((try config_simp); (try simp only [e406, ha, g410]); omega)
      dsimp only [J]
      config_simp
      simp only [e406, ha, g410]
      and_intros
      all_goals first
        | trivial
        | omega
        | assumption
        | (intro x hx; simp only [upd_apply]; split_ifs
           · rfl
           · exact g0 x (by omega))
        | (intro a ha'; simp only [upd_apply]
           rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact gm a (by omega))
        | (intro r hr; simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr))) ?_
  · refine ⟨fun x hx => absurd hx (by omega), fun a _ => ?_, fun r hr => ?_, ?_, rfl, rfl, rfl⟩
    all_goals config_simp
    · simp only [upd_apply]; split_ifs <;> omega
  intro c₂ k₂ hk₂ _ hJ₂
  obtain ⟨-, g0, gm, gn, g410, gr, grm, go⟩ := hJ₂
  exact ⟨by omega, g0, gm, gn, g410, gr, grm, go⟩

theorem iwRd_exec (hL : IwLay nN nD lc Fb Rb Cb Zb Wb W FC RV CS) (c : Config)
    (hc : WordsBounded W c) (hI : IwIn nN nD lc Fb Rb Cb Zb Wb B FC RV CS c) {i : ℕ}
    (hi : i < lc) (h12 : c.nreg 1712 = i) :
    ∃ c' k, Exec P W iwRd c c' k ∧ k ≤ 6 ∧
      (c'.nreg 1713 = CS i ∧ c'.nreg 1714 = RV (CS i) ∧ c'.nreg 1715 = FC (RV (CS i)) ∧
        (∀ r, r ≠ 1713 → r ≠ 1714 → r ≠ 1715 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.bC; have := hL.bR; have := hL.bF
  have hcs := hL.cslt i hi
  have hrv := hL.rvlt _ hcs
  have e1 := hI.cs i hi
  have e2 := hI.rv _ hcs
  have e3 := hI.fc _ hrv
  unfold iwRd
  exec_block
  all_goals try ((try config_simp); (try simp only [hI.r03, hI.r04, hI.r05, h12, e1, e2]); omega)
  config_simp
  simp only [hI.r03, hI.r04, hI.r05, h12, e1, e2, e3]
  and_intros
  all_goals first
    | trivial
    | omega
    | rfl
    | (intro r h1 h2 h3; simp only [upd_apply]; split_ifs <;> first | omega | rfl)

/-- The invariant of phase 2 after `j` steps (from `c₀`). -/
def IwSzInv (nN lc Zb : ℕ) (FC RV CS : ℕ → ℕ) (c₀ : Config) (j : ℕ) (c : Config) : Prop :=
  (∀ x < nN, c.nmem (Zb + x) = izFold FC RV CS (List.range' (lc - j) j) x) ∧
    (∀ a, (a < Zb ∨ Zb + nN ≤ a) → c.nmem a = c₀.nmem a) ∧
    (∀ r, r < 1710 ∨ 1718 < r → c.nreg r = c₀.nreg r) ∧ c.nreg 1710 = 1 ∧
    c.rreg = c₀.rreg ∧ c.rmem = c₀.rmem ∧ c.output = c₀.output

lemma range'_step {lc j : ℕ} (hj : j < lc) :
    List.range' (lc - (j + 1)) (j + 1) = (lc - (j + 1)) :: List.range' (lc - j) j := by
  rw [List.range'_succ]
  congr 2
  omega

theorem iwSzBody_exec (hL : IwLay nN nD lc Fb Rb Cb Zb Wb W FC RV CS) {c₀ : Config}
    (hI₀ : IwIn nN nD lc Fb Rb Cb Zb Wb B FC RV CS c₀)
    (hZ : ∀ j ≤ lc, ∀ x, izFold FC RV CS (List.range' (lc - j) j) x ≤ W)
    (j : ℕ) (c : Config) (hj : j < lc) (hc : WordsBounded W c) (h11 : c.nreg 1711 = j)
    (hJ : IwSzInv nN lc Zb FC RV CS c₀ j c) :
    ∃ c' k, Exec P W iwSzBody c c' k ∧ k ≤ 17 ∧ c'.nreg 1711 = j + 1 ∧
      IwSzInv nN lc Zb FC RV CS c₀ (j + 1) c' := by
  obtain ⟨gz, gm, gn, g10, gr, grm, go⟩ := hJ
  have hI : IwIn nN nD lc Fb Rb Cb Zb Wb B FC RV CS c :=
    hI₀.keep hL (fun r hr => gn r (Or.inl hr)) (fun a ha _ => gm a ha)
  have := hL.bZ; have := hL.bF; have := hL.bL
  set i := lc - (j + 1) with hi
  have hil : i < lc := by omega
  have hcs := hL.cslt i hil
  have hrv := hL.rvlt _ hcs
  have hy := hL.fclt _ hrv
  have hu := hL.fclt _ hcs
  unfold iwSzBody
  refine spec_seq ?_
  exec_block
  all_goals try ((try config_simp); (try simp only [h11, g10]); omega)
  refine spec_seq ?_
  refine spec_use (iwRd_exec (P := P) (B := B) hL _ (by assumption)
    (hI.mono (fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl)
      (fun _ _ => by rfl) (fun _ _ => by rfl) (fun _ _ => by rfl)) hil
    (by config_simp; simp only [h11, g10, hI.r02]; omega)) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨f13, f14, f15, fn, fnm, fr, frm, fo⟩
  config_simp at fn
  config_simp at fnm
  config_simp at fr
  config_simp at frm
  config_simp at fo
  have e03 : c₁.nreg 1703 = Fb := by rw [fn 1703 (by omega) (by omega) (by omega)]; config_simp; exact hI.r03
  have e06 : c₁.nreg 1706 = Zb := by rw [fn 1706 (by omega) (by omega) (by omega)]; config_simp; exact hI.r06
  have e10 : c₁.nreg 1710 = 1 := by rw [fn 1710 (by omega) (by omega) (by omega)]; config_simp; exact g10
  have e11 : c₁.nreg 1711 = j := by rw [fn 1711 (by omega) (by omega) (by omega)]; config_simp; exact h11
  have eu : c₁.nmem (Fb + CS i) = FC (CS i) := by rw [fnm]; exact hI.fc _ hcs
  have ezy : c₁.nmem (Zb + FC (RV (CS i))) =
      izFold FC RV CS (List.range' (lc - j) j) (FC (RV (CS i))) := by rw [fnm]; exact gz _ hy
  have ezu : c₁.nmem (Zb + FC (CS i)) =
      izFold FC RV CS (List.range' (lc - j) j) (FC (CS i)) := by rw [fnm]; exact gz _ hu
  have hstep : izFold FC RV CS (List.range' (lc - (j + 1)) (j + 1)) =
      izStep FC RV CS i (izFold FC RV CS (List.range' (lc - j) j)) := by
    rw [range'_step hj]; rfl
  have hval : izFold FC RV CS (List.range' (lc - j) j) (FC (CS i)) +
      izFold FC RV CS (List.range' (lc - j) j) (FC (RV (CS i))) ≤ W := by
    have := hZ (j + 1) (by omega) (FC (CS i))
    rw [hstep] at this
    unfold izStep at this
    rwa [Function.update_self] at this
  exec_block
  all_goals try
    ((try config_simp); (try simp only [e03, e06, e10, e11, f13, f15, eu, ezu, ezy]); omega)
  config_simp
  simp only [e03, e06, e10, e11, f13, f15, eu, ezu, ezy]
  refine ⟨by omega, ?_, ?_⟩
  · first | trivial | (simp only [upd_apply]; split_ifs <;> omega)
  refine ⟨fun x hx => ?_, fun a ha => ?_, fun r hr => ?_, ?_, by show c₁.rreg = _; rw [fr, gr], by show c₁.rmem = _; rw [frm, grm],
    by show c₁.output = _; rw [fo, go]⟩
  · rw [hstep]
    unfold izStep
    simp only [upd_apply, Function.update_apply]
    by_cases hx' : x = FC (CS i)
    · subst hx'
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false hx'), fnm]
      exact gz x hx
  · simp only [upd_apply]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), fnm]
    exact gm a ha
  · simp only [upd_apply]
    split_ifs <;> first
      | omega
      | (rw [fn r (by omega) (by omega) (by omega)]
         config_simp
         simp only [upd_apply]
         rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
         exact gn r hr)
  · simp only [upd_apply]; split_ifs <;> first | omega | rfl | exact e10

theorem iwSz_exec (hL : IwLay nN nD lc Fb Rb Cb Zb Wb W FC RV CS) (c : Config)
    (hc : WordsBounded W c) (hI : IwIn nN nD lc Fb Rb Cb Zb Wb B FC RV CS c)
    (hZ : ∀ j ≤ lc, ∀ x, izFold FC RV CS (List.range' (lc - j) j) x ≤ W)
    (h10 : c.nreg 1710 = 1) (h1 : ∀ x < nN, c.nmem (Zb + x) = 1) :
    ∃ c' k, Exec P W iwSz c c' k ∧ k ≤ 19 * lc + 3 ∧
      IwSzInv nN lc Zb FC RV CS c lc c' := by
  unfold iwSz
  refine spec_seq ?_
  have := hL.bL
  exec_block
  all_goals try omega
  refine spec_use (forLoop_exec (P := P) (a := 1711) (bR := 1702) (body := iwSzBody)
    (IwSzInv nN lc Zb FC RV CS c) (K := 17) (n := lc) _ (by assumption) (by config_simp)
    (by config_simp; rw [hI.r02]) ?_
    (fun j c₁ hj hw ha hb hJ => by
      obtain ⟨c', k, e, hk, h1, hJ'⟩ := iwSzBody_exec (P := P) (B := B) hL hI hZ j c₁ hj hw ha hJ
      exact ⟨c', k, e, hk, h1, (hJ'.2.2.1 1702 (by omega)).trans hI.r02, hJ'⟩)) ?_
  · refine ⟨fun x hx => ?_, fun a _ => ?_, fun r hr => ?_, ?_, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals first
      | (rw [h1 x hx]; simp [izFold])
      | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)
      | (simp only [upd_apply]; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), h10])
      | exact h10
      | rfl
  intro c₂ k₂ hk₂ _ hJ₂
  refine ⟨by omega, ?_⟩
  obtain ⟨-, gz, gm, gn, g10, gr, grm, go⟩ := hJ₂
  refine ⟨gz, gm, fun r hr => ?_, g10, gr, grm, go⟩
  rw [gn r hr]
  all_goals try config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

theorem iwWInit_exec (hL : IwLay nN nD lc Fb Rb Cb Zb Wb W FC RV CS) (c : Config)
    (hc : WordsBounded W c) (hI : IwIn nN nD lc Fb Rb Cb Zb Wb B FC RV CS c)
    (h10 : c.nreg 1710 = 1) :
    ∃ c' k, Exec P W iwWInit c c' k ∧ k ≤ 5 * nD + 3 ∧
      ((∀ x < nD, c'.nmem (Wb + x) = B) ∧
        (∀ a, (a < Wb ∨ Wb + nD ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 1710 ∨ 1718 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 1710 = 1 ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.bW; have := hL.bD
  unfold iwWInit
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x < i, c'.nmem (Wb + x) = B) ∧ (∀ a, (a < Wb ∨ Wb + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1710 ∨ 1718 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 1710 = 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 1711) (bR := 1701)
    (body := block [.addN 1712 1707 1711, .storeN 1712 1708, .addN 1711 1711 1710]) J (K := 3)
    (n := nD) _ ‹_› (by config_simp) (by config_simp; rw [hI.r01]) ?_
    (fun i c₁ hi hw ha hb ⟨g0, gm, gn, g410, gr, grm, go⟩ => by
      have e407 : c₁.nreg 1707 = Wb := (gn 1707 (by omega)).trans hI.r07
      have e408 : c₁.nreg 1708 = B := (gn 1708 (by omega)).trans hI.r08
      exec_block
      all_goals try ((try config_simp); (try simp only [e407, ha, g410]); omega)
      dsimp only [J]
      config_simp
      simp only [e407, e408, ha, g410]
      and_intros
      all_goals first
        | trivial
        | omega
        | assumption
        | (intro x hx; simp only [upd_apply]; split_ifs
           · rfl
           · exact g0 x (by omega))
        | (intro a ha'; simp only [upd_apply]
           rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact gm a (by omega))
        | (intro r hr; simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr))) ?_
  · refine ⟨fun x hx => absurd hx (by omega), fun a _ => rfl, fun r hr => ?_, ?_, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals first
      | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)
      | (simp only [upd_apply]; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), h10])
      | exact h10
      | rfl
  intro c₂ k₂ hk₂ _ hJ₂
  obtain ⟨-, g0, gm, gn, g410, gr, grm, go⟩ := hJ₂
  exact ⟨by omega, g0, gm, gn, g410, gr, grm, go⟩

/-- The invariant of phase 4 after `j` steps (from `c₀`, the sizes `Z`). -/
def IwWInv (nD Zb Wb B : ℕ) (FC RV CS Z : ℕ → ℕ) (c₀ : Config) (j : ℕ) (c : Config) : Prop :=
  (∀ i < j, c.nmem (Wb + CS i) = B - Z (FC (RV (CS i)))) ∧
    (∀ i < j, c.nmem (Wb + RV (CS i)) = B + Z (FC (RV (CS i)))) ∧
    (∀ x < nD, (∀ i < j, CS i ≠ x ∧ RV (CS i) ≠ x) → c.nmem (Wb + x) = B) ∧
    (∀ a, (a < Wb ∨ Wb + nD ≤ a) → c.nmem a = c₀.nmem a) ∧
    (∀ r, r < 1710 ∨ 1718 < r → c.nreg r = c₀.nreg r) ∧ c.nreg 1710 = 1 ∧
    c.rreg = c₀.rreg ∧ c.rmem = c₀.rmem ∧ c.output = c₀.output

/-- The targets of phase 4 are distinct. -/
structure IwDist (lc : ℕ) (RV CS : ℕ → ℕ) : Prop where
  inj₁ : ∀ i < lc, ∀ i' < lc, CS i = CS i' → i = i'
  inj₂ : ∀ i < lc, ∀ i' < lc, RV (CS i) = RV (CS i') → i = i'
  dis : ∀ i < lc, ∀ i' < lc, CS i ≠ RV (CS i')

theorem iwWBody_exec (hL : IwLay nN nD lc Fb Rb Cb Zb Wb W FC RV CS) (hD : IwDist lc RV CS)
    {c₀ : Config} (hI₀ : IwIn nN nD lc Fb Rb Cb Zb Wb B FC RV CS c₀) {Z : ℕ → ℕ}
    (hZ0 : ∀ x < nN, c₀.nmem (Zb + x) = Z x) (hZ : ∀ i < lc, B + Z (FC (RV (CS i))) ≤ W)
    (j : ℕ) (c : Config) (hj : j < lc) (hc : WordsBounded W c) (h11 : c.nreg 1711 = j)
    (hJ : IwWInv nD Zb Wb B FC RV CS Z c₀ j c) :
    ∃ c' k, Exec P W iwWBody c c' k ∧ k ≤ 16 ∧ c'.nreg 1711 = j + 1 ∧
      IwWInv nD Zb Wb B FC RV CS Z c₀ (j + 1) c' := by
  obtain ⟨ga, gb, gc, gm, gn, g10, gr, grm, go⟩ := hJ
  have := hL.zW; have := hL.bW; have := hL.bZ; have := hL.bL
  have hI : IwIn nN nD lc Fb Rb Cb Zb Wb B FC RV CS c :=
    hI₀.keep hL (fun r hr => gn r (Or.inl hr)) (fun a _ ha => gm a ha)
  have hcs := hL.cslt j hj
  have hrv := hL.rvlt _ hcs
  have hy := hL.fclt _ hrv
  unfold iwWBody
  refine spec_seq ?_
  exec_block
  refine spec_seq ?_
  refine spec_use (iwRd_exec (P := P) (B := B) hL _ (by assumption)
    (hI.mono (fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl)
      (fun _ _ => by rfl) (fun _ _ => by rfl) (fun _ _ => by rfl)) hj
    (by config_simp; simp only [h11])) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨f13, f14, f15, fn, fnm, fr, frm, fo⟩
  config_simp at fn
  config_simp at fnm
  config_simp at fr
  config_simp at frm
  config_simp at fo
  have e06 : c₁.nreg 1706 = Zb := by rw [fn 1706 (by omega) (by omega) (by omega)]; config_simp; exact hI.r06
  have e07 : c₁.nreg 1707 = Wb := by rw [fn 1707 (by omega) (by omega) (by omega)]; config_simp; exact hI.r07
  have e08 : c₁.nreg 1708 = B := by rw [fn 1708 (by omega) (by omega) (by omega)]; config_simp; exact hI.r08
  have e10 : c₁.nreg 1710 = 1 := by rw [fn 1710 (by omega) (by omega) (by omega)]; config_simp; exact g10
  have e11 : c₁.nreg 1711 = j := by rw [fn 1711 (by omega) (by omega) (by omega)]; config_simp; exact h11
  have ez : c₁.nmem (Zb + FC (RV (CS j))) = Z (FC (RV (CS j))) := by
    rw [fnm, gm _ (by omega)]; exact hZ0 _ hy
  have hzj := hZ j hj
  have hne : CS j ≠ RV (CS j) := hD.dis j hj j hj
  exec_block
  all_goals try
    ((try config_simp); (try simp only [e06, e07, e08, e10, e11, f13, f14, f15, ez]); omega)
  config_simp
  simp only [e06, e07, e08, e10, e11, f13, f14, f15, ez]
  refine ⟨by omega, ?_, ?_⟩
  · first | trivial | (simp only [upd_apply]; split_ifs <;> omega)
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun x hx hx' => ?_, fun a ha => ?_,
    fun r hr => ?_, ?_, by show c₁.rreg = _; rw [fr, gr], by show c₁.rmem = _; rw [frm, grm],
    by show c₁.output = _; rw [fo, go]⟩
  · simp only [upd_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl
    · have h1 : CS i ≠ RV (CS j) := hD.dis i (by omega) j hj
      have h2 : CS i ≠ CS j := fun h => by have := hD.inj₁ i (by omega) j hj h; omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (by omega)), fnm]
      exact ga i hi'
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  · simp only [upd_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl
    · have h1 : RV (CS i) ≠ RV (CS j) := fun h => by have := hD.inj₂ i (by omega) j hj h; omega
      have h2 : RV (CS i) ≠ CS j := fun h => hD.dis j hj i (by omega) h.symm
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (by omega)), fnm]
      exact gb i hi'
    · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  · obtain ⟨h1, h2⟩ := hx' j (by omega)
    simp only [upd_apply]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega)), fnm]
    exact gc x hx fun i hi => hx' i (by omega)
  · simp only [upd_apply]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega)), fnm]
    exact gm a ha
  · simp only [upd_apply]
    split_ifs <;> first
      | omega
      | (rw [fn r (by omega) (by omega) (by omega)]
         config_simp
         simp only [upd_apply]
         rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
         exact gn r hr)
  · simp only [upd_apply]; split_ifs <;> first | omega | rfl | exact e10

theorem iwW_exec (hL : IwLay nN nD lc Fb Rb Cb Zb Wb W FC RV CS) (hD : IwDist lc RV CS)
    (c : Config) (hc : WordsBounded W c) (hI : IwIn nN nD lc Fb Rb Cb Zb Wb B FC RV CS c)
    {Z : ℕ → ℕ} (hZ0 : ∀ x < nN, c.nmem (Zb + x) = Z x)
    (hZ : ∀ i < lc, B + Z (FC (RV (CS i))) ≤ W) (h10 : c.nreg 1710 = 1)
    (hB : ∀ x < nD, c.nmem (Wb + x) = B) :
    ∃ c' k, Exec P W iwW c c' k ∧ k ≤ 18 * lc + 3 ∧ IwWInv nD Zb Wb B FC RV CS Z c lc c' := by
  unfold iwW
  refine spec_seq ?_
  have := hL.bL
  exec_block
  all_goals try omega
  refine spec_use (forLoop_exec (P := P) (a := 1711) (bR := 1702) (body := iwWBody)
    (IwWInv nD Zb Wb B FC RV CS Z c) (K := 16) (n := lc) _ (by assumption) (by config_simp)
    (by config_simp; rw [hI.r02]) ?_
    (fun j c₁ hj hw ha hb hJ => by
      obtain ⟨c', k, e, hk, h1, hJ'⟩ :=
        iwWBody_exec (P := P) (B := B) hL hD hI hZ0 hZ j c₁ hj hw ha hJ
      exact ⟨c', k, e, hk, h1, (hJ'.2.2.2.2.1 1702 (by omega)).trans hI.r02, hJ'⟩)) ?_
  · refine ⟨fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega),
      fun x hx _ => hB x hx, fun a _ => rfl, fun r hr => ?_, ?_, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals first
      | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)
      | (simp only [upd_apply]; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), h10])
      | exact h10
      | rfl
  intro c₂ k₂ hk₂ _ hJ₂
  refine ⟨by omega, ?_⟩
  obtain ⟨-, ga, gb, gc, gm, gn, g10, gr, grm, go⟩ := hJ₂
  refine ⟨ga, gb, gc, gm, fun r hr => ?_, g10, gr, grm, go⟩
  rw [gn r hr]
  all_goals try config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

/-! ### The whole program -/

/-- **The program on index functions**: within `5 nN + 5 nD + 37 lc + 20` steps, with
`Zf = izFold … (range' 0 lc)` the sizes of phase 2, the word at `Wb + CS i` is
`B - Zf (FC (RV (CS i)))`, at `Wb + RV (CS i)` it is `B + Zf (FC (RV (CS i)))`, and `B` at every
other dart; the natural memory changes only in `SZ` and `WT`, the registers `≥ 1710` only. -/
theorem iwProg_exec (hL : IwLay nN nD lc Fb Rb Cb Zb Wb W FC RV CS) (hD : IwDist lc RV CS)
    (c : Config) (hc : WordsBounded W c) (hI : IwIn nN nD lc Fb Rb Cb Zb Wb B FC RV CS c)
    (hZ : ∀ j ≤ lc, ∀ x, izFold FC RV CS (List.range' (lc - j) j) x ≤ W)
    (hZB : ∀ i < lc, B + izFold FC RV CS (List.range' 0 lc) (FC (RV (CS i))) ≤ W) :
    ∃ c' k, Exec P W iwProg c c' k ∧ k ≤ 5 * nN + 5 * nD + 37 * lc + 20 ∧
      ((∀ i < lc, c'.nmem (Wb + CS i) = B - izFold FC RV CS (List.range' 0 lc) (FC (RV (CS i)))) ∧
        (∀ i < lc, c'.nmem (Wb + RV (CS i)) =
          B + izFold FC RV CS (List.range' 0 lc) (FC (RV (CS i)))) ∧
        (∀ x < nD, (∀ i < lc, CS i ≠ x ∧ RV (CS i) ≠ x) → c'.nmem (Wb + x) = B) ∧
        (∀ a, (a < Zb ∨ Zb + nN ≤ a) → (a < Wb ∨ Wb + nD ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 1710 ∨ 1718 < r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.zW
  unfold iwProg
  refine spec_seq ?_
  refine spec_use (iwInit_exec (P := P) (B := B) hL c hc hI) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨a1, a2, a3, a4, a5, a6, a7⟩
  have hI₁ := hI.keep hL (fun r hr => a3 r (Or.inl hr)) (fun a ha _ => a2 a ha)
  refine spec_seq ?_
  refine spec_use (iwSz_exec (P := P) hL c₁ hw₁ hI₁ hZ a4 a1) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨b1, b2, b3, b4, b5, b6, b7⟩
  have hI₂ := hI₁.keep hL (fun r hr => b3 r (Or.inl hr)) (fun a ha _ => b2 a ha)
  refine spec_seq ?_
  refine spec_use (iwWInit_exec (P := P) hL c₂ hw₂ hI₂ b4) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨d1, d2, d3, d4, d5, d6, d7⟩
  have hI₃ := hI₂.keep hL (fun r hr => d3 r (Or.inl hr)) (fun a _ ha => d2 a ha)
  have hZ3 : ∀ x < nN, c₃.nmem (Zb + x) = izFold FC RV CS (List.range' 0 lc) x := fun x hx => by
    rw [d2 _ (by omega), b1 x hx, Nat.sub_self]
  refine spec_use (iwW_exec (P := P) hL hD c₃ hw₃ hI₃ hZ3 hZB d4 d1) ?_
  intro c₄ k₄ hk₄ hw₄ ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩
  refine ⟨by omega, e1, e2, e3, fun a h1 h2 => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [e4 a h2, d2 a h2, b2 a h1, a2 a h1]
  · rw [e5 r hr, d3 r hr, b3 r hr, a3 r hr]
  · rw [e7, d5, b5, a5]
  · rw [e8, d6, b6, a6]
  · rw [e9, d7, b7, a7]

/-! ### On the arrays of a tree -/

section Tree

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-- The faces by dart number. -/
def iwFC {nD : ℕ} (M : CombMap D V F) (σ : D ≃ Fin nD) (φ : F → ℕ) (i : ℕ) : ℕ :=
  if h : i < nD then φ (M.face (σ.symm ⟨i, h⟩)) else 0

/-- The reverses by dart number. -/
def iwRV {nD : ℕ} (M : CombMap D V F) (σ : D ≃ Fin nD) (i : ℕ) : ℕ :=
  if h : i < nD then σ (M.rev (σ.symm ⟨i, h⟩)) else 0

/-- The parent darts of the cotree, in the order `cs`. -/
def iwCS {nD : ℕ} (C : STFlow.DTree M) (σ : D ≃ Fin nD) (cs : List F) (i : ℕ) : ℕ :=
  if h : i < cs.length then σ (C.par cs[i]) else 0

lemma iwCS_eq_getD {nD : ℕ} (C : STFlow.DTree M) (σ : D ≃ Fin nD) (cs : List F) (i : ℕ) :
    iwCS C σ cs i = (cs.map fun y => (σ (C.par y) : ℕ)).getD i 0 := by
  unfold iwCS
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]; rfl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (by omega)]; rfl

lemma iwFC_apply {nD : ℕ} (σ : D ≃ Fin nD) (φ : F → ℕ) (d : D) :
    iwFC M σ φ (σ d) = φ (M.face d) := by
  simp [iwFC]

lemma iwRV_apply {nD : ℕ} (σ : D ≃ Fin nD) (d : D) : iwRV M σ (σ d) = σ (M.rev d) := by
  simp [iwRV]

lemma iwCS_apply {nD : ℕ} (C : STFlow.DTree M) (σ : D ≃ Fin nD) (cs : List F) {i : ℕ}
    (h : i < cs.length) : iwCS C σ cs i = σ (C.par cs[i]) := by
  simp [iwCS, h]

variable (C : STFlow.DTree M) (cs : List F) {nD : ℕ} (σ : D ≃ Fin nD) (φ : F → ℕ)

open MSSP in
/-- The sizes of phase 2 on the arrays of a tree are those of `MSSP.szFold`. -/
theorem izFold_tree (hφ : Function.Injective φ) (hr : ∀ y ∈ cs, y ≠ C.root) :
    ∀ n s, s + n = cs.length →
      (∀ y, izFold (iwFC M σ φ) (iwRV M σ) (iwCS C σ cs) (List.range' s n) (φ y) =
        szFold C (cs.drop s) y) ∧
      (∀ x, (∀ y, φ y ≠ x) →
        izFold (iwFC M σ φ) (iwRV M σ) (iwCS C σ cs) (List.range' s n) x = 1)
  | 0, s, h => by
    have e : cs.drop s = [] := List.drop_eq_nil_of_le (by omega)
    simp [izFold, szFold, e]
  | n + 1, s, h => by
    obtain ⟨ih1, ih2⟩ := izFold_tree hφ hr n (s + 1) (by omega)
    have hs : s < cs.length := by omega
    set a := cs[s] with ha
    have har : a ≠ C.root := hr a (List.getElem_mem hs)
    have e1 : List.range' s (n + 1) = s :: List.range' (s + 1) n := List.range'_succ ..
    have e2 : cs.drop s = a :: cs.drop (s + 1) := List.drop_eq_getElem_cons hs
    have eu : iwFC M σ φ (iwCS C σ cs s) = φ (C.up a) := by
      rw [iwCS_apply C σ cs hs, iwFC_apply, C.up_of_ne har]
    have ey : iwFC M σ φ (iwRV M σ (iwCS C σ cs s)) = φ a := by
      rw [iwCS_apply C σ cs hs, iwRV_apply, iwFC_apply, C.head_par a har]
    rw [e1, e2]
    refine ⟨fun y => ?_, fun x hx => ?_⟩
    · show izStep _ _ _ s (izFold _ _ _ (List.range' (s + 1) n)) (φ y) = szStep C a _ y
      unfold izStep szStep
      rw [eu, ey, ih1, ih1]
      by_cases hy : y = C.up a
      · subst hy; rw [Function.update_self, Function.update_self]; rfl
      · rw [Function.update_of_ne (fun h => hy (hφ h)), Function.update_of_ne hy, ih1]; rfl
    · show izStep _ _ _ s (izFold _ _ _ (List.range' (s + 1) n)) x = 1
      unfold izStep
      rw [eu, Function.update_of_ne (fun h => hx _ h.symm), ih2 x hx]

open MSSP in
/-- **The isolating weight of the cotree on the machine.** On the arrays of Klein's input for a
rooted spanning tree `C` of the dual graph (faces `φ (face d)`, reverses `σ (rev d)`, parent darts
`σ (par cs[i])` along an order `cs` of the non-root faces by nondecreasing depth), with
`#F ≤ B` and `B + #F ≤ W`, `iwProg` writes **`B + treeW C d` at `Wb + σ d` for every dart `d`**
within `5 nN + 5 nD + 37 |cs| + 20` steps. `treeW C` is an isolating weight with the exceptional
face `C.root`, at most `#F` in absolute value (`MSSP.treeW_isoW`, `MSSP.abs_treeW_le`). -/
theorem iwProg_treeW (hnd : cs.Nodup) (hmem : ∀ y, y ∈ cs ↔ y ≠ C.root)
    (hpw : cs.Pairwise (fun a b => C.depth a ≤ C.depth b)) (hφ : Function.Injective φ)
    {nN Fb Rb Cb Zb Wb B : ℕ} (hφn : ∀ y, φ y < nN) (hB : Fintype.card F ≤ B)
    (hBW : B + Fintype.card F ≤ W)
    (hL : IwLay nN nD cs.length Fb Rb Cb Zb Wb W (iwFC M σ φ) (iwRV M σ) (iwCS C σ cs))
    (c : Config) (hc : WordsBounded W c)
    (hI : IwIn nN nD cs.length Fb Rb Cb Zb Wb B (iwFC M σ φ) (iwRV M σ) (iwCS C σ cs) c) :
    ∃ c' k, Exec P W iwProg c c' k ∧ k ≤ 5 * nN + 5 * nD + 37 * cs.length + 20 ∧
      (∀ d, (c'.nmem (Wb + σ d) : ℤ) = B + treeW C d) ∧
      (∀ a, (a < Zb ∨ Zb + nN ≤ a) → (a < Wb ∨ Wb + nD ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1710 ∨ 1718 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hr : ∀ y ∈ cs, y ≠ C.root := fun y hy => (hmem y).1 hy
  have hpar : ∀ {i} (h : i < cs.length), iwCS C σ cs i = σ (C.par cs[i]) :=
    fun h => iwCS_apply C σ cs h
  have hrv : ∀ {i} (h : i < cs.length), iwRV M σ (iwCS C σ cs i) = σ (M.rev (C.par cs[i])) :=
    fun h => by rw [hpar h, iwRV_apply]
  have hgi : ∀ {i i'} (h : i < cs.length) (h' : i' < cs.length), cs[i] = cs[i'] → i = i' :=
    fun h h' e => (List.Nodup.getElem_inj_iff hnd).1 e
  have hD : IwDist cs.length (iwRV M σ) (iwCS C σ cs) := by
    refine ⟨fun i hi i' hi' e => ?_, fun i hi i' hi' e => ?_, fun i hi i' hi' e => ?_⟩
    · rw [hpar hi, hpar hi'] at e
      have e' := σ.injective (Fin.ext e)
      have := C.head_par _ (hr _ (List.getElem_mem hi))
      rw [e', C.head_par _ (hr _ (List.getElem_mem hi'))] at this
      exact hgi hi hi' this.symm
    · rw [hrv hi, hrv hi'] at e
      have e' := M.rev_injective (σ.injective (Fin.ext e))
      have := C.head_par _ (hr _ (List.getElem_mem hi))
      rw [e', C.head_par _ (hr _ (List.getElem_mem hi'))] at this
      exact hgi hi hi' this.symm
    · rw [hpar hi, hrv hi'] at e
      exact par_ne_rev_par C (hr _ (List.getElem_mem hi')) (hr _ (List.getElem_mem hi))
        (σ.injective (Fin.ext e))
  have hfold := izFold_tree C cs σ φ hφ hr
  have hdrop : ∀ s, (cs.drop s).Nodup ∧ (∀ y ∈ cs.drop s, y ≠ C.root) ∧
      (cs.drop s).Pairwise (fun a b => C.depth a ≤ C.depth b) := fun s =>
    ⟨hnd.sublist (List.drop_sublist _ _), fun y hy => hr y (List.mem_of_mem_drop hy),
      hpw.sublist (List.drop_sublist _ _)⟩
  have hZ : ∀ j ≤ cs.length, ∀ x,
      izFold (iwFC M σ φ) (iwRV M σ) (iwCS C σ cs) (List.range' (cs.length - j) j) x ≤ W := by
    intro j hj x
    obtain ⟨h1, h2⟩ := hfold j (cs.length - j) (by omega)
    by_cases hx : ∃ y, φ y = x
    · obtain ⟨y, rfl⟩ := hx
      rw [h1]
      obtain ⟨a, b, e⟩ := hdrop (cs.length - j)
      have := szFold_le C _ a b e y
      omega
    · push Not at hx
      rw [h2 x hx]
      have := Fintype.card_pos_iff.2 ⟨C.root⟩
      omega
  have hZf : ∀ y, izFold (iwFC M σ φ) (iwRV M σ) (iwCS C σ cs) (List.range' 0 cs.length) (φ y) =
      szFold C cs y := fun y => by
    rw [(hfold cs.length 0 (by omega)).1 y, List.drop_zero]
  have hy : ∀ {i} (h : i < cs.length), iwFC M σ φ (iwRV M σ (iwCS C σ cs i)) = φ cs[i] :=
    fun h => by rw [hrv h, iwFC_apply, C.head_par _ (hr _ (List.getElem_mem h))]
  have hZB : ∀ i < cs.length, B + izFold (iwFC M σ φ) (iwRV M σ) (iwCS C σ cs)
      (List.range' 0 cs.length) (iwFC M σ φ (iwRV M σ (iwCS C σ cs i))) ≤ W := by
    intro i hi
    rw [hy hi, hZf]
    have := szFold_le C cs hnd hr hpw cs[i]
    omega
  obtain ⟨c', k, e, hk, h1, h2, h3, hm, hn, hrr, hrm, ho⟩ := iwProg_exec (P := P) hL hD c hc hI hZ hZB
  refine ⟨c', k, e, hk, fun d => ?_, hm, hn, hrr, hrm, ho⟩
  by_cases hp : ∃ y, y ≠ C.root ∧ d = C.par y
  · obtain ⟨y, hy0, rfl⟩ := hp
    obtain ⟨i, hi, hiy⟩ := List.mem_iff_getElem.1 ((hmem y).2 hy0)
    have := h1 i hi
    rw [hy hi, hZf, hpar hi, hiy, szFold_eq_tsz C cs hnd hmem hpw hy0] at this
    rw [this, treeW_par C hy0]
    have := tsz_lt C hy0
    push_cast [show tsz C y ≤ B by omega]
    ring
  by_cases hq : ∃ y, y ≠ C.root ∧ d = M.rev (C.par y)
  · obtain ⟨y, hy0, rfl⟩ := hq
    obtain ⟨i, hi, hiy⟩ := List.mem_iff_getElem.1 ((hmem y).2 hy0)
    have := h2 i hi
    rw [hy hi, hZf, hrv hi, hiy, szFold_eq_tsz C cs hnd hmem hpw hy0] at this
    rw [this, treeW_rev_par C hy0]
    push_cast; ring
  push Not at hp hq
  rw [treeW_off C (fun y h => hp y h) (fun y h => hq y h), h3 _ (σ d).isLt fun i hi => ⟨?_, ?_⟩]
  · simp
  · rw [hpar hi]; intro h
    exact hp _ (hr _ (List.getElem_mem hi)) (σ.injective (Fin.ext h)).symm
  · rw [hrv hi]; intro h
    exact hq _ (hr _ (List.getElem_mem hi)) (σ.injective (Fin.ext h)).symm

end Tree

end NegSSSP

end PlanarFlow
