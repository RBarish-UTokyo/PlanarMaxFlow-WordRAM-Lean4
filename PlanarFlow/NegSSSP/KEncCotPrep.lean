module

public import PlanarFlow.NegSSSP.KEncCotRun

/-!
# The inputs of the search for the cotree, on the machine

The cotree of the one-face encoding is a breadth-first search tree of the faces through the
darts off the spanning tree `T` (`PlanarFlow/NegSSSP/KEncCotRun.lean`). Its inputs are computed
from the arrays by darts `RV` (reversal), `NF` (the node `of + τ (face d)` of the face) and the
parent darts `IT[j] = σ (T.par ts[j])` of the order of `T` (`Klein.KInit`):

* `cpPrep`: per dart `i`, the keep flag `KE[i] = 1`, the key `KY[i] = NF[i] - of` and the head
  `HH[i] = NF[RV[i]] - of`; then for every parent dart `a = IT[j]`, `KE[a] = KE[RV[a]] = 0`.
* `cpPrep_exec`: within `17 nD + 11 lt + 10` steps (natural words only).

Registers: natural `1700 … 1708` (inputs `nD`, `lt`, `ITb`, `RVb`, `NFb`, `of`, and the outputs
`KEb = Ob`, `KYb = Ob + nD`, `HHb = Ob + 2 nD`), `1710 … 1719` (scratch).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Relation WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge

variable {P : Input} {W : ℕ}

/-! ### The program -/

/-- The dart `i = r1711`: `KY[i] := NF[i] - of`, `HH[i] := NF[RV[i]] - of`, `KE[i] := 1`. -/
def cpInitBody : Stmt :=
  block [.addN 1712 1704 1711, .loadN 1713 1712, .subN 1713 1713 1705, .addN 1712 1707 1711,
    .storeN 1712 1713, .addN 1712 1703 1711, .loadN 1714 1712, .addN 1712 1704 1714,
    .loadN 1713 1712, .subN 1713 1713 1705, .addN 1712 1708 1711, .storeN 1712 1713,
    .addN 1712 1706 1711, .storeN 1712 1710, .addN 1711 1711 1710]

/-- The parent dart `a = IT[j]`, `j = r1711`: `KE[a] := 0`, `KE[RV[a]] := 0`. -/
def cpMarkBody : Stmt :=
  block [.addN 1712 1702 1711, .loadN 1714 1712, .addN 1712 1706 1714, .storeN 1712 1719,
    .addN 1712 1703 1714, .loadN 1715 1712, .addN 1712 1706 1715, .storeN 1712 1719,
    .addN 1711 1711 1710]

/-- **The inputs of the search for the cotree.** -/
def cpPrep : Stmt :=
  .seq (block [.constN 1710 1, .constN 1719 0, .constN 1711 0, .addN 1707 1706 1700,
    .addN 1708 1707 1700]) <|
  .seq (.whileLtN 1711 1700 cpInitBody) <|
  .seq (block [.constN 1711 0]) (.whileLtN 1711 1701 cpMarkBody)

/-! ### The bodies -/

variable {nD lt ITb RVb NFb of KEb KYb HHb : ℕ}

theorem cpInitBody_exec (c : Config) (hc : WordsBounded W c) {i : ℕ}
    (r03 : c.nreg 1703 = RVb) (r04 : c.nreg 1704 = NFb) (r05 : c.nreg 1705 = of)
    (r06 : c.nreg 1706 = KEb) (r07 : c.nreg 1707 = KYb) (r08 : c.nreg 1708 = HHb)
    (r10 : c.nreg 1710 = 1) (r11 : c.nreg 1711 = i) (hi : i < nD)
    (hrv : c.nmem (RVb + i) < nD) (w1 : NFb + nD ≤ W) (w2 : RVb + nD ≤ W) (w3 : KEb + nD ≤ W)
    (w4 : KYb + nD ≤ W) (w5 : HHb + nD ≤ W)
    (d1 : RVb + i ≠ KYb + i) (d2 : NFb + c.nmem (RVb + i) ≠ KYb + i) :
    ∃ c' k, Exec P W cpInitBody c c' k ∧ k = 15 ∧
      c'.nmem = upd (upd (upd c.nmem (KYb + i) (c.nmem (NFb + i) - of)) (HHb + i)
        (c.nmem (NFb + c.nmem (RVb + i)) - of)) (KEb + i) 1 ∧
      c'.nreg 1711 = i + 1 ∧
      (∀ r, r ≠ 1711 → r ≠ 1712 → r ≠ 1713 → r ≠ 1714 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cpInitBody
  exec_block
  all_goals try ((try config_simp); (try simp only [r03, r04, r06, r07, r08, r10, r11,
    upd_apply, d1, ↓reduceIte]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r03, r04, r05, r06, r07, r08, r10, r11, upd_apply, d1, d2,
      ↓reduceIte]
  · config_simp; simp only [r10, r11]
  · config_simp; simp only [upd_apply, h1, h2, h3, h4, ↓reduceIte]

theorem cpMarkBody_exec (c : Config) (hc : WordsBounded W c) {j : ℕ}
    (r02 : c.nreg 1702 = ITb) (r03 : c.nreg 1703 = RVb) (r06 : c.nreg 1706 = KEb)
    (r10 : c.nreg 1710 = 1) (r11 : c.nreg 1711 = j) (r19 : c.nreg 1719 = 0) (hj : j < lt)
    (hit : c.nmem (ITb + j) < nD) (hrv : c.nmem (RVb + c.nmem (ITb + j)) < nD)
    (w1 : ITb + lt ≤ W) (w2 : RVb + nD ≤ W) (w3 : KEb + nD ≤ W)
    (d1 : RVb + c.nmem (ITb + j) ≠ KEb + c.nmem (ITb + j)) :
    ∃ c' k, Exec P W cpMarkBody c c' k ∧ k = 9 ∧
      c'.nmem = upd (upd c.nmem (KEb + c.nmem (ITb + j)) 0)
        (KEb + c.nmem (RVb + c.nmem (ITb + j))) 0 ∧
      c'.nreg 1711 = j + 1 ∧
      (∀ r, r ≠ 1711 → r ≠ 1712 → r ≠ 1714 → r ≠ 1715 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cpMarkBody
  exec_block
  all_goals try ((try config_simp); (try simp only [r02, r03, r06, r10, r11,
    upd_apply, d1, ↓reduceIte]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r02, r03, r06, r11, r19, upd_apply, d1, ↓reduceIte]
  · config_simp; simp only [r10, r11]
  · config_simp; simp only [upd_apply, h1, h2, h3, h4, ↓reduceIte]


/-! ### The whole program -/

set_option maxHeartbeats 2000000 in
/-- **The inputs of the search for the cotree on the machine**: with `r1700 … r1706` =
`nD, lt, ITb, RVb, NFb, of, Ob`, the outputs at `Ob` (`KE`), `Ob + nD` (`KY`), `Ob + 2 nD` (`HH`)
apart from the inputs, `cpPrep` ends within `17 nD + 11 lt + 10` steps with
`KE[x] = 0` if `x` is a parent dart `IT[j]` or its reverse and `1` otherwise,
`KY[x] = NF[x] - of`, `HH[x] = NF[RV[x]] - of`; the natural memory changes only in the outputs,
the natural registers only in `1707 … 1719`. -/
theorem cpPrep_exec {Ob : ℕ} (c : Config) (hc : WordsBounded W c)
    (r00 : c.nreg 1700 = nD) (r01 : c.nreg 1701 = lt) (r02 : c.nreg 1702 = ITb)
    (r03 : c.nreg 1703 = RVb) (r04 : c.nreg 1704 = NFb) (r05 : c.nreg 1705 = of)
    (r06 : c.nreg 1706 = Ob)
    (hit : ∀ j < lt, c.nmem (ITb + j) < nD) (hrv : ∀ i < nD, c.nmem (RVb + i) < nD)
    (lI : ITb + lt ≤ Ob ∨ Ob + 3 * nD ≤ ITb) (lR : RVb + nD ≤ Ob ∨ Ob + 3 * nD ≤ RVb)
    (lN : NFb + nD ≤ Ob ∨ Ob + 3 * nD ≤ NFb)
    (wI : ITb + lt ≤ W) (wR : RVb + nD ≤ W) (wN : NFb + nD ≤ W) (wO : Ob + 3 * nD ≤ W)
    (w1 : 1 ≤ W) :
    ∃ c' t, Exec P W cpPrep c c' t ∧ t ≤ 17 * nD + 11 * lt + 10 ∧
      ((∀ x < nD, c'.nmem (Ob + x) = if ∃ j < lt, x = c.nmem (ITb + j) ∨
          x = c.nmem (RVb + c.nmem (ITb + j)) then 0 else 1) ∧
        (∀ x < nD, c'.nmem (Ob + nD + x) = c.nmem (NFb + x) - of) ∧
        (∀ x < nD, c'.nmem (Ob + 2 * nD + x) = c.nmem (NFb + c.nmem (RVb + x)) - of) ∧
        (∀ a, a < Ob ∨ Ob + 3 * nD ≤ a → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 1707 ∨ 1719 < r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
        c'.rmem = c.rmem ∧ c'.output = c.output) := by
  classical
  unfold cpPrep
  refine spec_seq ?_
  exec_block
  all_goals try ((try config_simp); (try simp only [r00, r06]); omega)
  -- per dart
  let J : ℕ → Config → Prop := fun i d =>
    (∀ x < i, d.nmem (Ob + x) = 1 ∧ d.nmem (Ob + nD + x) = c.nmem (NFb + x) - of ∧
        d.nmem (Ob + 2 * nD + x) = c.nmem (NFb + c.nmem (RVb + x)) - of) ∧
      (∀ a, a < Ob ∨ Ob + 3 * nD ≤ a → d.nmem a = c.nmem a) ∧
      (∀ r, r < 1707 ∨ 1719 < r → d.nreg r = c.nreg r) ∧
      d.nreg 1707 = Ob + nD ∧ d.nreg 1708 = Ob + 2 * nD ∧
      d.nreg 1710 = 1 ∧ d.nreg 1719 = 0 ∧ d.rreg = c.rreg ∧ d.rmem = c.rmem ∧
      d.output = c.output
  refine spec_seq ?_
  refine spec_use (forLoop_exec (P := P) (a := 1711) (bR := 1700) (body := cpInitBody) J
    (K := 15) (n := nD) _ ‹_› (by config_simp) (by config_simp; exact r00) ?_
    (fun i d hi hw ha hb ⟨g, gm, gn, g07, g08, g10, g19, gr, grm, go⟩ => by
      have e03 : d.nreg 1703 = RVb := (gn 1703 (by omega)).trans r03
      have e04 : d.nreg 1704 = NFb := (gn 1704 (by omega)).trans r04
      have e05 : d.nreg 1705 = of := (gn 1705 (by omega)).trans r05
      have e06 : d.nreg 1706 = Ob := (gn 1706 (by omega)).trans r06
      have hrvi : d.nmem (RVb + i) = c.nmem (RVb + i) := gm _ (by omega)
      have hrv' := hrv i hi
      have hnf1 : d.nmem (NFb + i) = c.nmem (NFb + i) := gm _ (by omega)
      have hnf2 : d.nmem (NFb + d.nmem (RVb + i)) = c.nmem (NFb + c.nmem (RVb + i)) := by
        rw [hrvi]; exact gm _ (by omega)
      obtain ⟨d', k, ex, hk, hm, h11, hn, hr, hrm, ho⟩ := cpInitBody_exec (P := P) (nD := nD)
        d hw e03 e04 e05 e06 g07 g08 g10 ha hi (by rw [hrvi]; exact hrv') wN wR (by omega)
        (by omega) (by omega) (by omega) (by rw [hrvi]; omega)
      refine ⟨d', k, ex, by omega, h11, by
        rw [hn _ (by omega) (by omega) (by omega) (by omega)]; exact hb, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, by rw [hr, gr], by rw [hrm, grm], by rw [ho, go]⟩
      · intro x hx
        rw [hm, hnf1, hnf2]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | rfl
        · obtain ⟨g1, g2, g3⟩ := g x hx
          simp only [upd_apply, show Ob + x ≠ Ob + i by omega, show Ob + x ≠ Ob + 2 * nD + i by omega,
            show Ob + x ≠ Ob + nD + x by omega, show Ob + nD + x ≠ Ob + i by omega,
            show Ob + nD + x ≠ Ob + 2 * nD + i by omega, show Ob + nD + x ≠ Ob + nD + i by omega,
            show Ob + 2 * nD + x ≠ Ob + i by omega, show Ob + 2 * nD + x ≠ Ob + 2 * nD + i by omega,
            show Ob + 2 * nD + x ≠ Ob + nD + i by omega, show Ob + x ≠ Ob + nD + i by omega,
            ↓reduceIte]
          exact ⟨g1, g2, g3⟩
        · simp only [upd_apply, show Ob + nD + x ≠ Ob + x by omega,
            show Ob + nD + x ≠ Ob + 2 * nD + x by omega, show Ob + 2 * nD + x ≠ Ob + x by omega,
            show Ob + x ≠ Ob + 2 * nD + x by omega, show Ob + x ≠ Ob + nD + x by omega,
            ↓reduceIte]
          exact ⟨trivial, trivial, trivial⟩
      · intro a ha'
        rw [hm]
        simp only [upd_apply, show a ≠ Ob + i by omega, show a ≠ Ob + nD + i by omega,
          show a ≠ Ob + 2 * nD + i by omega, ↓reduceIte]
        exact gm a ha'
      · intro r hr'
        rw [hn r (by omega) (by omega) (by omega) (by omega)]; exact gn r hr'
      · rw [hn _ (by omega) (by omega) (by omega) (by omega)]; exact g07
      · rw [hn _ (by omega) (by omega) (by omega) (by omega)]; exact g08
      · rw [hn _ (by omega) (by omega) (by omega) (by omega)]; exact g10
      · rw [hn _ (by omega) (by omega) (by omega) (by omega)]; exact g19)) ?_
  · refine ⟨fun x hx => absurd hx (by omega), fun _ _ => rfl, fun r hr => ?_, ?_, ?_, ?_, ?_,
      rfl, rfl, rfl⟩
    all_goals config_simp
    · simp only [upd_apply]; split_ifs <;> omega
    · simp only [r06, r00]
    · simp only [r06, r00]; omega
  intro c₁ k₁ hk₁ hw₁ ⟨_, g, gm, gn, g07, g08, g10, g19, gr, grm, go⟩
  -- the parent darts
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J2 : ℕ → Config → Prop := fun j d =>
    (∀ x < nD, d.nmem (Ob + x) = if ∃ j' < j, x = c.nmem (ITb + j') ∨
        x = c.nmem (RVb + c.nmem (ITb + j')) then 0 else 1) ∧
      (∀ a, a < Ob ∨ Ob + nD ≤ a → d.nmem a = c₁.nmem a) ∧
      (∀ r, r < 1710 ∨ 1719 < r → d.nreg r = c₁.nreg r) ∧
      d.nreg 1710 = 1 ∧ d.nreg 1719 = 0 ∧ d.rreg = c.rreg ∧ d.rmem = c.rmem ∧
      d.output = c.output
  have q01 : c₁.nreg 1701 = lt := (gn 1701 (by omega)).trans r01
  refine spec_use (forLoop_exec (P := P) (a := 1711) (bR := 1701) (body := cpMarkBody) J2
    (K := 9) (n := lt) _ ‹_› (by config_simp) (by config_simp; exact q01) ?_
    (fun j d hj hw ha hb ⟨f, fm, fn, f10, f19, fr, frm, fo⟩ => by
      have e02 : d.nreg 1702 = ITb := (fn 1702 (by omega)).trans ((gn 1702 (by omega)).trans r02)
      have e03 : d.nreg 1703 = RVb := (fn 1703 (by omega)).trans ((gn 1703 (by omega)).trans r03)
      have e06 : d.nreg 1706 = Ob := (fn 1706 (by omega)).trans ((gn 1706 (by omega)).trans r06)
      have hitj : d.nmem (ITb + j) = c.nmem (ITb + j) := by
        rw [fm _ (by omega), gm _ (by omega)]
      have ha' := hit j hj
      have hrva : d.nmem (RVb + d.nmem (ITb + j)) = c.nmem (RVb + c.nmem (ITb + j)) := by
        rw [hitj, fm _ (by omega), gm _ (by omega)]
      have hb' := hrv _ ha'
      obtain ⟨d', k, ex, hk, hm, h11, hn, hr, hrm, ho⟩ := cpMarkBody_exec (P := P) (nD := nD)
        d hw e02 e03 e06 f10 ha f19 hj (by rw [hitj]; exact ha') (by rw [hrva]; exact hb') wI wR
        (by omega) (by rw [hitj]; omega)
      refine ⟨d', k, ex, by omega, h11, by
        rw [hn _ (by omega) (by omega) (by omega) (by omega)]; exact hb, ?_, ?_, ?_, ?_, ?_,
        by rw [hr, fr], by rw [hrm, frm], by rw [ho, fo]⟩
      · intro x hx
        rw [hm, hrva, hitj]
        by_cases hxe : x = c.nmem (ITb + j) ∨ x = c.nmem (RVb + c.nmem (ITb + j))
        · have hex : ∃ j' < j + 1, x = c.nmem (ITb + j') ∨
              x = c.nmem (RVb + c.nmem (ITb + j')) := ⟨j, by omega, hxe⟩
          simp only [hex, ↓reduceIte, upd_apply]
          rcases hxe with h | h
          · subst h; split_ifs <;> simp_all
          · subst h; simp
        · have hiff : (∃ j' < j + 1, x = c.nmem (ITb + j') ∨
              x = c.nmem (RVb + c.nmem (ITb + j'))) ↔ ∃ j' < j, x = c.nmem (ITb + j') ∨
              x = c.nmem (RVb + c.nmem (ITb + j')) := by
            constructor
            · rintro ⟨j', hj', h⟩
              rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
              · exact ⟨j', hj', h⟩
              · exact absurd h hxe
            · rintro ⟨j', hj', h⟩; exact ⟨j', by omega, h⟩
          obtain ⟨hx1, hx2⟩ := not_or.1 hxe
          simp only [upd_apply, show Ob + x ≠ Ob + c.nmem (ITb + j) by omega,
            show Ob + x ≠ Ob + c.nmem (RVb + c.nmem (ITb + j)) by omega, ↓reduceIte, hiff]
          exact f x hx
      · intro a ha''
        rw [hm, hrva, hitj]
        simp only [upd_apply, show a ≠ Ob + c.nmem (ITb + j) by omega,
          show a ≠ Ob + c.nmem (RVb + c.nmem (ITb + j)) by omega, ↓reduceIte]
        exact fm a ha''
      · intro r hr'
        rw [hn r (by omega) (by omega) (by omega) (by omega)]; exact fn r hr'
      · rw [hn _ (by omega) (by omega) (by omega) (by omega)]; exact f10
      · rw [hn _ (by omega) (by omega) (by omega) (by omega)]; exact f19)) ?_
  · refine ⟨fun x hx => ?_, fun _ _ => rfl, fun r hr => ?_, ?_, ?_, gr, grm, go⟩
    · have hn : ¬ ∃ j' < 0, x = c.nmem (ITb + j') ∨ x = c.nmem (RVb + c.nmem (ITb + j')) := by
        rintro ⟨j', hj', -⟩; omega
      simp only [hn, ↓reduceIte]
      exact (g x hx).1
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
    · config_simp; exact g10
    · config_simp; exact g19
  intro c₂ k₂ hk₂ hw₂ ⟨_, f, fm, fn, f10, f19, fr, frm, fo⟩
  refine ⟨by omega, f, fun x hx => ?_, fun x hx => ?_, fun a ha => ?_, fun r hr => ?_,
    fr, frm, fo⟩
  · rw [fm _ (by omega)]; exact (g x hx).2.1
  · rw [fm _ (by omega)]; exact (g x hx).2.2
  · rw [fm _ (by omega)]; exact gm a ha
  · rw [fn r (by omega)]; exact gn r hr

end NegSSSP

end PlanarFlow
