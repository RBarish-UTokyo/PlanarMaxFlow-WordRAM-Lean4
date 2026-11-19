module

public import PlanarFlow.BKMNW.S7B2

/-!
# Stage 7 of `sepL`: the outputs 1–4 of `SepPSpecX`, composed

**`s7 = s7a ; (odA ; odB) ; odC ; s7O1 ; s7G`**, **`s7_exec`**: from the record's arrays and the
path's flags (`S7In`, `DF`, `FX`), the certificate's facts on the classes (`HClosed` of the new
hole, `IsCls` of `clsF`, the weight bound `hw ≤ A` of every class, the disjoint hole sets of
distinct classes when `K ≠ 0`), within `600 n + 30 m + 70 k + 500` steps:

* the outputs 1–4 of `SepPSpecX` at `Sb`: `bf (en i ∈ l)`, `bf (en i ∈ ρ.darts)`,
  `bf (tail (en i) ∈ ρ.mverts)`, `bf (¬ Disjoint Hs[j] ρ.mverts)`, where
  `l = (twoGroupsL (hw M K Hs ρ.mverts) A (ordE eG N (P.image (clsF M P Nf Hs K ρ)))).toFinset
  .biUnion id` is the left piece of `splitOf`;
* over the record: `LF[i] = bf (g i ∈ l)` at `Z + 34 n + 8 k + 11` (and `g i` is in the right
  piece iff not in `l`), the hole flags at `Z + n + 1`;
* the memory outside the scratch `[Z, Z + 35 n + 8 k + 11)` and the outputs `[Sb, Sb + 3 m + k)`
  kept.
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

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- **Stage 7**: the split's flags and the outputs 1–4. -/
def s7 : Stmt := .seq s7a (.seq (.seq odA odB) (.seq odC (.seq s7O1 s7G)))

section Sem

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **Stage 7 of `sepL`** (see the module docstring). -/
theorem s7_exec {M : CombMap D V F} {Ps Nf : Finset D} {Hs : List (Finset V)} {K A : ℕ}
    {ρ : HPath M} {g en : ℕ → D} {gid : D → ℕ} {eG : ℕ → D} {N : ℕ} (c : Config)
    (hc : WordsBounded W c)
    {n k Z Sb m HPb VFb RPb VKb NFb FXb DFb : ℕ} {rp hp vk vf nf : ℕ → ℕ}
    (hI : S7In M Ps Hs ρ.mverts Nf g n rp hp vk vf nf) (hk : Hs.length = k)
    (hmono : ∀ i j, i < j → j < n → gid (g i) < gid (g j))
    (he : ∀ i < N, gid (eG i) = i) (hesurj : ∀ d, ∃ i < N, eG i = d)
    (hY : HClosed Hs (newHole Hs ρ.mverts)) (hC : IsCls Ps (clsF M Ps Nf Hs K ρ))
    (hNf : Nf ⊆ Ps)
    (hA : ∀ X ∈ Ps.image (clsF M Ps Nf Hs K ρ), hw M K Hs ρ.mverts X ≤ A)
    (htH : K ≠ 0 → ∀ d ∈ Ps, ∀ d' ∈ Ps, clsF M Ps Nf Hs K ρ d ≠ clsF M Ps Nf Hs K ρ d' →
      Disjoint (tH M Hs ρ.mverts (clsF M Ps Nf Hs K ρ d))
        (tH M Hs ρ.mverts (clsF M Ps Nf Hs K ρ d')))
    (hnt : K * nTouch M Ps Hs ≤ W) (hA3 : 3 * A ≤ W)
    (r00 : c.nreg 7100 = n) (r05 : c.nreg 7105 = k + 1) (r99 : c.nreg 7199 = Z)
    (r93 : c.nreg 7193 = Sb) (r30 : c.nreg 7130 = m) (r21 : c.nreg 6521 = 1)
    (r01 : c.nreg 7101 = HPb) (r02 : c.nreg 7102 = VFb) (r06 : c.nreg 7106 = RPb)
    (r09 : c.nreg 7109 = VKb) (r42 : c.nreg 7142 = NFb) (r43 : c.nreg 7143 = K)
    (r53 : c.nreg 7153 = A) (r31 : c.nreg 7131 = FXb) (r32 : c.nreg 7132 = DFb)
    (mHP : ∀ i < n, c.nmem (HPb + i) = hp i) (mVF : ∀ i < n, c.nmem (VFb + i) = vf i)
    (mRP : ∀ i < n, c.nmem (RPb + i) = rp i) (mVK : ∀ i < n, c.nmem (VKb + i) = vk i)
    (mNF : ∀ i < n, c.nmem (NFb + i) = nf i)
    (mDF : ∀ i < n, c.nmem (DFb + i) = bf (g i ∈ ρ.darts.toFinset))
    (mFX : ∀ i < m, c.nmem (FXb + i) < n ∧ g (c.nmem (FXb + i)) = en i)
    (lay : HPb + n ≤ Sb ∧ FXb + m ≤ Sb ∧ RPb + n ≤ Z ∧ Sb + 3 * m + k ≤ VFb ∧ VFb + n ≤ Z ∧
      Sb + 3 * m + k ≤ VKb ∧ VKb + n ≤ Z ∧ Sb + 3 * m + k ≤ NFb ∧ NFb + n ≤ Z ∧
      Sb + 3 * m + k ≤ DFb ∧ DFb + n ≤ Z ∧ Sb + 3 * m + k ≤ Z ∧ Z + 35 * n + 8 * k + 12 ≤ W)
    (hW : 9 * n + 3 * k + 6 ≤ W) (hWm : m + k + 1 ≤ W) :
    ∃ c' t, Exec P W s7 c c' t ∧ t ≤ 600 * n + 30 * m + 70 * k + 500 ∧
      (∀ i < m, c'.nmem (Sb + i) = bf (en i ∈ (twoGroupsL (hw M K Hs ρ.mverts) A
          (ordE eG N (Ps.image (clsF M Ps Nf Hs K ρ)))).toFinset.biUnion _root_.id)) ∧
      (∀ i < m, c'.nmem (Sb + m + i) = bf (en i ∈ ρ.darts.toFinset)) ∧
      (∀ i < m, c'.nmem (Sb + 2 * m + i) = bf (M.tail (en i) ∈ ρ.mverts)) ∧
      (∀ j < k, c'.nmem (Sb + 3 * m + j) = bf (¬ Disjoint (Hs.getD j ∅) ρ.mverts)) ∧
      (∀ i < n, c'.nmem (Z + 34 * n + 8 * k + 11 + i) = bf (g i ∈
        (twoGroupsL (hw M K Hs ρ.mverts) A
          (ordE eG N (Ps.image (clsF M Ps Nf Hs K ρ)))).toFinset.biUnion _root_.id)) ∧
      (∀ i < n, (g i ∈ (Ps.image (clsF M Ps Nf Hs K ρ) \ (twoGroupsL (hw M K Hs ρ.mverts) A
          (ordE eG N (Ps.image (clsF M Ps Nf Hs K ρ)))).toFinset).biUnion _root_.id ↔
        g i ∉ (twoGroupsL (hw M K Hs ρ.mverts) A
          (ordE eG N (Ps.image (clsF M Ps Nf Hs K ρ)))).toFinset.biUnion _root_.id)) ∧
      (∀ j < k, c'.nmem (Z + n + 1 + j) = bf (¬ Disjoint (Hs.getD j ∅) ρ.mverts)) ∧
      (∀ a, ¬ (Z ≤ a ∧ a < Z + 35 * n + 8 * k + 11) → ¬ (Sb ≤ a ∧ a < Sb + 3 * m + k) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4000 ∨ (4013 < x ∧ x < 4400) ∨ (4467 < x ∧ x < 4630) ∨
        (4639 < x ∧ x < 4910) ∨ (4916 < x ∧ x < 6030) ∨ (6035 < x ∧ x < 6210) ∨
        (6217 < x ∧ x < 6300) ∨ (6309 < x ∧ x < 6520) ∨ x = 6521 ∨ (6529 < x ∧ x < 7100) ∨
        7199 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13⟩ := lay
  have hd := hI.hd
  unfold s7
  -- stage 7 (I)
  obtain ⟨c₁, t₁, e₁, ht₁, R1, HT0, HTj, ID1, IDlt, fm1, fn1, fr1, frm1, fo1⟩ :=
    s7a_exec (P := P) (K := K) c hc hI hk hY hC hNf r00 r05 r99 r93 r30 r21 r01 r02 r06 r09 r42
      r43 mHP mVF mRP mVK mNF ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩ hW
      (by omega)
  have q1 : ∀ x, (x = 7101 ∨ x = 7143 ∨ x = 7153 ∨ x = 7131 ∨ x = 7132 ∨ x = 7102) →
      c₁.nreg x = c.nreg x := fun x hx => fn1 x (by omega)
  -- positions and weights
  obtain ⟨c₂, t₂, e₂, ht₂, lst, hOd, RB, mP1, mWT, fm2, fn2, fr2, frm2, fo2⟩ :=
    s7bAB_exec (P := P) (A := A) c₁ e₁.wb_right hI.mem hI.surj hI.inj hd hI.hp hk hC hA htH hnt
      (by omega) R1 ((q1 _ (by omega)).trans r01) ((q1 _ (by omega)).trans r43)
      (fun i hi => by rw [fm1 _ (by omega)]; exact mHP i hi) HT0 HTj ID1 IDlt
      ⟨by omega, l13⟩
  have q2 : ∀ x, (x = 7153 ∨ x = 7131 ∨ x = 7132 ∨ x = 7102 ∨ (7130 ≤ x ∧ x ≤ 7137) ∨
      x = 7193 ∨ x = 7100) → c₂.nreg x = c₁.nreg x := fun x hx => fn2 x (by omega)
  have hwA : ∀ q < odM lst n, hw M K Hs ρ.mverts (odL g n lst q) ≤ A := fun q hq => by
    obtain ⟨i, hi, e, -⟩ := hOd.odL_surj hq
    rw [← e, hOd.odL_pos hi]
    exact hA _ (mem_image_of_mem _ (hI.mem i hi))
  -- the left piece
  obtain ⟨c₃, t₃, e₃, ht₃, LF3, RP3, fm3, fn3, fr3, frm3, fo3⟩ :=
    s7bC_exec (P := P) (eG := eG) (N := N) c₂ e₂.wb_right hOd hmono he hesurj RB
      ((q2 _ (by omega)).trans ((q1 _ (by omega)).trans r53)) mP1 mWT hwA hA3 l13
  have q3 : ∀ x, ((7130 ≤ x ∧ x ≤ 7137) ∨ x = 7193 ∨ x = 7100 ∨ x = 7102 ∨ x = 7186) →
      c₃.nreg x = c₂.nreg x := fun x hx => fn3 x (by omega)
  have M3 : ∀ a, a < Z → c₃.nmem a = c.nmem a := fun a ha => by
    rw [fm3 a (by omega), fm2 a (by omega), fm1 a (by omega)]
  have M3' : ∀ a, (Sb ≤ a ∧ a < Sb + 3 * m + k) → c₃.nmem a = c.nmem a := fun a ha => M3 a
    (by omega)
  -- output 1
  obtain ⟨c₄, t₄, e₄, ht₄, O1, fm4, fn4, fr4, frm4, fo4⟩ := s7O1_exec (P := P) c₃ e₃.wb_right
    (m := m) (n := n) (FXb := FXb) (WTb := Z + 33 * n + 8 * k + 11) (Sb := Sb)
    ((q3 _ (by omega)).trans ((q2 _ (by omega)).trans R1.r30))
    ((q3 _ (by omega)).trans ((q2 _ (by omega)).trans ((q1 _ (by omega)).trans r31)))
    ((q3 _ (by omega)).trans (RB.r86.trans (by ring))) ((q3 _ (by omega)).trans RB.r00)
    ((q3 _ (by omega)).trans ((q2 _ (by omega)).trans R1.r93))
    (fun i hi => by rw [M3 _ (by omega)]; exact (mFX i hi).1) ⟨l2, by omega, by omega⟩ (by omega)
  have q4 : ∀ x, ((7130 ≤ x ∧ x ≤ 7137) ∨ x = 7102) → c₄.nreg x = c₂.nreg x := fun x hx => by
    rw [fn4 x (by omega) (by omega), q3 x (by omega)]
  have M4 : ∀ a, (a < Sb ∨ Sb + m ≤ a) → a < Z → c₄.nmem a = c.nmem a := fun a h1 h2 => by
    rw [fm4 a (by omega), M3 a h2]
  -- outputs 2–4
  obtain ⟨c₅, t₅, e₅, ht₅, O2, O3, O4, fm5, fn5, fr5, frm5, fo5⟩ := s7G_exec' (P := P) c₄
    e₄.wb_right (m := m) (k := k) (FXb := FXb) (DFb := DFb) (VFb := VFb) (HTb := Z + n) (Sb := Sb)
    (n := n) ((q4 _ (by omega)).trans ((q2 _ (by omega)).trans R1.r30))
    ((q4 _ (by omega)).trans ((q2 _ (by omega)).trans ((q1 _ (by omega)).trans r31)))
    ((q4 _ (by omega)).trans ((q2 _ (by omega)).trans ((q1 _ (by omega)).trans r32)))
    ((q4 _ (by omega)).trans ((q2 _ (by omega)).trans ((q1 _ (by omega)).trans r02)))
    ((q4 _ (by omega)).trans ((q2 _ (by omega)).trans R1.r33)) ((q4 _ (by omega)).trans ((q2 _ (by omega)).trans R1.r34))
    ((q4 _ (by omega)).trans ((q2 _ (by omega)).trans R1.r35)) ((q4 _ (by omega)).trans ((q2 _ (by omega)).trans R1.r36))
    ((q4 _ (by omega)).trans ((q2 _ (by omega)).trans R1.r37)) (fun i hi => by rw [M4 _ (by omega) (by omega)]; exact (mFX i hi).1)
    ⟨l2, by omega, by omega, by omega, by omega, by omega, by omega⟩ hWm
  have FX4 : ∀ i < m, c₄.nmem (FXb + i) = c.nmem (FXb + i) := fun i hi =>
    M4 _ (by omega) (by omega)
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), by omega, fun i hi => ?_,
    fun i hi => ?_, fun i hi => ?_, fun j hj => ?_, fun i hi => ?_, RP3, fun j hj => ?_,
    fun a h1 h2 => ?_, fun x hx => ?_, by rw [fr5, fr4, fr3, fr2, fr1],
    by rw [frm5, frm4, frm3, frm2, frm1], by rw [fo5, fo4, fo3, fo2, fo1]⟩
  · obtain ⟨hx, hg⟩ := mFX i hi
    rw [fm5 _ (by omega), O1 i hi, M3 (FXb + i) (by omega),
      show Z + 33 * n + 8 * k + 11 + n + c.nmem (FXb + i) =
        Z + 34 * n + 8 * k + 11 + c.nmem (FXb + i) by ring, LF3 _ hx, hg]
  · obtain ⟨hx, hg⟩ := mFX i hi
    rw [O2 i hi, FX4 i hi, M4 _ (by omega) (by omega), mDF _ hx, hg]
  · obtain ⟨hx, hg⟩ := mFX i hi
    rw [O3 i hi, FX4 i hi, M4 _ (by omega) (by omega), mVF _ hx, hI.vf _ hx, hg]
  · rw [O4 j hj, fm4 _ (by omega), fm3 _ (by omega), fm2 _ (by omega)]; exact HTj j hj
  · rw [fm5 _ (by omega), fm4 _ (by omega)]; exact LF3 i hi
  · rw [fm5 _ (by omega), fm4 _ (by omega), fm3 _ (by omega), fm2 _ (by omega)]; exact HTj j hj
  · rw [fm5 a (by omega), fm4 a (by omega), fm3 a (by omega), fm2 a (by omega),
      fm1 a (by omega)]
  · rw [fn5 x (by omega), fn4 x (by omega) (by omega), fn3 x (by omega), fn2 x (by omega),
      fn1 x (by omega)]

end Sem

end MfDrv

end BKMNW

end PlanarFlow
