module

public import PlanarFlow.BKMNW.S7A

/-!
# Stage 7 of `sepL` composed (II): positions, weights, the left piece, the outputs 1–4

After `s7a` (`S7Regs`, the class numbers `ID` at `Z + 15 n + 2 k + 4`, the hole flags at `Z + n`):

* **`s7bAB_exec`** (`odA ; odB`): there is `lst` with `OdIn P (clsF …) g n ID lst`, the positions
  `P1[i] = odPos lst i + 1` at `P1b = Z + 30 n + 5 k + 7`, and the weights
  `WT[q] = hw M K Hs C (odL g n lst q)` at `WTb = Z + 33 n + 8 k + 11` (`q < odM lst n`);
* **`s7bC_exec`** (`odC`): the flags `LF[i] = bf (g i ∈ l)` at `LFb = Z + 34 n + 8 k + 11`, `l` the
  first group of `twoGroupsL (hw M K Hs C) A (ordE eG N (P.image (clsF …)))` — the left piece of
  `splitOf`;
* `s7G_exec'` (the gathers of `SepPSpecX`'s outputs 2–4 with the inputs above the outputs).
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

section Sem

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **Positions and weights of the classes** (`odA ; odB` after `s7a`). -/
theorem s7bAB_exec {M : CombMap D V F} {Ps Nf : Finset D} {Hs : List (Finset V)} {K A : ℕ}
    {ρ : HPath M} {g : ℕ → D} (c : Config) (hc : WordsBounded W c)
    {n k Z Sb m HPb : ℕ} {hp : ℕ → ℕ}
    (hmem : ∀ i < n, g i ∈ Ps) (hsurj : ∀ d ∈ Ps, ∃ i < n, g i = d)
    (hinj : ∀ i < n, ∀ j < n, g i = g j → i = j) (hd : Hs.Pairwise Disjoint)
    (hhp : ∀ i < n, hp i = hlab Hs (M.tail (g i))) (hk : Hs.length = k)
    (hC : IsCls Ps (clsF M Ps Nf Hs K ρ))
    (hA : ∀ X ∈ Ps.image (clsF M Ps Nf Hs K ρ), hw M K Hs ρ.mverts X ≤ A)
    (htH : K ≠ 0 → ∀ d ∈ Ps, ∀ d' ∈ Ps, clsF M Ps Nf Hs K ρ d ≠ clsF M Ps Nf Hs K ρ d' →
      Disjoint (tH M Hs ρ.mverts (clsF M Ps Nf Hs K ρ d))
        (tH M Hs ρ.mverts (clsF M Ps Nf Hs K ρ d')))
    (hnt : K * nTouch M Ps Hs ≤ W) (hAW : A ≤ W)
    (R : S7Regs c n k Z Sb m) (r01 : c.nreg 7101 = HPb) (r43 : c.nreg 7143 = K)
    (mHP : ∀ i < n, c.nmem (HPb + i) = hp i)
    (mHT0 : c.nmem (Z + n) = 0)
    (mHT : ∀ j < k, c.nmem (Z + n + 1 + j) = bf (¬ Disjoint (Hs.getD j ∅) ρ.mverts))
    (mID : ∀ i < n, ∀ j < n, (c.nmem (Z + 15 * n + 2 * k + 4 + i) =
      c.nmem (Z + 15 * n + 2 * k + 4 + j) ↔ g j ∈ clsF M Ps Nf Hs K ρ (g i)))
    (mIDlt : ∀ i < n, c.nmem (Z + 15 * n + 2 * k + 4 + i) < 3 * (2 * n + (n + k + 1)))
    (lay : HPb + n ≤ Z ∧ Z + 35 * n + 8 * k + 12 ≤ W) :
    ∃ c' t, Exec P W (.seq odA odB) c c' t ∧ t ≤ 115 * n + 40 * k + 130 ∧
      ∃ lst : ℕ → ℕ, OdIn Ps (clsF M Ps Nf Hs K ρ) g n
          (fun i => c.nmem (Z + 15 * n + 2 * k + 4 + i)) lst ∧
        OdRegsB c' n k HPb (Z + n) K (Z + 30 * n + 5 * k + 7) (odM lst n) ∧
        (∀ i < n, c'.nmem (Z + 30 * n + 5 * k + 7 + i) = odPos lst i + 1) ∧
        (∀ q < odM lst n, c'.nmem (Z + 33 * n + 8 * k + 11 + q) =
          hw M K Hs ρ.mverts (odL g n lst q)) ∧
        (∀ a, (a < Z + 16 * n + 2 * k + 4 ∨ Z + 34 * n + 8 * k + 11 ≤ a) →
          c'.nmem a = c.nmem a) ∧
        (∀ x, (x < 4630 ∨ (4639 < x ∧ x < 6300) ∨ (6309 < x ∧ x < 6520) ∨ x = 6521 ∨
          (6529 < x ∧ x < 7154) ∨ (7167 < x ∧ x < 7170) ∨ (7174 < x ∧ x < 7176) ∨
          (7189 < x)) → c'.nreg x = c.nreg x) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2⟩ := lay
  obtain ⟨c₁, t₁, e₁, ht₁, RA, lst, hLS, hlst, hP1, h06, fm1, fn1, fr1, frm1, fo1⟩ :=
    odA_exec (P := P) c hc (n := n) (nI := 3 * (2 * n + (n + k + 1)))
      (Ob := Z + 16 * n + 2 * k + 4) (IDb := Z + 15 * n + 2 * k + 4) R.r00 R.r50 R.r51 R.r52
      R.r21 mIDlt ⟨by omega, by omega⟩ (by omega)
  have hOd : OdIn Ps (clsF M Ps Nf Hs K ρ) g n
      (fun i => c.nmem (Z + 15 * n + 2 * k + 4 + i)) lst :=
    ⟨hC, hmem, hsurj, hinj, mID, fun i hi => (hlst i hi).1, fun i hi => (hlst i hi).2.1,
      fun i hi j hj e => (hlst i hi).2.2 j hj e⟩
  have hmC : odM lst n ≤ n := cnt_le _ _
  have hpos : ∀ i < n, odPos lst i + 1 ≤ n := fun i hi => by
    have := hOd.odPos_lt hi; omega
  -- the weights
  have q1 : ∀ x, (x = 7101 ∨ x = 7104 ∨ x = 7105 ∨ x = 7143 ∨ x = 6521 ∨ x = 7100) →
      c₁.nreg x = c.nreg x := fun x hx => fn1 x (by omega)
  set ht : ℕ → ℕ := fun h => c.nmem (Z + n + h) with hht
  have ht_j : ∀ j < k, ht (j + 1) = bf (¬ Disjoint (Hs.getD j ∅) ρ.mverts) := fun j hj => by
    simp only [hht]; rw [show Z + n + (j + 1) = Z + n + 1 + j by omega]; exact mHT j hj
  have hhtz : ∀ j < Hs.length, (ht (j + 1) = 0 ↔ Disjoint (Hs.getD j ∅) ρ.mverts) :=
    fun j hj => by rw [ht_j j (by omega)]; unfold bf; split_ifs with h <;> simp_all
  have hwq : ∀ q < odM lst n, ((range n).filter fun i => odPos lst i + 1 = q + 1).card +
      saF (fun j => svF hp (fun i => odPos lst i + 1) n (j + 1) 0)
        (fun j => vhV K (ht (j + 1)) (svF hp (fun i => odPos lst i + 1) n (j + 1) 0)) k (q + 1)
        = hw M K Hs ρ.mverts (odL g n lst q) := fun q hq => by
    rw [← hk]; exact od_wt_sem hOd hd htH hhp hhtz q
  have hwA : ∀ q < odM lst n, hw M K Hs ρ.mverts (odL g n lst q) ≤ A := fun q hq => by
    obtain ⟨i, hi, e, -⟩ := hOd.odL_surj hq
    rw [← e, hOd.odL_pos hi]
    exact hA _ (mem_image_of_mem _ (hmem i hi))
  obtain ⟨c₂, t₂, e₂, ht₂, RB, WT, fm2, fn2, fr2, frm2, fo2⟩ := odB_exec (P := P) c₁ e₁.wb_right
    (n := n) (k := k) (HPb := HPb) (HTb := Z + n) (K := K) (P1b := Z + 30 * n + 5 * k + 7)
    (mC := odM lst n) (p1 := fun i => odPos lst i + 1) (hp := hp) (ht := ht)
    RA.r00 ((q1 _ (by omega)).trans r01) ((q1 _ (by omega)).trans R.r04)
    ((q1 _ (by omega)).trans R.r05) ((q1 _ (by omega)).trans r43)
    (by rw [RA.r80]; ring_nf) h06 RA.r21
    (fun i hi => by rw [show Z + 30 * n + 5 * k + 7 + i =
      Z + 16 * n + 2 * k + 4 + 5 * n + 3 * (2 * n + (n + k + 1)) + i by ring]; exact hP1 i hi)
    (fun i hi => by rw [fm1 _ (by omega)]; exact mHP i hi)
    (fun h hh => by rw [fm1 _ (by omega)])
    hpos (fun i hi => by rw [hhp i hi, ← hk]; exact hlab_le _ _)
    (fun h hh => by
      rcases Nat.eq_zero_or_pos h with rfl | hp'
      · simp only [hht, add_zero, mHT0]; omega
      · obtain ⟨j, rfl⟩ : ∃ j, h = j + 1 := ⟨h - 1, by omega⟩
        rw [ht_j j (by omega)]; exact bf_le_one7 _) hmC
    (by
      have := od_hsum (M := M) (P := Ps) (g := g) (n := n) hd (K := K) (hp := hp)
        (p1 := fun i => odPos lst i + 1) (ht := ht) hmem hhp
      rw [hk] at this; omega)
    (fun q hq => by rw [hwq q hq]; have := hwA q hq; omega)
    ⟨by omega, by omega, by omega⟩
  refine ⟨c₂, _, .seq e₁ e₂, by omega, lst, hOd, RB, fun i hi => ?_, fun q hq => ?_,
    fun a ha => ?_, fun x hx => ?_, by rw [fr2, fr1], by rw [frm2, frm1], by rw [fo2, fo1]⟩
  · rw [fm2 _ (by omega), show Z + 30 * n + 5 * k + 7 + i =
      Z + 16 * n + 2 * k + 4 + 5 * n + 3 * (2 * n + (n + k + 1)) + i by ring]
    exact hP1 i hi
  · rw [show Z + 33 * n + 8 * k + 11 + q = Z + 30 * n + 5 * k + 7 + 3 * n + 3 * k + 4 + q by
      ring, WT q hq]
    exact hwq q hq
  · rw [fm2 a (by omega), fm1 a (by omega)]
  · rw [fn2 x (by omega), fn1 x (by omega)]

end Sem

end MfDrv

end BKMNW

end PlanarFlow
