module

public import PlanarFlow.BKMNW.SmSegsC
public import PlanarFlow.BKMNW.SepPX2

/-!
# `sepPXS` meets `SepPSpecXS` (the separator with its parts)

`sepPXS s sepL = sepD0 s ; if (large) then sepL else sepSmS`: `sepPX` with the small branch
`sepSmS` (`sepSm` writing `SegsOut`).

* `SegsOut.mono`;
* **`sepPXS_spec`**: `sepL` meeting `SepPSpecXLS` ⟹ `sepPXS ds.s sepL` meets **`SepPSpecXS`**
  (steps `sT n k + 600 n + 70 k + 700`, room `sR n m k + smRS n m k`; proof of `sepPX_spec`);
* `sepPXLS_vacuous`, **`sepPXS_spec_small`**: for small pieces only, `sepPXS ds.s .skip` meets
  `SepPSpecXS` unconditionally (steps `600 n + 70 k + 700`, room `smRS n m k`).
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

/-- **The separator program with the parts of the small separator.** -/
def sepPXS (s : ℕ) (sepL : Stmt) : Stmt := .seq (sepD0 s) (.ifLtN 5611 5610 sepL sepSmS)

lemma SegsOut.mono {en : ℕ → D} {m : ℕ} {π : HSep M} {lo hi hi' Gb : ℕ} {mem : ℕ → ℕ}
    (h : SegsOut M en m π lo hi Gb mem) (hh : hi ≤ hi') : SegsOut M en m π lo hi' Gb mem :=
  ⟨h.1, h.2.1, h.2.2.1.trans hh, h.2.2.2⟩

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **`sepPXS` meets `SepPSpecXS`** (see the module docstring). -/
theorem sepPXS_spec {Reach : MCall M → Prop} {sepL : Stmt} {sT : ℕ → ℕ → ℕ}
    {sR : ℕ → ℕ → ℕ → ℕ} (hsL : SepPSpecXLS M ds Reach gid ν u S T Z I W sepL sT sR)
    (hpk : PkMin gid ds.pk) (hν : Injective ν) (hloop : ∀ y, M.head y ≠ M.tail y)
    (hsW : ds.s ≤ W) :
    SepPSpecXS M ds Reach gid ν u S T Z I W (sepPXS ds.s sepL)
      (fun n k => sT n k + 600 * n + 70 * k + 700) (fun n m k => sR n m k + smRS n m k) := by
  intro l r π Hs σ d e h Sb m en c hin hLy hc r4 r5 r3 r50 heh hhS hw
  obtain ⟨hR, hok, m', en', n, g, hL', hp1, hsz, hLR⟩ := id hin
  have hmm : m' = m := hL'.card.trans hLy.card.symm
  subst hmm
  have hf : fsz m' = 4 + 7 * m' := rfl
  have hsm0 : smRS (l.piece ∪ r.piece).card m' Hs.length =
      22 * m' + 24 * (l.piece ∪ r.piece).card + 8 * Hs.length + 30 + 2 * m' + 2 * Hs.length + 16 :=
    rfl
  have hw' : Sb + (sR (l.piece ∪ r.piece).card m' Hs.length +
      smRS (l.piece ∪ r.piece).card m' Hs.length) ≤ W := hw
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
  have hW1 : Sb + smRS n m' Hs.length ≤ W := by rw [hnc]; clear * - hw'; omega
  have hSb : Sb ≤ W := by clear * - hW1; unfold smRS smR at hW1; omega
  obtain ⟨c₁, t₁, e₁, ht₁, v10, v11, n1, m1, rr1, rm1, o1'⟩ := sepD0_exec (I := I) (s := ds.s) c hc
    r4 hLy.hm (by rw [show d + 7 * m' + 4 = d + fsz m' by omega]; exact hRdef) hRn rfl hph2
    (by clear * - hp1 o1 hSb hf; omega) (by clear * - o1 hSb; omega) hsW
    (by clear * - hW1; unfold smRS smR at hW1; omega)
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
    · show t₁ + (t₂ + 1) ≤ sT (l.piece ∪ r.piece).card Hs.length + 600 * (l.piece ∪ r.piece).card +
        70 * Hs.length + 700
      clear * - ht₁ ht₂; omega
    · rw [dk2 x h1 h2]; exact R1 x (by clear * - h2; omega)
    · rw [(mk2 a ha).1, (mk2 a ha).2, m1, rm1]; exact ⟨rfl, rfl⟩
    · show _ ≤ Sb + (sR (l.piece ∪ r.piece).card m' Hs.length +
        smRS (l.piece ∪ r.piece).card m' Hs.length)
      clear * -; omega
    · show _ ≤ Sb + (sR (l.piece ∪ r.piece).card m' Hs.length +
        smRS (l.piece ∪ r.piece).card m' Hs.length)
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
    obtain ⟨c₂, t₂, e₂, ht₂, dk2, mk2, oo2, s1, s2, s3, s4, s5, s6, hRO, hSO⟩ := sepSmS_exec
      (I := I) (ds := ds) c₁ e₁.wb_right hok hLy1 (by rw [m1]; exact hRdef) hp1
      (hA.congr fun a _ _ => by rw [m1]) (by rw [m1]; exact hRn) hsm hpk hν hloop
      ((R1 3004 (by decide)).trans r4) ((n1 6500 (Or.inr (by decide))).trans r50) o1 hW1
      (by clear * - hW1; unfold smRS smR at hW1; omega)
    refine ⟨c₂, _, .seq e₁ (.ifLtN_false (by rw [v10, v11]; exact hp) e₂), ?_,
      fun x h1 h2 => ?_, fun a ha => ?_, by rw [oo2, o1'], s1, s2, s3, s4, s5, s6,
      hRO.mono ?_, hSO.mono ?_⟩
    · show t₁ + (t₂ + 2) ≤ sT (l.piece ∪ r.piece).card Hs.length + 600 * (l.piece ∪ r.piece).card +
        70 * Hs.length + 700
      rw [← hnc]; clear * - ht₁ ht₂ hmn; omega
    · rw [dk2 x h1 h2]; exact R1 x (by clear * - h2; omega)
    · rw [(mk2 a ha).1, (mk2 a ha).2, m1, rm1]; exact ⟨rfl, rfl⟩
    · show _ ≤ Sb + (sR (l.piece ∪ r.piece).card m' Hs.length +
        smRS (l.piece ∪ r.piece).card m' Hs.length)
      rw [← hnc]; clear * -; omega
    · show _ ≤ Sb + (sR (l.piece ∪ r.piece).card m' Hs.length +
        smRS (l.piece ∪ r.piece).card m' Hs.length)
      rw [← hnc]; clear * -; omega

/-- **`SepPSpecXLS` holds vacuously when every call of `Reach` has at most `ds.s` darts.** -/
theorem sepPXLS_vacuous {Reach : MCall M → Prop} (hsmall : ∀ x, Reach x → x.1.piece.card ≤ ds.s)
    (sepL : Stmt) (sT : ℕ → ℕ → ℕ) (sR : ℕ → ℕ → ℕ → ℕ) :
    SepPSpecXLS M ds Reach gid ν u S T Z I W sepL sT sR := by
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

/-- **The separator program meets `SepPSpecXS` when every piece is small** (at most `ds.s` darts:
then every node call is a node of `smD`). -/
theorem sepPXS_spec_small {Reach : MCall M → Prop}
    (hsmall : ∀ x, Reach x → x.1.piece.card ≤ ds.s)
    (hpk : PkMin gid ds.pk) (hν : Injective ν) (hloop : ∀ y, M.head y ≠ M.tail y)
    (hsW : ds.s ≤ W) :
    SepPSpecXS M ds Reach gid ν u S T Z I W (sepPXS ds.s .skip)
      (fun n k => 0 + 600 * n + 70 * k + 700) (fun n m k => 0 + smRS n m k) :=
  sepPXS_spec (sepPXLS_vacuous hsmall .skip (fun _ _ => 0) (fun _ _ _ => 0)) hpk hν hloop hsW

end Exec

end MfDrv

end BKMNW

end PlanarFlow
