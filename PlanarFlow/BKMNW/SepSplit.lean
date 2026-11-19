module

public import PlanarFlow.BKMNW.SepKids

/-!
# The extended split meets its field of `MfSpecR`

**`splitSX sepP`** = `splitS sepP` with the last block `spFin` replaced by the copy phase `spRec`
(`SepRec.lean`): `spFront sepP ; spChL ; spGlR ; sfChild ; spRec`. The left child's frame is
`[h + 5, el)` with its record where the separator program wrote it, the right child's frame
`[el + 5, er)` copied above the children's records with its record after it.

* `rSpX sR x` (the room: `rSp` with `sR n m k`, plus `7 m + 20 + rszC (chR x)` for the copied
  right child), `scpX sT x` (the steps: `sT n k + 542 m + 21 k + 670 + 7 rszC (chR x)`), with
  `n = #piece`, `m = #pdarts`, `k = #Hs`;
* `finLX_of_recAt` (a frame with a pointer to a record `RecAt` is an extended frame);
* **`mfSplit_specX`**: for a separator program meeting `SepPSpecX` and `Reach` closed under the
  children, `splitSX sepP` meets the field `split` of `MfSpecR` for the frame predicates
  `FInLX ds Reach` (`G = True`), room `rSpX sR`, steps `scpX sT`.
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

/-- **The extended split around the separator program `sepP`.** -/
def splitSX (sepP : Stmt) : Stmt :=
  .seq (spFront sepP) (.seq spChL (.seq spGlR (.seq sfChild spRec)))

variable (M) in
/-- The room of the extended split at a node call. -/
noncomputable def rSpX (sR : ℕ → ℕ → ℕ → ℕ) : MCall M → ℕ
  | (.node l r π, Hs, σ) => 18 + 14 * (pdarts M (l.piece ∪ r.piece) Hs).card +
      sR (l.piece ∪ r.piece).card (pdarts M (l.piece ∪ r.piece) Hs).card Hs.length +
      21 * (pdarts M (l.piece ∪ r.piece) Hs).card + 4 * Hs.length + 2 +
      7 * (pdarts M (l.piece ∪ r.piece) Hs).card + 20 + rszC M (chR M l r π Hs σ)
  | (.leaf _, _, _) => 0

variable (M) in
/-- The steps of the extended split at a node call. -/
noncomputable def scpX (sT : ℕ → ℕ → ℕ) : MCall M → ℕ
  | (.node l r π, Hs, σ) => sT (l.piece ∪ r.piece).card Hs.length +
      542 * (pdarts M (l.piece ∪ r.piece) Hs).card + 21 * Hs.length + 670 +
      7 * rszC M (chR M l r π Hs σ)
  | (.leaf _, _, _) => 0

/-- **A frame with a pointer to a record is an extended frame.** -/
lemma finLX_of_recAt {Reach : MCall M → Prop} {x : MCall M} {m : ℕ} {en : ℕ → D} {d e R z : ℕ}
    {c : Config} (hR : Reach x) (hok : CallOk M S T x) (hL : Lay M gid u S T Z x m en d c.nmem)
    (hp : c.nmem (d + fsz m) = R) (h1 : d + fsz m < R) (h2 : R + z ≤ e)
    (hrec : RecAt M ds gid ν S T x R z c.nmem) : FInLX M ds Reach gid ν u S T Z x d e c := by
  obtain ⟨-, n, g, hz, hLR⟩ := hrec
  have hm := hL.card
  subst hm
  refine ⟨hR, hok, _, en, n, g, hL, by rw [hp]; exact h1, ?_, by rw [hp]; exact hLR⟩
  rw [hp, ← hz]; exact h2

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The extended split meets the field `split` of `MfSpecR`** (see the module docstring). -/
theorem mfSplit_specX {Reach : MCall M → Prop} {sepP : Stmt} {sT : ℕ → ℕ → ℕ}
    {sR : ℕ → ℕ → ℕ → ℕ}
    (hsep : SepPSpecX M ds Reach gid ν u S T Z I W sepP sT sR)
    (hReach : ∀ l r π Hs σ, Reach ((.node l r π, Hs, σ) : MCall M) →
      Reach (chL M l r π Hs σ) ∧ Reach (chR M l r π Hs σ)) {Hb : ℕ} :
    ∀ l r π Hs σ d e h c, True → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → h + rSpX M sR (.node l r π, Hs, σ) ≤ W →
    FInLX M ds Reach gid ν u S T Z (.node l r π, Hs, σ) d e c →
    ∃ c' t el er, Exec I W (splitSX sepP) c c' t ∧ t ≤ scpX M sT (.node l r π, Hs, σ) ∧ True ∧
      DRegKeep c c' ∧ HeapKeep Hb h h h c c' ∧ c'.output = c.output ∧ c'.nreg 2998 = el ∧
      c'.nreg 2999 = er ∧ h + 5 ≤ el ∧ el + 5 ≤ er ∧ er ≤ h + rSpX M sR (.node l r π, Hs, σ) ∧
      FInLX M ds Reach gid ν u S T Z (chL M l r π Hs σ) (h + 5) el c' ∧
      FInLX M ds Reach gid ν u S T Z (chR M l r π Hs σ) (el + 5) er c' := by
  intro l r π Hs σ d e h c _ hc r4 r5 r3 hd1 hde heh hroom hin
  have hin0 := hin
  obtain ⟨hR, hok, m, en, n0, g0, hL, hpt, hsz, -⟩ := hin0
  have hfs : d + fsz m ≤ e := by
    have := three_le_rszL (c.nmem (c.nmem (d + fsz m) + 1)) n0 m; omega
  have hm : m = (pdarts M (l.piece ∪ r.piece) Hs).card := hL.card
  set zR := rszC M (chR M l r π Hs σ) with hzR
  have hroom' : h + 18 + 14 * m + sR (l.piece ∪ r.piece).card m Hs.length + 21 * m +
      4 * Hs.length + 2 + 7 * m + 20 + zR ≤ W := by
    dsimp only [rSpX] at hroom; rw [← hm] at hroom; omega
  obtain ⟨hRl, hRr⟩ := hReach l r π Hs σ hR
  obtain ⟨c₁, c₃, c₄, c₅, t₁, t₃, t₄, t₅, e₁, e₃, e₄, e₅, ht, mcl, mcr, ixl, ixr, hmcl, hmcr,
    el_def, hLl, hLr, hRO, dk5, mk5, o5⟩ := spKids_execX hsep c hc r4 r5 r3 heh hin hL hfs
    (by omega)
  set Xb := c₅.nreg 6501 with hXb
  set zl := c₅.nmem Xb with hzl
  set zr := c₅.nmem (Xb + 1) with hzr
  obtain ⟨hX1, hX2, hRecL, hRecR⟩ := hRO
  have hzR3 : 3 ≤ zr := by
    obtain ⟨-, nr, gr', hz, -⟩ := hRecR; exact le_of_le_of_eq (three_le_rszL _ _ _) hz.symm
  have hzr' : zr ≤ zR := hRecR.1
  have hmr : c₅.nmem (h + 5 + 4 + 7 * mcl + 5) = mcr := hLr.hm
  have T1 : h + 18 + 14 * m + 21 * m + 4 * Hs.length + 2 ≤ Xb := hX1
  have T2 : h + 5 + 4 + 7 * mcl + 9 + 6 * mcr ≤ Xb := by omega
  have T3 : Xb + 2 + zl + zr ≤ h + 18 + 14 * m + sR (l.piece ∪ r.piece).card m Hs.length := hX2
  have T4 : Xb + 2 + zl + zr + 10 + 7 * mcr + zr ≤ W := by omega
  -- the copy phase
  obtain ⟨c₆, t₆, e₆, ht₆, f98, f99, p6l, cpL, p6r, cpR, k6, n6, rr6, rm6, o6⟩ :=
    spRec_exec (I := I) c₅ e₅.wb_right rfl el_def rfl rfl hmr T2 T4
  set el := h + 5 + 4 + 7 * mcl with hel
  set elF := Xb + 2 + zl + zr with helF
  set erF := Xb + 2 + zl + zr + 10 + 7 * mcr + zr with herF
  have hLl6 : Lay M gid u S T Z (chL M l r π Hs σ) mcl (fun k => en (ixl k)) (h + 5) c₆.nmem :=
    hLl.congr fun a h1 h2 => k6 a (by omega) (by omega)
  have hLr6 : Lay M gid u S T Z (chR M l r π Hs σ) mcr (fun k => en (ixr k)) (elF + 5) c₆.nmem :=
    hLr.shift fun a ha => cpL a ha
  have hRL6 : RecAt M ds gid ν S T (chL M l r π Hs σ) (Xb + 2) zl c₆.nmem :=
    hRecL.congr fun a h1 h2 => k6 a (by omega) (by omega)
  have hRR6 : RecAt M ds gid ν S T (chR M l r π Hs σ) (elF + 5 + 5 + 7 * mcr) zr c₆.nmem :=
    hRecR.shift fun a ha => cpR a ha
  refine ⟨c₆, _, elF, erF,
    .seq e₁ (.seq e₃ (.seq e₄ (.seq e₅ e₆))), ?_, trivial, fun x h1 h2 => ?_,
    fun a h1 h2 _ => ?_, by rw [o6, o5], f98, f99, by omega, by omega, ?_, ?_, ?_⟩
  · have T6 : t₆ ≤ 42 * mcr + 7 * zr + 70 := ht₆
    have T7 : zr ≤ rszC M (chR M l r π Hs σ) := hRecR.1
    have T8 : t₁ + t₃ + t₄ + t₅ ≤ sT (l.piece ∪ r.piece).card Hs.length + 497 * m + 21 * Hs.length + 540 :=
      ht
    dsimp only [scpX]; rw [← hm]; omega
  · rw [n6 x (by omega) (by omega) (by omega)]
    exact dk5 x h1 h2
  · have k1 := mk5 a h2
    refine ⟨?_, ?_⟩
    · rw [k6 a (by omega) (by omega), k1.1]
    · rw [rm6, k1.2]
  · dsimp only [rSpX]; rw [← hm]; omega
  · refine finLX_of_recAt hRl hin.2.1.chL hLl6 ?_ (by unfold fsz; omega) (by omega) hRL6
    have : h + 5 + fsz mcl = el := by unfold fsz; omega
    rw [this]; exact p6l
  · refine finLX_of_recAt hRr hin.2.1.chR hLr6 ?_ (by unfold fsz; omega) (by omega) hRR6
    have : elF + 5 + fsz mcr = elF + 5 + 4 + 7 * mcr := by unfold fsz; omega
    rw [this]; exact p6r

end Exec

end MfDrv

end BKMNW

end PlanarFlow
