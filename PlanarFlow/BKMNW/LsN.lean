module

public import PlanarFlow.BKMNW.LsM

/-!
# `sepL`, second half: `ls8 ; ls9 ; ls10`

**`lsHalf2_exec`**: `ls8_exec`, `ls9_exec`, `ls10_exec` in a row: from the scratch flags and the
path left by the first half, the outputs 1–4, the tags, `RecsOut` and `SegsOut'` of
`SepPSpecXLS'` (bounded by any `hi ≥ E + 4 n + 3`); memory below `Sb` and registers
`3000 … 3012` kept.
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

variable {gid : D → ℕ} {ν : V → ℕ} {S T : Finset V} {ds : DSys M}

/-- The second half of `sepL`. -/
def lsH2 : Stmt := .seq ls8 (.seq ls9 ls10)

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 8000000 in
/-- **The second half of `sepL`** (see the module docstring). -/
theorem lsHalf2_exec (c : Config) (hc : WordsBounded W c) {l r : ADec M} {π : HSep M}
    {Hs : List (Finset V)} {σ st : Perm D} {g en : ℕ → D} {d m k R n Sb U hi : ℕ}
    (hR : LsR c m k R n Sb) (hL : LsL c n k U) (hU : U = Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3)
    (r4 : c.nreg 3004 = d) (hm : c.nmem d = m)
    (hk : c.nmem (d + 1) = k) (hRm : c.nmem (d + 7 * m + 4) = R) (hn : c.nmem R = n)
    (o1 : R + 3 + 6 * n + m ≤ Sb) (o2 : d + 7 * m + 4 < R)
    (w : U + 55 * n + 9 * k + 17 ≤ W) (w2 : 100 ≤ W) (hhi : U ≤ hi)
    (arr : RArr M gid ν S T (.node l r π, Hs, σ) m n R g c.nmem)
    (hk' : Hs.length = k) (pw : Hs.Pairwise Disjoint)
    (hSC : Disjoint S π.path.mverts) (hTC : Disjoint T π.path.mverts)
    (hSA : Disjoint S (hunion Hs))
    (stab : Stable st (pdarts M (core M ds.Q (l.piece ∪ r.piece)) Hs))
    (sp : ∀ i < n, g i ∈ pdarts M (core M ds.Q (l.piece ∪ r.piece)) Hs →
      c.nmem (R + 3 + 5 * n + i) < n ∧ g (c.nmem (R + 3 + 5 * n + i)) = st (g i))
    (hLF : ∀ i < n, c.nmem (U + 44 * n + 9 * k + 14 + i) = bf (g i ∈ l.piece))
    (hVF : ∀ i < n, c.nmem (U + 5 * n + k + 3 + i) = bf (M.tail (g i) ∈ π.path.mverts))
    (hHM : ∀ j < k, c.nmem (U + 11 * n + k + 4 + j) =
      bf (¬ Disjoint (Hs.getD j ∅) π.path.mverts))
    (hDF : ∀ i < n, c.nmem (U + 4 * n + k + 2 + i) = bf (g i ∈ π.path.darts.toFinset))
    (hCC : ∀ i < n, c.nmem (U + 45 * n + 9 * k + 15 + i) =
      bf (g i ∈ pdarts M (core M ds.Q (l.piece ∪ r.piece)) Hs))
    (hlr : ∀ i < n, g i ∈ r.piece ↔ g i ∉ l.piece)
    (hlrev : ∀ d ∈ l.piece, M.rev d ∈ l.piece) (hrrev : ∀ d ∈ r.piece, M.rev d ∈ r.piece)
    (hl : l = ds.dec S T l.piece (childHoles Hs π.path.mverts)
      (childRot M st (pdarts M (core M ds.Q (l.piece ∪ r.piece)) Hs) π.path.darts
        (pdarts M (core M ds.Q l.piece) (childHoles Hs π.path.mverts)))
        (decide (1 - c.nreg 8559 = 1)))
    (hr : r = ds.dec S T r.piece (childHoles Hs π.path.mverts)
      (childRot M st (pdarts M (core M ds.Q (l.piece ∪ r.piece)) Hs) π.path.darts
        (pdarts M (core M ds.Q r.piece) (childHoles Hs π.path.mverts)))
        (decide (1 - c.nreg 8559 = 1)))
    (hν : Injective ν) (hpk : PkMin gid ds.pk) (hloop : ∀ d, M.head d ≠ M.tail d)
    (hs : ds.s = 100000) (hsW : 100000 ≤ W) (hlargeL : ds.s < l.piece.card → ntag l = 1)
    (hlargeR : ds.s < r.piece.card → ntag r = 1)
    (hFX : ∀ i < m, c.nmem (R + 3 + 6 * n + i) < n ∧ g (c.nmem (R + 3 + 6 * n + i)) = en i)
    {n' : ℕ} (r57 : c.nreg 8557 = n') (r71 : c.nreg 8571 = Sb + 21 * m + 38 * n + 8 * k + 24 + n)
    (hn' : n' ≤ n) (hn'1 : 1 ≤ n')
    (hIX : ∀ q < n', c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q) < n)
    (hcov : 0 < m → ∀ q < n', ∃ f < m, en f = g (c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q)))
    (hPD : PathPD M (fun q => g (c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q))) n'
      (Sb + 21 * m + 38 * n + 8 * k + 24 + n) c π.path)
    (hρ : π.path.Simple Hs) (hπ : π.segs = segsF π.path Hs) (hm0 : m = 0 → π.segs = [])
    (hHP : ∀ i < n, c.nmem (R + 3 + 2 * n + i) = hlab Hs (M.tail (g i)))
    (heninj : ∀ i < m, ∀ j < m, en i = en j → i = j) :
    ∃ c' t, Exec I W lsH2 c c' t ∧ t ≤ 1720 * n + 37 * m + 107 * k + 1550 ∧
      (∀ i < m, c'.nmem (Sb + i) = bf (en i ∈ l.piece)) ∧
      (∀ i < m, c'.nmem (Sb + m + i) = bf (en i ∈ π.path.darts.toFinset)) ∧
      (∀ i < m, c'.nmem (Sb + 2 * m + i) = bf (M.tail (en i) ∈ π.path.mverts)) ∧
      (∀ j < k, c'.nmem (Sb + 3 * m + j) = bf (¬ Disjoint (Hs.getD j ∅) π.path.mverts)) ∧
      c'.nmem (Sb + 3 * m + k) = ntag l ∧ c'.nmem (Sb + 3 * m + k + 1) = ntag r ∧
      RecsOut M ds gid ν S T l r π Hs σ (Sb + 21 * m + 4 * k + 2) hi (c'.nreg 6501) c'.nmem ∧
      SegsOut' M en m π (c'.nreg 6501 + 2 + c'.nmem (c'.nreg 6501) +
        c'.nmem (c'.nreg 6501 + 1)) hi (c'.nreg 6502) c'.nmem ∧
      (∀ a, a < Sb → c'.nmem a = c.nmem a) ∧
      (∀ x, 3000 ≤ x → x ≤ 3012 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lsH2
  obtain ⟨c₁, t₁, e₁, ht₁, tl, tr, hRO, M1, hR1, hL1, F1, rr1, rm1, o1'⟩ := ls8_exec (I := I)
    (ds := ds) c hc hR hL hU r4 hm hk hRm hn o1 o2 (by omega) (by omega) arr hk' pw hSC hTC hSA
    stab sp hLF hVF (by rw [hk']; exact hHM) hDF hCC hlr hlrev hrrev hl hr hν hpk hloop hs hsW
    hlargeL hlargeR
  set E := Sb + 21 * m + 38 * n + 8 * k + 24 with hE
  have K1 : ∀ a, E ≤ a → c₁.nmem a = c.nmem a := fun a ha => M1 a (Or.inr ha)
  obtain ⟨c₂, t₂, e₂, ht₂, O1, O2, O3, O4, M2, hR2, hL2, F2, rr2, rm2, o2'⟩ := ls9_exec (I := I)
    (en := en) (g := g) (X := l.piece) (Y := π.path.darts.toFinset) (C := π.path.mverts)
    (hf := fun j => bf (¬ Disjoint (Hs.getD j ∅) π.path.mverts)) c₁ e₁.wb_right hR1 hL1 hU
    (fun i hi => by rw [M1 _ (Or.inl (by omega))]; exact hFX i hi)
    (fun i hi => by rw [K1 _ (by omega)]; exact hLF i hi)
    (fun i hi => by rw [K1 _ (by omega)]; exact hDF i hi)
    (fun i hi => by rw [K1 _ (by omega)]; exact hVF i hi)
    (fun j hj => by rw [K1 _ (by omega)]; exact hHM j hj) o1 (by omega) (by omega)
  -- the records' end
  obtain ⟨hlo1, hhi1, -, -⟩ := id hRO
  have X1 := hlo1
  have Xr : c₂.nreg 6501 = c₁.nreg 6501 := F2 _ (by omega)
  have Xm : ∀ a, Sb + 21 * m + 4 * k + 2 ≤ a → c₂.nmem a = c₁.nmem a := fun a ha =>
    M2 a (by omega)
  have K2 : ∀ a, E ≤ a → c₂.nmem a = c.nmem a := fun a ha => by
    rw [Xm a (by omega)]; exact K1 a ha
  obtain ⟨c₃, t₃, e₃, ht₃, hSO, v02, M3, F3, rr3, rm3, o3⟩ := ls10_exec (I := I) (en := en)
    (g := g) (Hs := Hs) (π := π) c₂ e₂.wb_right hR2 hL2 hU
    (by rw [F2 _ (by omega), F1 _ (by omega)]; exact r57)
    (by rw [F2 _ (by omega), F1 _ (by omega)]; exact r71) hn' hn'1
    (fun q hq => by rw [K2 _ (by omega)]; exact hIX q hq)
    (fun h q hq => by rw [K2 _ (by omega)]; exact hcov h q hq)
    (pathPD_congr hPD (fun j hj => K2 _ (by omega)) (fun i hi => by
      show g (c₂.nmem (E + i)) = g (c.nmem (E + i)); rw [K2 _ (by omega)])) hρ hπ hm0
    (fun i hi => by rw [M2 _ (by omega), M1 _ (Or.inl (by omega))]; exact hHP i hi)
    (fun f hf => by rw [M2 _ (by omega), M1 _ (Or.inl (by omega))]; exact hFX f hf)
    (fun i hi j hj h => arr.g_inj hi hj h) heninj
    (lo := c₁.nreg 6501 + 2 + c₁.nmem (c₁.nreg 6501) + c₁.nmem (c₁.nreg 6501 + 1))
    (hi := hi) (by omega) (by omega) o1 (by omega) (by omega)
  have Y3 : ∀ a, Sb + 21 * m + 4 * k + 2 ≤ a → a < E → c₃.nmem a = c₁.nmem a := fun a h1 h2 => by
    rw [M3 a (by omega) (by omega), Xm a h1]
  have Xr3 : c₃.nreg 6501 = c₁.nreg 6501 := by rw [F3 _ (Or.inr rfl), Xr]
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, fun x h1 h2 => ?_,
    by rw [rr3, rr2, rr1], by rw [rm3, rm2, rm1], by rw [o3, o2', o1']⟩
  · rw [M3 _ (by omega) (by omega)]; exact O1 i hi
  · rw [M3 _ (by omega) (by omega)]; exact O2 i hi
  · rw [M3 _ (by omega) (by omega)]; exact O3 i hi
  · rw [M3 _ (by omega) (by omega)]; exact O4 j hj
  · rw [M3 _ (by omega) (by omega), M2 _ (by omega)]; exact tl
  · rw [M3 _ (by omega) (by omega), M2 _ (by omega)]; exact tr
  · rw [Xr3]
    exact (RecsOut.congr hRO fun a h1 h2 => Y3 a (by omega) h2).mono (by omega)
  · rw [Xr3, Y3 _ (by omega) (by omega), Y3 _ (by omega) (by omega), v02]
    exact hSO
  · rw [M3 a (by omega) (by omega), M2 a (by omega), M1 a (Or.inl ha)]
  · rw [F3 x (Or.inl (by omega)), F2 x (by omega), F1 x (by omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
