module

public import PlanarFlow.BKMNW.LinJoin
public import PlanarFlow.BKMNW.MfDrvFrame

/-!
# The sum of the children's flows in the parent's frame (`joinFlow`, on the frames)

At a node call `x = (.node l r π, Hs, σ)` the driver hands the combination the parent's input
frame (`FInL` at `d`) and the two children's output frames (`FOutL` of `chL` at `bl + 5`, of
`chR` at `el + 5`). **`njProg_join`**: the program `njProg` (`PlanarFlow/BKMNW/LinJoin.lean`)
writes into the parent's array `FL` the sum `joinFlow fl fr` of the children's flows (the input of
`sepStep` in `arunL`), within `44 m + 59` steps (`m` the darts of the parent piece map):

* the merge on `GID` finds the parent index of every child dart (the numberings are the
  increasing orders of `gid`, and the child darts are parent darts: `pdarts_child_sub`);
* the children's darts are disjoint (`Disjoint l.piece r.piece`, from `Good`), so every parent dart
  takes the flow of the child it belongs to, and `0` (the offset `Z`) off both.

`fext_joinFlow` (`fext (joinFlow fl fr) = fext fl + fext fr` on the parent darts), `Lay.gid_inj`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-- `joinFlow` extended by zero is the sum of the extensions, on the parent darts. -/
lemma fext_joinFlow {B Bl Br : Finset D} (fl : SDart Bl → ℤ) (fr : SDart Br → ℤ) {y : D}
    (hy : y ∈ B) : fext (joinFlow (B := B) fl fr) y = fext fl y + fext fr y := by
  unfold fext joinFlow
  simp only [hy, dite_true]

/-- Equal global numbers of a dart of the frame and an enumerated dart: the same dart. -/
lemma Lay.gid_inj {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (h : Lay M gid u S T Z x m en d mem) {y : D} (hy : y ∈ pdarts M x.1.piece x.2.1) {i : ℕ}
    (hi : i < m) (he : gid y = gid (en i)) : y = en i := by
  obtain ⟨i', hi', rfl⟩ := h.en_surj y hy
  rw [h.en_inj hi' hi (by
    rcases lt_trichotomy i' i with hlt | heq | hlt
    · have := h.en_mono i' i hlt hi; omega
    · rw [heq]
    · have := h.en_mono i i' hlt hi'; omega)]

/-- The strictly increasing `GID` array of a frame. -/
lemma Lay.gd_mono {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (h : Lay M gid u S T Z x m en d mem) :
    ∀ i j, i < j → j < m → mem (d + 4 + i) < mem (d + 4 + j) := fun i j hij hj => by
  rw [h.gd i (by omega), h.gd j hj]; exact h.en_mono i j hij hj

/-- **The sum of the children's flows in the parent's frame** (see the module docstring). -/
theorem njProg_join {I : Input} {W : ℕ} {Reach : MCall M → Prop} (l r : ADec M) (π : HSep M)
    (Hs : List (Finset V)) (σ : Perm D) {d e bl el er : ℕ} (c : Config) (hc : WordsBounded W c)
    (r4 : c.nreg 3004 = d) (r6 : c.nreg 3006 = bl + 5) (r8 : c.nreg 3008 = el + 5)
    (r9 : c.nreg 3009 = er) (h1 : e ≤ bl) (h2 : bl + 5 ≤ el) (h3 : el + 5 ≤ er)
    {fl : SDart (pdarts M (chL M l r π Hs σ).1.piece (chL M l r π Hs σ).2.1) → ℤ}
    {fr : SDart (pdarts M (chR M l r π Hs σ).1.piece (chR M l r π Hs σ).2.1) → ℤ}
    (hin : FInL M Reach gid u S T Z (.node l r π, Hs, σ) d e c)
    (hl : FOutL M gid u S T Z (chL M l r π Hs σ) fl (bl + 5) el c)
    (hr : FOutL M gid u S T Z (chR M l r π Hs σ) fr (el + 5) er c) :
    ∃ c' t m en, Exec I W njProg c c' t ∧ t ≤ 44 * m + 59 ∧
      Lay M gid u S T Z (.node l r π, Hs, σ) m en d c'.nmem ∧ d + fsz m ≤ e ∧
      (∀ i < m, (c'.nmem (d + 4 + 6 * m + i) : ℤ) =
        Z + fext (joinFlow (B := pdarts M (l.piece ∪ r.piece) Hs) fl fr) (en i)) ∧
      (∀ a, a < bl + 5 → ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, x < 6260 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨-, hok, m, en, hL, hfs⟩ := hin
  obtain ⟨ml, enl, hLl, hfsl, hfl⟩ := hl
  obtain ⟨mr, enr, hLr, hfsr, hfr⟩ := hr
  unfold fsz at hfs hfsl hfsr
  have her : er ≤ W := r9 ▸ hc.1 3009
  -- the child darts are parent darts, and the two children are disjoint
  obtain ⟨-, ⟨-, -, hdis, -⟩, -⟩ := hok
  have sL : pdarts M l.piece (childHoles Hs π.path.mverts) ⊆ pdarts M (l.piece ∪ r.piece) Hs :=
    fun y hy => (mem_sdiff.1 (pdarts_child_sub π.path subset_union_left hy)).1
  have sR : pdarts M r.piece (childHoles Hs π.path.mverts) ⊆ pdarts M (l.piece ∪ r.piece) Hs :=
    fun y hy => (mem_sdiff.1 (pdarts_child_sub π.path subset_union_right hy)).1
  have dLR : ∀ y, y ∈ pdarts M l.piece (childHoles Hs π.path.mverts) →
      y ∉ pdarts M r.piece (childHoles Hs π.path.mverts) := fun y h1 h2 =>
    disjoint_left.1 hdis (pdarts_subset _ _ h1) (pdarts_subset _ _ h2)
  have eLm : ∀ k < ml, enl k ∈ pdarts M l.piece (childHoles Hs π.path.mverts) := hLl.en_mem
  have eRm : ∀ k < mr, enr k ∈ pdarts M r.piece (childHoles Hs π.path.mverts) := hLr.en_mem
  have eBm : ∀ i < m, en i ∈ pdarts M (l.piece ∪ r.piece) Hs := hL.en_mem
  -- the sizes
  have hcard : ml + mr ≤ m := by
    rw [hL.card, hLl.card, hLr.card]
    simp only [chL, chR, ADec.piece]
    rw [← card_union_of_disjoint (disjoint_left.2 fun y h1 h2 => dLR y h1 h2)]
    exact card_le_card (union_subset sL sR)
  -- the merge hypotheses
  have exL : ∀ k < ml, ∃ i < m, c.nmem (d + 4 + i) = c.nmem (bl + 5 + 4 + k) := fun k hk => by
    obtain ⟨i, hi, he⟩ := hL.en_surj _ (sL (eLm k hk))
    exact ⟨i, hi, by rw [hL.gd i hi, hLl.gd k hk, he]⟩
  have exR : ∀ k < mr, ∃ i < m, c.nmem (d + 4 + i) = c.nmem (el + 5 + 4 + k) := fun k hk => by
    obtain ⟨i, hi, he⟩ := hL.en_surj _ (sR (eRm k hk))
    exact ⟨i, hi, by rw [hL.gd i hi, hLr.gd k hk, he]⟩
  obtain ⟨c', t, ex, ht, va, vb, vc, vm, vr, vrr, vrm, vo⟩ := njProg_exec (P := I) c hc r4 r6 r8
    hL.hm hLl.hm hLr.hm hL.hz (by omega) (by omega) (by omega) hL.gd_mono hLl.gd_mono
    hLr.gd_mono exL exR
  refine ⟨c', t, m, en, ex, by omega,
    hL.congr fun a ha1 ha2 => vm a (by omega) (by omega), by unfold fsz; omega,
    fun i hi => ?_, vm, vr, vrr, vrm, vo⟩
  rw [fext_joinFlow fl fr (eBm i hi)]
  by_cases hyr : en i ∈ pdarts M r.piece (childHoles Hs π.path.mverts)
  · obtain ⟨k, hk, hke⟩ := hLr.en_surj _ hyr
    have hfl0 : fext fl (en i) = 0 := by
      unfold fext; split_ifs with h
      · exact absurd hyr (dLR _ h)
      · rfl
    rw [va i hi k hk (by rw [hLr.gd k hk, hL.gd i hi, hke]), hfr k hk, hke, hfl0, zero_add]
  · have hnr : ∀ k' < mr, c.nmem (el + 5 + 4 + k') ≠ c.nmem (d + 4 + i) := fun k' hk' he => by
      rw [hLr.gd k' hk', hL.gd i hi] at he
      exact hyr (hL.gid_inj (sR (eRm k' hk')) hi he ▸ eRm k' hk')
    have hfr0 : fext fr (en i) = 0 := by
      unfold fext; split_ifs with h
      · exact absurd h hyr
      · rfl
    by_cases hyl : en i ∈ pdarts M l.piece (childHoles Hs π.path.mverts)
    · obtain ⟨k, hk, hke⟩ := hLl.en_surj _ hyl
      rw [vb i hi k hk (by rw [hLl.gd k hk, hL.gd i hi, hke]) hnr, hfl k hk, hke, hfr0, add_zero]
    · have hnl : ∀ k' < ml, c.nmem (bl + 5 + 4 + k') ≠ c.nmem (d + 4 + i) := fun k' hk' he => by
        rw [hLl.gd k' hk', hL.gd i hi] at he
        exact hyl (hL.gid_inj (sL (eLm k' hk')) hi he ▸ eLm k' hk')
      have hfl0 : fext fl (en i) = 0 := by
        unfold fext; split_ifs with h
        · exact absurd h hyl
        · rfl
      rw [vc i hi hnl hnr, hfl0, hfr0]; simp

end MfDrv

end BKMNW

end PlanarFlow
