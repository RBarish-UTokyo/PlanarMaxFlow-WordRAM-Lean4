module

public import PlanarFlow.Monge.FRProg
public import PlanarFlow.Monge.FRLayout
public import WordRAM.Machine.WordMono

/-!
# FR-Dijkstra at a base offset and inside a larger configuration

`PlanarFlow.Monge.FR.frProg_exec` runs `frProg` from any configuration holding its input
(`Inp`: the bases in `r100 … r109`; `Data`: the arrays) for any layout `Prm` meeting `Lay`, with
word bound `P.W`; `mkPrm` lays the arrays out from address `0`.

* `Prm.shift σ P`: all the bases and the word bound moved up by `σ` (`Lay.shift`); `mkPrmAt σ`
  is `mkPrm` at the base `σ` (`mkPrmAt_lay`). The run of `frProg_exec` applies unchanged.
* `frProg_regsOK`, `frProg_noInp`, `frProg_noRand`: `frProg` names only the registers `< 372`
  and reads no input.
* `frProg_exec_emb`: **inside a larger configuration** `d` with any word bound `W' ≥ P.W`, by
  `WordRAM.Machine.Exec.lift_trunc`: `frProg` runs from `d` within `frCost P` steps with the
  outcome of `frProg_exec` read in `d'`, keeping every register `≥ 372` and all the memory above
  `P.W` (the frame), provided the registers `< 372` and the memory at addresses `≤ P.W` of `d`
  are bounded by `P.W`. For a layout at the base `σ` (`mkPrmAt σ`) the memory below `σ` is not
  in the frame (the run of `frProg_exec` does not record which cells below `P.W` it writes);
  the frame is the memory above `P.W`.
-/

@[expose] public section

namespace PlanarFlow

namespace Monge

namespace FR

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- All the bases and the word bound of a layout moved up by `σ`. -/
def Prm.shift (σ : ℕ) (P : Prm) : Prm :=
  { P with
    Db := σ + P.Db, pb := σ + P.pb, ob := σ + P.ob, lb := σ + P.lb, sb := σ + P.sb,
    db := σ + P.db, wb := σ + P.wb, W := σ + P.W }

theorem Prm.shift_hb (σ : ℕ) (P : Prm) : (P.shift σ).hb = σ + P.hb := by
  unfold Prm.hb Prm.shift; dsimp only; omega

theorem Prm.shift_Lv (σ : ℕ) (P : Prm) : (P.shift σ).Lv = P.Lv := rfl

theorem Prm.shift_TB (σ : ℕ) (P : Prm) : (P.shift σ).TB = P.TB := rfl

theorem Prm.shift_rb (σ : ℕ) (P : Prm) : (P.shift σ).rb = σ + P.rb := by
  unfold Prm.rb Prm.bh Prm.tb
  rw [Prm.shift_hb, Prm.shift_Lv, Prm.shift_TB]
  unfold Prm.shift; dsimp only; omega

/-- **The shifted layout meets `Lay`.** -/
theorem Lay.shift {P : Prm} (hL : Lay P) (σ : ℕ) : Lay (P.shift σ) where
  b_pos := hL.b_pos
  bN := hL.bN
  r_lt := hL.r_lt
  m1 := by have := hL.m1; unfold Prm.shift; dsimp only; omega
  m2 := by have := hL.m2; unfold Prm.shift; dsimp only; omega
  m3 := by have := hL.m3; unfold Prm.shift; dsimp only; omega
  m4 := by have := hL.m4; unfold Prm.shift; dsimp only; omega
  m5 := by have := hL.m5; unfold Prm.shift; dsimp only; omega
  m6 := by have := hL.m6; unfold Prm.shift; dsimp only; omega
  w := by
    have := hL.w; rw [Prm.shift_Lv]; unfold Prm.shift; dsimp only; omega
  wx := by
    have := hL.wx; rw [Prm.shift_rb, Prm.shift_Lv]; unfold Prm.shift; dsimp only; omega
  off_mono := hL.off_mono
  off_last := hL.off_last
  dst_lt := hL.dst_lt

/-- The feasibility of the prices does not depend on the bases. -/
theorem Feas.shift {P : Prm} (hF : Feas P) (σ : ℕ) : Feas (P.shift σ) := hF

/-- **The layout of `mkPrm` at the base `σ`.** -/
noncomputable def mkPrmAt (σ N b : ℕ) (D : ℕ → ℕ → ℤ) (p : ℕ → ℤ) (r : ℕ)
    (Es : List (ℕ × ℕ × ℤ)) : Prm :=
  (mkPrm N b D p r Es).shift σ

theorem mkPrmAt_lay {σ N b : ℕ} {D : ℕ → ℕ → ℤ} {p : ℕ → ℤ} {r : ℕ} {Es : List (ℕ × ℕ × ℤ)}
    (hb : 1 ≤ b) (hbN : b ≤ N) (hr : r < N) (hhd : ∀ a ∈ Es, a.2.1 < N) :
    Lay (mkPrmAt σ N b D p r Es) :=
  (mkPrm_lay hb hbN hr hhd).shift σ

/-- `frProg` names only the registers `< 372`. -/
theorem frProg_regsOK : frProg.regsOK (fun r => decide (r < 372)) = true := by decide

/-- `frProg` reads no input. -/
theorem frProg_noInp : frProg.noInp = true := by decide

/-- `frProg` uses no random word. -/
theorem frProg_noRand : frProg.noRand = true := by decide

/-- The register predicate of `frProg`. -/
abbrev frU : ℕ → Bool := fun r => decide (r < 372)

variable {P : Prm} {I : Input}

/-- The arrays of the input lie below the work space. -/
theorem Data.congr (hL : Lay P) {c c' : Config} (h : Data P c)
    (hn : ∀ a ≤ P.W, c'.nmem a = c.nmem a) (hr : ∀ a ≤ P.W, c'.rmem a = c.rmem a) :
    Data P c' := by
  have := hL.m6; have := lay_w hL; have := hL.m5
  exact h.of hL (fun a ha => hn a (by omega)) (fun a ha => hr a (by omega))

/-- The result of a run reads only the flags and the distances, below the work space. -/
theorem FRes.congr (hL : Lay P) {K : ℕ} {v : ℕ → ℕ} {dd : ℕ → ℤ} {nm nm' : ℕ → ℕ}
    {rm rm' : ℕ → ℝ} (h : FRes P K v dd nm rm) (hn : ∀ a ≤ P.W, nm' a = nm a)
    (hr : ∀ a ≤ P.W, rm' a = rm a) : FRes P K v dd nm' rm' := by
  have := hL.m6; have := lay_w hL; have := hL.m5
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, h3, h4, fun y hy => ?_, fun i hi => ?_⟩
  · rw [hn _ (by omega)]; exact h5 y hy
  · have := h3 i hi; rw [hr _ (by omega)]; exact h6 i hi

/-- **FR-Dijkstra inside a larger configuration.** For a layout `P` meeting `Lay`, a Monge
dense distance graph and feasible prices, from any `d` bounded by `W' ≥ P.W` holding the input
(`Inp`, `Data`), with its registers `< 372` and its memory at addresses `≤ P.W` bounded by
`P.W`, `frProg` runs on any input within `frCost P` steps; at the end the input arrays are
intact, the output and the registers `< 100` are kept, a run `(K, v, dd)` of Dijkstra's algorithm
is in the memory (`FRes`), and every register `≥ 372` and all the memory above `P.W` are
unchanged. -/
theorem frProg_exec_emb (hL : Lay P) (hDc : Crossing P.b P.D) (hF : Feas P) {W' : ℕ}
    (hW : P.W ≤ W') (d : Config) (hd : WordsBounded W' d) (hin : Inp P d) (hDa : Data P d)
    (hrb : ∀ r < 372, d.nreg r ≤ P.W) (hmb : ∀ a ≤ P.W, d.nmem a ≤ P.W) :
    ∃ d' k, Exec I W' frProg d d' k ∧ k ≤ frCost P ∧ Data P d' ∧ d'.output = d.output ∧
      (∀ r < 100, d'.nreg r = d.nreg r) ∧ (∀ r < 100, d'.rreg r = d.rreg r) ∧
      (∃ K v dd, FRes P K v dd d'.nmem d'.rmem) ∧
      (∀ r, 372 ≤ r → d'.nreg r = d.nreg r) ∧ (∀ r, 372 ≤ r → d'.rreg r = d.rreg r) ∧
      (∀ a, P.W < a → d'.nmem a = d.nmem a) ∧ (∀ a, P.W < a → d'.rmem a = d.rmem a) := by
  set c := trunc frU P.W d with hcdef
  have hA := agree_trunc frU P.W d
  have hn : ∀ r < 372, c.nreg r = d.nreg r := fun r hr => (hA.nreg r (by simp [frU, hr])).symm
  have hnr : ∀ r < 372, c.rreg r = d.rreg r := fun r hr => (hA.rreg r (by simp [frU, hr])).symm
  have hw : WordsBounded P.W c :=
    wordsBounded_trunc (fun r hr => hrb r (by simpa [frU] using hr)) hmb
  have hinc : Inp P c := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hn _ (by omega)]
    exacts [hin.r100, hin.r101, hin.r102, hin.r103, hin.r104, hin.r105, hin.r106, hin.r107,
      hin.r108, hin.r109]
  have hDac : Data P c := hDa.congr hL (fun a ha => (hA.nmem a ha).symm) (fun a ha => (hA.rmem a ha).symm)
  obtain ⟨c', k, e, hk, hDa', ho, hr1, hr2, K, v, dd, hres⟩ :=
    frProg_exec (I := I) hL hDc hF c hw hinc hDac
  obtain ⟨d', e', hA', hK, ho'⟩ :=
    Exec.lift_trunc (P' := I) e frProg_regsOK frProg_noInp frProg_noRand hW hd
  refine ⟨d', k, e', hk, hDa'.congr hL hA'.nmem hA'.rmem, by rw [ho', ho]; rfl,
    fun r hr => ?_, fun r hr => ?_, ⟨K, v, dd, hres.congr hL hA'.nmem hA'.rmem⟩,
    fun r hr => hK.nreg r (by simp [frU]; omega), fun r hr => hK.rreg r (by simp [frU]; omega),
    hK.nmem, hK.rmem⟩
  · rw [hA'.nreg r (by simp [frU]; omega), hr1 r hr, hn r (by omega)]
  · rw [hA'.rreg r (by simp [frU]; omega), hr2 r hr, hnr r (by omega)]

end FR

end Monge

end PlanarFlow
