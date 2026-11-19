module

public import PlanarFlow.NegSSSP.NdFullSem

/-!
# The full branch: the split re-run, its data in memory

* **`bigOut_agree`**: `BigOut` (the data the split leaves in the large case) is a fact about the
  memory below `B₀ + 66 k + 35` and the registers `< 972`: it holds in every configuration that
  agrees there.
* **`Frame.spStage_exec'`**: `spStage_exec` exporting the agreement of the final configuration
  with the canonical end `spFin g N Q` on the split's work area and the registers `< 972`
  (copy of the proof), so (`spFin_big`, `bigOut_agree`) in the large case the final
  configuration meets `BigOut`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

section Big

open Orbit CombMap BKMNW PlanarSeparator PlanarSeparator.MillerProg PlanarSeparator.StDart

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {N : CombMap D V F}

open Classical in
/-- **`BigOut` depends only on the split's work area and the registers `< 972`.** -/
theorem bigOut_agree {Pc : Finset D} {m k : ℕ} {δ : ℕ → D} {B₀ : ℕ} {x₁ : D} {c c' : Config}
    {Ws : ℕ} (h : BigOut N Pc m k δ B₀ x₁ c) (hA : Agree (fun r => decide (r < 972)) Ws c c')
    (hmk : m ≤ k) (hW : B₀ + 66 * k + 35 ≤ Ws) : BigOut N Pc m k δ B₀ x₁ c' := by
  obtain ⟨A₀, hcut, hside, nV, nF, q, ν, hν, hnvf, hq, hpos0, hpos1, m', cn, vn, fn, ψ, C, Z,
    hm', hνeq, hqk, hψ, hs1, hs2, hbd1, hbd2, hBs, hE, hz1, hz0, hX, hF, r960, r961, r962, r800,
    r801, r802, r803, r804, r805, r807, r808⟩ := h
  have hm : ∀ a ≤ Ws, c'.nmem a = c.nmem a := hA.nmem
  have hr : ∀ r < 972, c'.nreg r = c.nreg r := fun r hr => hA.nreg r (by simp [hr])
  refine ⟨A₀, hcut, fun x hx => by rw [hm _ (by omega)]; exact hside x hx, nV, nF, q, ν, hν,
    hnvf, hq, hpos0.congr rfl fun b _ => hm _ (by have := hν b; omega),
    hpos1.congr rfl fun b _ => hm _ (by have := hν b; omega), m', cn, vn, fn, ψ, C, Z, hm',
    hνeq, hqk, hψ, hs1, hs2, hbd1, hbd2, hBs,
    enc_congr hE fun i hi => ⟨hm _ (by omega), hm _ (by omega), hm _ (by omega),
      hm _ (by omega), hm _ (by omega)⟩,
    fun x => by rw [hm _ (by have := (cn x).2; omega)]; exact hz1 x,
    fun x => by rw [hm _ (by have := (cn x).2; omega)]; exact hz0 x,
    fun h hh hm' => by rw [hm _ (by omega)]; exact hX h hh hm',
    fun x hx => by rw [hm _ (by omega)]; exact hF x hx, ?_⟩
  rw [hr 960 (by omega), hr 961 (by omega), hr 962 (by omega), hr 800 (by omega),
    hr 801 (by omega), hr 802 (by omega), hr 803 (by omega), hr 804 (by omega),
    hr 805 (by omega), hr 807 (by omega), hr 808 (by omega)]
  exact ⟨r960, r961, r962, r800, r801, r802, r803, r804, r805, r807, r808⟩

end Big

namespace Frame

open BKMNW Driver

variable {P : Input} {W : ℕ}

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {g : GIds D V} {N : CombMap D V F}

/-- **`spStage_exec` with the agreement with the canonical run** (see the module docstring). -/
theorem spStage_exec' (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {ℓ : D → ℤ} {L n : ℕ} {Q : Finset D} (hQ : Q ⊆ reps N) {d e : ℕ} (c : Config)
    (hc : WordsBounded W c) (hin : InP g N ℓ L n Q d e c) (r04 : c.nreg 3004 = d)
    (hd : spWs (ck N Q) < d) (hrr : ∀ r < 972, c.rreg r = 0)
    (hrm : ∀ a ≤ spWs (ck N Q), c.rmem a = 0) (hW : d + 4 + 3 * ck N Q + 1 ≤ W)
    (hW2 : spWs (ck N Q) + 205 ≤ W) :
    ∃ c' t, Exec P W spStage c c' t ∧ t ≤ prepCost (ck N Q) + splitT (ck N Q) ∧
      Agree spU (spWs (ck N Q)) (spFin g N Q) c' ∧
      c'.nreg 2966 = 1 ∧ c'.nreg 2969 = ck N Q ∧ c'.nreg 2972 = spB0 (ck N Q) ∧
      (∀ a, spWs (ck N Q) < a → c'.nmem a = c.nmem a) ∧
      (∀ r, 972 ≤ r → (r < 2966 ∨ 2980 < r) → c'.nreg r = c.nreg r) ∧
      (∀ r, 972 ≤ r → c'.rreg r = c.rreg r) ∧
      (∀ a, spWs (ck N Q) < a → c'.rmem a = c.rmem a) ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, hA, m₁, n₁, p66, p69, p72, r₁, rm₁, o₁⟩ :=
    spPrep_agree (P := P) c hc hin r04 hd hrr hrm hW hW2
  obtain ⟨⟨t₀, ex₀, ht₀⟩, -, -⟩ := spFin_run (g := g) hM hrot hface hQ
  obtain ⟨c₂, e₂, hA₂, hK₂, -⟩ := Exec.lift (P' := P) ex₀ splitProg_ok.1 splitProg_ok.2.1
    splitProg_ok.2.2 (show spWs (ck N Q) ≤ W by omega) hA e₁.wb_right
  have hU : ∀ r, 972 ≤ r → spU r = false := fun r hr => by simp [spU]; omega
  refine ⟨c₂, t₁ + t₀, .seq e₁ e₂, by omega, hA₂, by rw [hK₂.nreg _ (hU _ (by omega))]; exact p66,
    by rw [hK₂.nreg _ (hU _ (by omega))]; exact p69,
    by rw [hK₂.nreg _ (hU _ (by omega))]; exact p72, fun a ha => ?_, fun r h1 h2 => ?_,
    fun r hr => ?_, fun a ha => ?_, ?_⟩
  · rw [hK₂.nmem a ha, m₁ a ha]
  · rw [hK₂.nreg r (hU r h1), n₁ r h1 h2]
  · rw [hK₂.rreg r (hU r hr), r₁]
  · rw [hK₂.rmem a ha, rm₁]
  · rw [exec_output e₂ splitProg_noOut, o₁]

end Frame

end NegSSSP

end PlanarFlow
