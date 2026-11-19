module

public import PlanarFlow.NegSSSP.Enc.FeHcB
public import PlanarFlow.NegSSSP.Enc.NodeOne

/-!
# The whole node as one fixed program: the pieces

* `hfSave dst src`: `r(dst+1) := r src`, `r dst := 2 · r src + 1` (scratch `10520`), 4 steps,
  `hfSave_exec`. Used to move the bound `Hc` of each encoder (register `2125`, renamed `3325`)
  into the node's parameters `2 Hc + 1`, `Hc` (`10411`, `10412` for the first part, `10466`,
  `10467` for the second).
* **`nodeFullT`** `= feFixT 10000 ; hfSave 10411 3325 ; feFixT 10200 ; hfSave 10466 3325 ;
  nodeFixT`: **the node of the recursion as one fixed statement** (independent of the instance).
* `hf_enc_ok` (the renamed encoder names only `[2600, 3748)`, no input, no `rand`),
  `hnV_upd` (the node parameters other than `2 Hcᵢ + 1`, `Hcᵢ` do not depend on `Hcᵢ`),
  `kpnOf_len` (`kpnOf` depends on the input words only through their number).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {I : Input} {W : ℕ}

/-- `r(dst+1) := r src`, `r dst := 2 r src + 1`. -/
def hfSave (dst src : ℕ) : Stmt :=
  block [.copyN (dst + 1) src, .addN dst src src, .constN 10520 1, .addN dst dst 10520]

theorem hfSave_exec {dst src : ℕ} (c : Config) (hc : WordsBounded W c)
    (h : 2 * c.nreg src + 1 ≤ W) (hs : src < 10400) (hd : 10400 ≤ dst) (hd' : dst + 1 < 10520) :
    ∃ c', Exec I W (hfSave dst src) c c' 4 ∧ c'.nreg (dst + 1) = c.nreg src ∧
      c'.nreg dst = 2 * c.nreg src + 1 ∧
      (∀ r, r ≠ dst → r ≠ dst + 1 → r ≠ 10520 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have n1 : src ≠ dst + 1 := by omega
  have n2 : src ≠ dst := by omega
  have e1 := Exec.copyN (P := I) hc (dst + 1) src
  set c1 := { c with nreg := upd c.nreg (dst + 1) (c.nreg src) } with hc1
  have v1 : c1.nreg src = c.nreg src := upd_other _ _ _ n1
  have e2 := Exec.addN (P := I) e1.wb_right dst src src (by rw [v1]; omega)
  set c2 := { c1 with nreg := upd c1.nreg dst (c1.nreg src + c1.nreg src) } with hc2
  have e3 := Exec.constN (P := I) e2.wb_right 10520 1 (by omega)
  set c3 := { c2 with nreg := upd c2.nreg 10520 1 } with hc3
  have v3 : c3.nreg dst + c3.nreg 10520 = 2 * c.nreg src + 1 := by
    simp only [hc3, hc2, upd_same, upd_other _ _ _ (show dst ≠ 10520 by omega), v1]; omega
  have e4 := Exec.addN (P := I) e3.wb_right dst dst 10520 (by rw [v3]; exact h)
  refine ⟨_, .seq e1 (.seq e2 (.seq e3 (.seq e4 (.skip e4.wb_right)))), ?_, ?_, ?_, rfl, rfl,
    rfl, rfl⟩
  · simp only [upd_other _ _ _ (show dst + 1 ≠ dst by omega),
      upd_other _ _ _ (show dst + 1 ≠ 10520 by omega), hc3, hc2, hc1, upd_same]
  · simp only [upd_same]; exact v3
  · intro r h1 h2 h3
    simp only [upd_other _ _ _ h1, upd_other _ _ _ h3, hc3, hc2, hc1, upd_other _ _ _ h2]

/-- **The node of the recursion as one fixed statement.** -/
def nodeFullT : Stmt :=
  .seq (feFixT 10000) <| .seq (hfSave 10411 3325) <| .seq (feFixT 10200) <|
    .seq (hfSave 10466 3325) nodeFixT

theorem hf_enc_ok (p : FeP) : (rnS nbSwap (feProgDk p)).regsOK nbU = true ∧
    (rnS nbSwap (feProgDk p)).noInp = true ∧ (rnS nbSwap (feProgDk p)).noRand = true := by
  refine ⟨?_, ?_, ?_⟩ <;> kernel_rfl

theorem hf_swap2125 : nbSwap.symm 3325 = 2125 := rfl

set_option maxHeartbeats 2000000 in
/-- The node parameters other than `2 Hcᵢ + 1`, `Hcᵢ` do not depend on `Hcᵢ`. -/
theorem hnV_upd (p₀ p₁ : KPN) (a b M H βN j : ℕ) (hj : j < 115) (h11 : j ≠ 11) (h12 : j ≠ 12)
    (h66 : j ≠ 66) (h67 : j ≠ 67) :
    hnV { p₀ with Hc := a } { p₁ with Hc := b } M H βN j = hnV p₀ p₁ M H βN j := by
  interval_cases j <;> first | (exfalso; omega) | kernel_rfl

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

/-- `kpnOf` depends on the input words only through their number, and its field `Hc` is the
argument `Hc`. -/
theorem kpnOf_len {X : Finset D} {B : Finset V} (fd : FaceData N X B) (ℓ : D → ℤ) (n Bw : ℕ)
    {Pk Pk' : Input} (hl : Pk.data.length = Pk'.data.length) (β RkN Pb Hc βK βN M : ℕ) :
    kpnOf fd ℓ n Bw Pk β RkN Pb Hc βK βN M =
      { kpnOf fd ℓ n Bw Pk' β RkN Pb 0 βK βN M with Hc := Hc } := by
  unfold kpnOf; rw [hl]

theorem fePk_len (p : FeP) (m : ℕ → ℕ) : (fePk p m).data.length = p.Kw + 1 := by
  simp [fePk]

end NegSSSP

end PlanarFlow
