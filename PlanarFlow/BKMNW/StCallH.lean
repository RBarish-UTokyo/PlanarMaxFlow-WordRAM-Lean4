module

public import PlanarFlow.BKMNW.StCallD3

/-!
# Glue lemmas for the composed s-t flow call

* `res_lt`: every word of the residue region `[β₀, β₀ + 5m + 3)` is below the modulus;
* `img_ib`: the clamped copy of the image at `ib` carries the map words, the terminal darts and
  the `KInit` words of the image in the scratch (all at most `W₀`);
* `wz_bound`: the parameter bound of `sPrm` is at most `ib + pstWN W₀ H` when `H ≥ 4m + 2`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace StCall

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP StEnc
  NsStep STFlow CombMap Klein

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {en : ℕ → D} {m : ℕ}

/-- **The residue words are below the modulus.** -/
theorem res_lt (h : EnumOK M en m) {mem : ℕ → ℕ} {Mo : ℕ} (hMo : 0 < Mo)
    {fW fP fC fR : D → ℤ} {zT zH : ℤ}
    (hwt : ∀ e, mem (101 * m + 46 + (aWT + enEq h e)) = zres Mo (fW e))
    (hph : ∀ e, mem (101 * m + 46 + (aPH m + enEq h e)) = zres Mo (fP e))
    (hcp : ∀ e, mem (101 * m + 46 + (aCP m + enEq h e)) = zres Mo (fC e))
    (hrs : ∀ e, mem (101 * m + 46 + (aRS m + enEq h e)) = zres Mo (fR e))
    (hth : mem (101 * m + 46 + aTH m) = zres Mo zT)
    (hh0 : mem (101 * m + 46 + aH0 m) = zres Mo zH)
    (hgap : ∀ i < m + 1, mem (103 * m + 46 + i) = 0) :
    ∀ a < 5 * m + 3, mem (101 * m + 46 + a) < Mo := by
  intro a ha
  have hz := zres_lt hMo
  have pick : ∀ k < m, ∃ e : D, (enEq h e : ℕ) = k := fun k hk =>
    ⟨(enEq h).symm ⟨k, hk⟩, by rw [Equiv.apply_symm_apply]⟩
  by_cases h1 : a < m
  · obtain ⟨e, he⟩ := pick a h1
    have := hwt e; rw [he] at this; unfold aWT at this; rw [zero_add] at this
    rw [this]; exact hz _
  by_cases h2 : a < 2 * m
  · obtain ⟨e, he⟩ := pick (a - m) (by omega)
    have := hph e; rw [he] at this; unfold aPH at this
    rw [show m + (a - m) = a by omega] at this; rw [this]; exact hz _
  by_cases h3 : a < 3 * m + 1
  · have := hgap (a - 2 * m) (by omega)
    rw [show 103 * m + 46 + (a - 2 * m) = 101 * m + 46 + a by omega] at this
    rw [this]; omega
  by_cases h4 : a = 3 * m + 1
  · subst h4; have := hth; unfold aTH at this; rw [this]; exact hz _
  by_cases h5 : a = 3 * m + 2
  · subst h5; have := hh0; unfold aH0 at this; rw [this]; exact hz _
  by_cases h6 : a < 4 * m + 3
  · obtain ⟨e, he⟩ := pick (a - (3 * m + 3)) (by omega)
    have := hcp e; rw [he] at this; unfold aCP at this
    rw [show 3 * m + 3 + (a - (3 * m + 3)) = a by omega] at this; rw [this]; exact hz _
  · obtain ⟨e, he⟩ := pick (a - (4 * m + 3)) (by omega)
    have := hrs e; rw [he] at this; unfold aRS at this
    rw [show 4 * m + 3 + (a - (4 * m + 3)) = a by omega] at this; rw [this]; exact hz _

/-- **The clamped image at `ib`** carries the words of the image in the scratch. -/
theorem img_ib (h : EnumOK M en m) {nF nV : ℕ} (τv : F ≃ Fin nF) (τf : V ≃ Fin nV)
    (hFm : nF ≤ m) (hVm : nV ≤ m) {T₀ : DTree M} {ts : List F} {C₀ : DTree M.dual} {cs : List V}
    (hts : ts.length ≤ m) (hcs : cs.length ≤ m) {d₀ d₁ : D}
    {mem mem' : ℕ → ℕ} {Sb ib : ℕ}
    (hK : KInM M.dual (enEq h) (fun x => 1 + (τv x : ℕ)) (ιG M h)
      (fun y => 2 * m + 1 + (τf y : ℕ)) (ιE M h) mem (Sb + 3 * m))
    (hG0 : mem (Sb + 15 * m + 1) = enEq h d₁) (hG1 : mem (Sb + 15 * m + 2) = enEq h d₀)
    (hIV : ∀ i (hi : i < ((List.finRange nF).map τv.symm).length),
      mem (Sb + 24 * m + 5 + i) = 1 + τv ((List.finRange nF).map τv.symm)[i])
    (hIT : ∀ i (hi : i < ts.length),
      mem (Sb + 24 * m + 5 + (4 * m + 1) + i) = enEq h (T₀.par ts[i]))
    (hIF : ∀ i (hi : i < ((List.finRange nV).map τf.symm).length),
      mem (Sb + 24 * m + 5 + 2 * (4 * m + 1) + i) =
        2 * m + 1 + τf ((List.finRange nV).map τf.symm)[i])
    (hIC : ∀ i (hi : i < cs.length),
      mem (Sb + 24 * m + 5 + 3 * (4 * m + 1) + i) = enEq h (C₀.par cs[i]))
    (hH0 : mem (Sb + 24 * m + 5 + 4 * (4 * m + 1)) = ((List.finRange nF).map τv.symm).length)
    (hH1 : mem (Sb + 24 * m + 5 + 4 * (4 * m + 1) + 1) = ts.length)
    (hH2 : mem (Sb + 24 * m + 5 + 4 * (4 * m + 1) + 2) = ((List.finRange nV).map τf.symm).length)
    (hH3 : mem (Sb + 24 * m + 5 + 4 * (4 * m + 1) + 3) = cs.length)
    (hcl : ∀ i < 37 * m + 13, mem' (ib + i) = min (mem (Sb + 3 * m + i)) (101 * m + 45)) :
    KInM M.dual (enEq h) (fun x => 1 + (τv x : ℕ)) (ιG M h)
      (fun y => 2 * m + 1 + (τf y : ℕ)) (ιE M h) mem' ib ∧
    mem' (ib + (12 * m + 1)) = enEq h d₁ ∧ mem' (ib + (12 * m + 1) + 1) = enEq h d₀ ∧
    (∀ i (hi : i < ((List.finRange nF).map τv.symm).length),
      mem' (ib + (21 * m + 5) + i) = 1 + τv ((List.finRange nF).map τv.symm)[i]) ∧
    (∀ i (hi : i < ts.length),
      mem' (ib + (21 * m + 5) + (4 * m + 1) + i) = enEq h (T₀.par ts[i])) ∧
    (∀ i (hi : i < ((List.finRange nV).map τf.symm).length),
      mem' (ib + (21 * m + 5) + 2 * (4 * m + 1) + i) =
        2 * m + 1 + τf ((List.finRange nV).map τf.symm)[i]) ∧
    (∀ i (hi : i < cs.length),
      mem' (ib + (21 * m + 5) + 3 * (4 * m + 1) + i) = enEq h (C₀.par cs[i])) ∧
    mem' (ib + (21 * m + 5) + 4 * (4 * m + 1)) = ((List.finRange nF).map τv.symm).length ∧
    mem' (ib + (21 * m + 5) + 4 * (4 * m + 1) + 1) = ts.length ∧
    mem' (ib + (21 * m + 5) + 4 * (4 * m + 1) + 2) = ((List.finRange nV).map τf.symm).length ∧
    mem' (ib + (21 * m + 5) + 4 * (4 * m + 1) + 3) = cs.length ∧
    (∀ i < 37 * m + 13, mem' (ib + i) ≤ 101 * m + 45) := by
  have hσ : ∀ d, (enEq h d : ℕ) < m := fun d => (enEq h d).2
  have cl : ∀ k < 37 * m + 13, ∀ v, mem (Sb + 3 * m + k) = v → v ≤ 101 * m + 45 →
      mem' (ib + k) = v := fun k hk v hv hb => by
    rw [hcl k hk, hv]; omega
  have hlF : ((List.finRange nF).map τv.symm).length = nF := by simp
  have hlV : ((List.finRange nV).map τf.symm).length = nV := by simp
  refine ⟨hK.clamp (E := 4 * m + 1) (ιE_lt h) (by omega) (fun x => by have := (τv x).2; omega)
      (fun d => by have := NegSSSP.eIx_lt (M := M) (enEq h) d; unfold ιG; omega)
      (fun y => by have := (τf y).2; omega) (fun d => by have := ιE_lt h d; omega)
      (fun i hi => hcl i (by omega)), ?_, ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_, ?_, ?_, ?_, ?_, fun i hi => (hcl i hi).trans_le (min_le_right _ _)⟩
  · exact cl _ (by omega) _ (by rw [show Sb + 3 * m + (12 * m + 1) = Sb + 15 * m + 1 by omega,
      hG0]) (by have := hσ d₁; omega)
  · rw [add_assoc]
    exact cl _ (by omega) _ (by rw [show Sb + 3 * m + (12 * m + 1 + 1) = Sb + 15 * m + 2 by omega,
      hG1]) (by have := hσ d₀; omega)
  · rw [add_assoc]
    have hi' := hi; rw [hlF] at hi'
    exact cl _ (by omega) _ (by rw [show Sb + 3 * m + (21 * m + 5 + i) = Sb + 24 * m + 5 + i by
      omega, hIV i hi]) (by have := (τv ((List.finRange nF).map τv.symm)[i]).2; omega)
  · rw [add_assoc, add_assoc]
    exact cl _ (by omega) _ (by rw [show Sb + 3 * m + (21 * m + 5 + ((4 * m + 1) + i)) =
      Sb + 24 * m + 5 + (4 * m + 1) + i by omega, hIT i hi]) (by have := hσ (T₀.par ts[i]); omega)
  · rw [add_assoc, add_assoc]
    have hi' := hi; rw [hlV] at hi'
    exact cl _ (by omega) _ (by rw [show Sb + 3 * m + (21 * m + 5 + (2 * (4 * m + 1) + i)) =
      Sb + 24 * m + 5 + 2 * (4 * m + 1) + i by omega, hIF i hi])
      (by have := (τf ((List.finRange nV).map τf.symm)[i]).2; omega)
  · rw [add_assoc, add_assoc]
    exact cl _ (by omega) _ (by rw [show Sb + 3 * m + (21 * m + 5 + (3 * (4 * m + 1) + i)) =
      Sb + 24 * m + 5 + 3 * (4 * m + 1) + i by omega, hIC i hi])
      (by have := hσ (C₀.par cs[i]); omega)
  · rw [add_assoc]
    exact cl _ (by omega) _ (by rw [show Sb + 3 * m + (21 * m + 5 + 4 * (4 * m + 1)) =
      Sb + 24 * m + 5 + 4 * (4 * m + 1) by omega, hH0]) (by rw [hlF]; omega)
  · rw [add_assoc, add_assoc]
    exact cl _ (by omega) _ (by rw [show Sb + 3 * m + (21 * m + 5 + (4 * (4 * m + 1) + 1)) =
      Sb + 24 * m + 5 + 4 * (4 * m + 1) + 1 by omega, hH1]) (by omega)
  · rw [add_assoc, add_assoc]
    exact cl _ (by omega) _ (by rw [show Sb + 3 * m + (21 * m + 5 + (4 * (4 * m + 1) + 2)) =
      Sb + 24 * m + 5 + 4 * (4 * m + 1) + 2 by omega, hH2]) (by rw [hlV]; omega)
  · rw [add_assoc, add_assoc]
    exact cl _ (by omega) _ (by rw [show Sb + 3 * m + (21 * m + 5 + (4 * (4 * m + 1) + 3)) =
      Sb + 24 * m + 5 + 4 * (4 * m + 1) + 3 by omega, hH3]) (by omega)

/-- **The parameter bound** is at most `ib + pstWN W₀ H` when `H ≥ 4m + 2`. -/
theorem wz_bound {m H ib : ℕ} (hH : 4 * m + 2 ≤ H) :
    7 * (4 * m + 1) + 9 * m + (37 * m + 13) + pstM H + H + (101 * m + 46) + ib +
      (37 * m + 13) + 16 ≤ ib + pstWN (101 * m + 45) H := by
  unfold pstWN
  have e : pstM H = 2 * H + 1 := rfl
  have : 2 * pstM H ≤ pstM H * pstM H := Nat.mul_le_mul_right _ (by omega)
  omega

end StCall

end BKMNW

end PlanarFlow
