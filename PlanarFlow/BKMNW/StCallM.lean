module

public import PlanarFlow.BKMNW.StIsoG

/-!
# The s-t flow of explicit choices from the fixed natural program

`pcore_sNFM` (`StNat.lean`) with the data of the s-t flow of `X` to `Y` (`pstflowT`): the
capacities `capR c X Y`, the restriction `RS = 1 - [Inside]`, a perturbation `isoEpsG V F w` of an
isolating weight `w` of the sink (`StIsoG.lean`; e.g. `MSSP.treeW` of a spanning tree rooted at the
sink, `isIsoW_treeW`) and `N = 2 lexR + 1`:

* `rsIn M X Y d = if Inside M X Y d then 0 else 1`, `rsIn_mul` (`rsIn · g = restrictR M X Y g`);
* **`st_sNFM`**: `sNFM` ends with words whose signed values (`sdec`) are exactly
  **`pstflowT M (isoEpsG V F w) c X Y s d₀ T₀`**, within `3 (4 · pcoreB + 3)` steps, the modulus
  bounded by the word-size bound `pstH n m #F #V isoW_bound` (`stH_le`);
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW Klein DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs WordRAM.Machine.ModNat

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {nD : ℕ} {σ : D ≃ Fin nD} {n : ℕ} {ιF : F → ℕ} {ιG : D → ℕ}
  {ιV : V → ℕ} {ιE : D → ℕ} {P : Input} {B : ℕ}

variable (M) in
/-- The restriction word of a dart: `0` inside `X` or inside `Y`, `1` elsewhere. -/
def rsIn (X Y : Finset V) (d : D) : ℤ := if Inside M X Y d then 0 else 1

lemma rsIn_mul (X Y : Finset V) (g : D → ℤ) (d : D) :
    rsIn M X Y d * g d = restrictR M X Y g d := by
  unfold rsIn restrictR; split_ifs <;> simp

lemma rsIn_bd (X Y : Finset V) (d : D) : 0 ≤ rsIn M X Y d ∧ rsIn M X Y d ≤ 1 := by
  unfold rsIn; split_ifs <;> simp

/-- The constant `N = 2 lexR + 1` of the perturbation `isoEpsG w`. -/
def stN (w : D → ℤ) : ℤ := 2 * lexR F (isoEpsG V F w) + 1

/-- **The modulus is bounded by the word-size bound**: `pcoreH ≤ pstH n m #F #V isoW_bound`. -/
theorem stH_le (hM : M.IsPlane) {w : D → ℤ} {t : V} (hw : IsIsoW M t w) {c : D → ℤ}
    (hc : ∀ d, 0 ≤ c d) (n : ℕ) :
    pcoreH D V F n (stN (V := V) (F := F) w) c (isoEpsG V F w) ≤
      pstH n (Fintype.card D) (Fintype.card F) (Fintype.card V) (isoW_bound D V F c).toNat :=
  pstH_mono (Int.toNat_le_toNat (kH0_isoG_le hM hw hc))

set_option maxHeartbeats 1000000 in
/-- **The s-t flow of explicit choices from the fixed natural program.** On a plane map with
transitive rotations and faces, capacities `c ≥ 0`, disjoint `X`, `Y`, a source `s = tail d₁ ∈ X`,
a dart `d₀` with tail `t ∈ Y`, an isolating weight `w` of `t`, a dual tree `T₀` rooted at the face
of `d₀` meeting `LInv` for `capR c X Y`, `ε = isoEpsG V F w`, and the input `P` and the machine
configuration `d` of `pcore_sNFM` (capacities `capR c X Y`, restriction `rsIn`): `sNFM` runs within
`3 (4 · pcoreB + 3)` steps and the signed values of its words at `W + 1 + OUT + σ e` are
`pstflowT M ε c X Y s d₀ T₀ e`. -/
theorem st_sNFM (hWa : 9 * nD + 7 * n + 6 ≤ B) (hB : n + 2 * nD ≤ B) (hB7 : 7 * nD + 3 ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ B + 16 * (n + 1)) (hM : M.IsPlane) (hrot : M.RotTrans)
    (hface : M.FaceTrans) {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) {X Y : Finset V} (hXY : Disjoint X Y)
    {d₀ d₁ : D} (hd₁ : M.tail d₁ ∈ X) (hd₀ : M.tail d₀ ∈ Y) {w : D → ℤ}
    (hw : IsIsoW M (M.tail d₀) w) {T₀ : DTree M} (hroot : T₀.root = M.face d₀)
    (hI₀ : LInv (capR M c X Y) (isoEpsG V F w) (M.tail d₁) (M.tail d₀)
      (tSt M (capR M c X Y) (isoEpsG V F w) T₀))
    (hL : Layout M.dual n ιF ιG ιV ιE)
    (hK : KInput M.dual ∅ 0 σ ιF ιG ιV ιE P)
    (hG : KBnd 2 (fun i => if i = 0 then d₁ else d₀) σ n P) {C₀ : DTree M.dual}
    {vs ts : List F} {fs cs : List V} (hI : KInit M.dual σ ιF ιV n 2 (toDD T₀) C₀ vs ts fs cs P)
    (hoff : ∀ x, x ≠ C₀.root → ¬ (toDD T₀).InT (C₀.par x)) (hCr : C₀.root = M.tail d₁)
    (P' : Input) {W' ib : ℕ} {d : Config} (hd : WordsBounded W' d)
    (hWW : pstWN (B + 16 * (n + 1))
      (pcoreH D V F n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)) ≤ W')
    (hdr4 : ∀ r < 406, d.nreg r ≤ pstWN (B + 16 * (n + 1))
      (pcoreH D V F n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)))
    (hdm4 : ∀ a ≤ pstWN (B + 16 * (n + 1))
        (pcoreH D V F n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)),
      d.nmem a ≤ pstWN (B + 16 * (n + 1))
        (pcoreH D V F n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)))
    (hdr : ∀ r < 201, d.nreg r ≤ B + 16 * (n + 1))
    (hdm : ∀ a ≤ B + 16 * (n + 1), d.nmem a ≤ B + 16 * (n + 1))
    (hrr : ∀ r < 201, d.nreg (201 + r) <
      pstM (pcoreH D V F n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)))
    (hrm : ∀ a ≤ B + 16 * (n + 1), d.nmem (B + 16 * (n + 1) + 1 + a) <
      pstM (pcoreH D V F n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)))
    (hwt : ∀ e, d.nmem (B + 16 * (n + 1) + 1 + (aWT + σ e)) =
      zres (pstM (pcoreH D V F n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)))
        (wlen (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w) e))
    (hph : ∀ e, d.nmem (B + 16 * (n + 1) + 1 + (aPH nD + σ e)) =
      zres (pstM (pcoreH D V F n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)))
        (wlen (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w) e))
    (hcp : ∀ e, d.nmem (B + 16 * (n + 1) + 1 + (aCP nD + σ e)) =
      zres (pstM (pcoreH D V F n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)))
        (capR M c X Y e))
    (hrsm : ∀ e, d.nmem (B + 16 * (n + 1) + 1 + (aRS nD + σ e)) =
      zres (pstM (pcoreH D V F n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)))
        (rsIn M X Y e))
    (hth : d.nmem (B + 16 * (n + 1) + 1 + aTH nD) =
      zres (pstM (pcoreH D V F n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)))
        (kTh D F (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)))
    (hh0 : d.nmem (B + 16 * (n + 1) + 1 + aH0 nD) =
      zres (pstM (pcoreH D V F n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)))
        (kH0 D F (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)))
    (hIn : InData P (pstWN (B + 16 * (n + 1))
      (pcoreH D V F n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w))) ib
        P.data.length W' d)
    (hv : ∀ j < 45, d.nreg (1000 + j) = StFix.sVM B nD n
      (pcoreH D V F n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w))
      (B + 16 * (n + 1) + 1) ib P.data.length j) :
    ∃ d' k', Exec P' W' StFix.sNFM d d' k' ∧ k' ≤ 3 * (4 * pcoreB V F nD n + 3) ∧
      (∀ e, sdec (pstM (pcoreH D V F n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)))
        (pcoreH D V F n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w))
        (d'.nmem (B + 16 * (n + 1) + 1 + (aOT nD + σ e))) =
          pstflowT M (isoEpsG V F w) c X Y (M.tail d₁) d₀ T₀ e) ∧
      (∀ r, 406 ≤ r → r ≠ 999 → d'.nreg r = d.nreg r) ∧
      (∀ r, 406 ≤ r → d'.rreg r = d.rreg r) ∧
      (∀ a, pstWN (B + 16 * (n + 1))
        (pcoreH D V F n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)) < a →
          d'.nmem a = d.nmem a) ∧
      (∀ a, pstWN (B + 16 * (n + 1))
        (pcoreH D V F n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)) < a →
          d'.rmem a = d.rmem a) ∧
      d'.output = d.output := by
  have hst : M.tail d₁ ≠ M.tail d₀ := fun h => disjoint_left.1 hXY hd₁ (h ▸ hd₀)
  have hc' : ∀ e, 0 ≤ capR M c X Y e := capR_nonneg hc X Y
  have hPO : PertOK M (capR M c X Y) (isoEpsG V F w) (M.tail d₁) (M.tail d₀) d₀ :=
    pertOK_isoG hM hrot hface hc' hst hw rfl
  have hN : 2 * lexR F (isoEpsG V F w) < stN (V := V) (F := F) w := by unfold stN; omega
  obtain ⟨d', k', ex, hk, hOUT, h1, h2, h3, h4, h5⟩ := pcore_sNFM hWa hB hB7 hP hM hc' hst rfl rfl
    hPO hroot hI₀ hN hL hK hG hI hoff hCr (rsIn_bd X Y) P' hd hWW hdr4 hdm4 hdr hdm hrr hrm hwt hph
    hcp hrsm hth hh0 hIn hv
  refine ⟨d', k', ex, hk, fun e => ?_, h1, h2, h3, h4, h5⟩
  rw [hOUT e, sdec_flow hM hc' hst hPO hI₀ hN (rsIn_bd X Y) e, rsIn_mul]
  rfl

end STFlow

end PlanarFlow
