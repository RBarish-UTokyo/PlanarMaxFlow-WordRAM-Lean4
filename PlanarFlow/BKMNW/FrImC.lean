module

public import PlanarFlow.BKMNW.FrImB

/-!
# The FR image, part C: the cells of the image

The cells of the natural image `frNM` and of the residues `frRS` of `frPrm b Dm pm r ET EH Lz mE`
region by region (`frNM_lo`, `frNM_off`, `frNM_dst`, `frNM_hi`, `frRS_D`, `frRS_p`, `frRS_mid`,
`frRS_len`), and the explicit arcs of the layout through the indices sorted by `osProg`
(`pre_fiL_map`: the arcs tail by tail are the sorted indices mapped to their arcs).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MsCall

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge Monge.FR NegSSSP

/-! ### The arcs through the sorted indices -/

/-- The arc of an index. -/
def fiArc (EH : ℕ → ℕ) (Lz : ℕ → ℤ) (a : ℕ × ℕ × ℤ) : ℕ × ℕ × ℤ := (a.1, EH a.2.1, Lz a.2.1)

theorem csList_fiL (ET EH : ℕ → ℕ) (Lz : ℕ → ℤ) (n : ℕ) :
    csList ET EH (fun _ => 1) Lz n = (fiL ET n).map (fiArc EH Lz) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [fiL, csList, ih, one_ne_zero, ↓reduceIte, List.map_append, List.map_cons,
      List.map_nil, fiArc, id]

theorem blk_map (EH : ℕ → ℕ) (Lz : ℕ → ℤ) (L : List (ℕ × ℕ × ℤ)) (x : ℕ) :
    FR.blk (L.map (fiArc EH Lz)) x = (FR.blk L x).map (fiArc EH Lz) := by
  simp only [FR.blk, List.filter_map]
  rfl

theorem pre_fiL_map (EH : ℕ → ℕ) (Lz : ℕ → ℤ) (L : List (ℕ × ℕ × ℤ)) (x : ℕ) :
    pre (L.map (fiArc EH Lz)) x = (pre L x).map (fiArc EH Lz) := by
  induction x with
  | zero => rfl
  | succ x ih => rw [pre_succ, pre_succ, ih, blk_map, List.map_append]

theorem length_pre_fiL (ET EH : ℕ → ℕ) (Lz : ℕ → ℤ) (mE x : ℕ) :
    (pre (csList ET EH (fun _ => 1) Lz mE) x).length = (pre (fiL ET mE) x).length := by
  rw [csList_fiL, pre_fiL_map, List.length_map]

theorem getD_pre_fiL (ET EH : ℕ → ℕ) (Lz : ℕ → ℤ) (mE x e : ℕ)
    (he : e < (pre (fiL ET mE) x).length) :
    (pre (csList ET EH (fun _ => 1) Lz mE) x).getD e (0, 0, 0) =
      fiArc EH Lz ((pre (fiL ET mE) x).getD e (0, 0, 0)) := by
  rw [csList_fiL, pre_fiL_map, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact he),
    List.getD_eq_getElem _ _ he, List.getElem_map]

/-! ### The cells of the image -/

section Cells

variable {b : ℕ} {Dm : ℕ → ℕ → ℕ} {pm : ℕ → ℤ} {r mE : ℕ} {ET EH : ℕ → ℕ} {Lz : ℕ → ℤ}
  {L : ℕ}

theorem frNM_lo (h : ∀ a < mE, ET a < b) {a : ℕ} (ha : a < b * b + b) :
    FrFix.frNM (frPrm b Dm pm r ET EH Lz mE) a = 0 := by
  unfold FrFix.frNM
  rw [frPrm_ob, frPrm_N, frPrm_m h]
  split_ifs <;> first | rfl | omega

theorem frNM_off (h : ∀ a < mE, ET a < b) {x : ℕ} (hx : x ≤ b) :
    FrFix.frNM (frPrm b Dm pm r ET EH Lz mE) (b * b + b + x) = (pre (fiL ET mE) x).length := by
  unfold FrFix.frNM
  rw [frPrm_ob, frPrm_N, frPrm_m h]
  rw [FR.ite_of_pos ⟨by omega, by omega⟩, show b * b + b + x - (b * b + b) = x by omega]
  exact length_pre_fiL ET EH Lz mE x

theorem frNM_dst (h : ∀ a < mE, ET a < b) {e : ℕ} (he : e < mE) :
    FrFix.frNM (frPrm b Dm pm r ET EH Lz mE) (b * b + b + b + 1 + e) =
      EH ((pre (fiL ET mE) b).getD e (0, 0, 0)).2.1 := by
  have hm := frPrm_m (Dm := Dm) (pm := pm) (r := r) (EH := EH) (Lz := Lz) h
  have hlen : e < (pre (fiL ET mE) b).length := by
    have : (frPrm b Dm pm r ET EH Lz mE).m = (pre (fiL ET mE) b).length :=
      length_pre_fiL ET EH Lz mE b
    omega
  unfold FrFix.frNM
  rw [frPrm_ob, frPrm_N, hm, FR.ite_of_neg (by omega), FR.ite_of_pos ⟨by omega, by omega⟩,
    show b * b + b + b + 1 + e - (b * b + b + b + 1) = e by omega]
  show ((arcList b (csList ET EH (fun _ => 1) Lz mE)).getD e (0, 0, 0)).2.1 = _
  rw [arcList, getD_pre_fiL ET EH Lz mE b e hlen]
  rfl

theorem frNM_hi (h : ∀ a < mE, ET a < b) {a : ℕ} (ha : b * b + b + b + 1 + mE ≤ a) :
    FrFix.frNM (frPrm b Dm pm r ET EH Lz mE) a = 0 := by
  unfold FrFix.frNM
  rw [frPrm_ob, frPrm_N, frPrm_m h]
  split_ifs <;> first | rfl | omega

theorem frRS_D (hb : FrImgB b Dm pm r mE ET EH Lz L) {a : ℕ} (ha : a < b * b) :
    FrFix.frRS (frPrm b Dm pm r ET EH Lz mE) L a = Dm (a / b) (a % b) := by
  have hb1 := hb.b_pos
  have hi : a / b < b := by rw [Nat.div_lt_iff_lt_mul (by omega)]; exact ha
  have hj : a % b < b := Nat.mod_lt _ (by omega)
  have hle := hb.dm _ hi _ hj
  unfold FrFix.frRS FrFix.frRZ
  rw [frPrm_Db, frPrm_b, FR.ite_of_pos ⟨by omega, by omega⟩, Nat.sub_zero]
  rw [frM_frPrm]
  show ((((Dm (a / b) (a % b) : ℕ) : ℤ) % ((2 * (6 * ((b + 2) * L)) + 1 : ℕ) : ℤ)).toNat) = _
  have hlt : Dm (a / b) (a % b) < 2 * (6 * ((b + 2) * L)) + 1 := by nlinarith
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hlt), Int.toNat_natCast]

theorem frRS_p (hb : FrImgB b Dm pm r mE ET EH Lz L) {x : ℕ} (hx : x < b) :
    FrFix.frRS (frPrm b Dm pm r ET EH Lz mE) L (b * b + x) =
      (pm x % (frM (frPrm b Dm pm r ET EH Lz mE) L : ℤ)).toNat := by
  unfold FrFix.frRS FrFix.frRZ
  rw [frPrm_Db, frPrm_b, frPrm_pb, frPrm_N, FR.ite_of_neg (by omega), FR.ite_of_pos ⟨by omega, by omega⟩,
    show b * b + x - b * b = x by omega]
  rfl

theorem frRS_mid (hb : FrImgB b Dm pm r mE ET EH Lz L) {a : ℕ} (h1 : b * b + b ≤ a)
    (h2 : a < b * b + b + b + 1 + mE) :
    FrFix.frRS (frPrm b Dm pm r ET EH Lz mE) L a = 0 := by
  unfold FrFix.frRS FrFix.frRZ
  rw [frPrm_Db, frPrm_b, frPrm_pb, frPrm_N, frPrm_lb hb.et, FR.ite_of_neg (by omega), FR.ite_of_neg (by omega),
    FR.ite_of_neg (by omega)]
  rfl

theorem frRS_len (hb : FrImgB b Dm pm r mE ET EH Lz L) {e : ℕ} (he : e < mE) :
    FrFix.frRS (frPrm b Dm pm r ET EH Lz mE) L (b * b + b + b + 1 + mE + e) =
      (Lz ((pre (fiL ET mE) b).getD e (0, 0, 0)).2.1 %
        (frM (frPrm b Dm pm r ET EH Lz mE) L : ℤ)).toNat := by
  have hm := frPrm_m (Dm := Dm) (pm := pm) (r := r) (EH := EH) (Lz := Lz) hb.et
  have hlen : e < (pre (fiL ET mE) b).length := by
    have : (frPrm b Dm pm r ET EH Lz mE).m = (pre (fiL ET mE) b).length :=
      length_pre_fiL ET EH Lz mE b
    omega
  unfold FrFix.frRS FrFix.frRZ
  rw [frPrm_Db, frPrm_b, frPrm_pb, frPrm_N, frPrm_lb hb.et, hm, FR.ite_of_neg (by omega),
    FR.ite_of_neg (by omega), FR.ite_of_pos ⟨by omega, by omega⟩,
    show b * b + b + b + 1 + mE + e - (b * b + b + b + 1 + mE) = e by omega]
  show ((((arcList b (csList ET EH (fun _ => 1) Lz mE)).getD e (0, 0, 0)).2.2 %
    (frM (frPrm b Dm pm r ET EH Lz mE) L : ℤ)).toNat) = _
  rw [arcList, getD_pre_fiL ET EH Lz mE b e hlen]
  rfl

end Cells

end MsCall

end BKMNW

end PlanarFlow
