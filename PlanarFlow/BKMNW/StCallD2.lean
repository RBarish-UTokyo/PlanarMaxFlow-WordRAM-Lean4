module

public import PlanarFlow.BKMNW.StCallD1

/-!
# The run stage of the s-t flow call, part 2: the logged run

**`stD2_exec`**: from a configuration `e` whose registers `< 1000` are zero, whose `r1000 + j`
hold the parameters `sVM` of `sNFM`, with the log registers `r9150 = p > Wz`, `r9151 = 1`, the
encoded input (map words, terminal darts, the `KInit` words) at `ib` (`pstWN W₀ H < ib`,
`ib + pstWN W₀ H ≤ Wz`, zero above `len` up to `pstWN`), the residues at `β₀` and the rest of the
memory `≤ W₀` zero, the logged run `stD2 = lgS 9150 9151 sNFM` (the reference run of
`STFlow.st_sNFM_mem` from the configuration cut to the registers `< 1045` and the memory `≤ Wz`,
lifted by `StFix.sNFM_lgRun`) ends within `3 · 3 (4 · pcoreB + 3)` steps with the signed values
of the output words at `β₀ + 6m + 3 + i` equal to the s-t flow `pstflowT M (isoEpsG (treeW C)) c X
Y (tail d₁) d₀ T₀ (en i)`, the frame `LgKeep` (the log at `p`, the registers `≥ 1045` but `9150`
kept), the memory `≤ Wz` bounded by `Wz`.
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

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 2000000 in
/-- **The logged run** (see the module docstring). -/
theorem stD2_exec (hM : M.IsPlane) (hrot : M.RotTrans) (h : EnumOK M en m)
    (h' : EnumOK M.dual en m) (hm : 0 < m) {cp : D → ℤ} (hcp : ∀ d, 0 ≤ cp d) {X Y : Finset V}
    (hXY : Disjoint X Y) {d₀ d₁ : D} (hd₁ : M.tail d₁ ∈ X) (hd₀ : M.tail d₀ ∈ Y)
    {C : DTree M.dual} (hCr : C.root = M.tail d₀) {T₀ : DTree M} (hroot : T₀.root = M.face d₀)
    (hLI : LInv (capR M cp X Y) (isoEpsG V F (MSSP.treeW C)) (M.tail d₁) (M.tail d₀)
      (tSt M (capR M cp X Y) (isoEpsG V F (MSSP.treeW C)) T₀))
    {nF nV : ℕ} (τv : F ≃ Fin nF) (τf : V ≃ Fin nV)
    {C₀ : DTree M.dual} {ts : List F} {cs : List V}
    (hOT : Klein.Orders (toDD T₀) ((List.finRange nF).map τv.symm) ts)
    (hOC : Klein.Orders C₀ ((List.finRange nV).map τf.symm) cs)
    (hoff : ∀ x, x ≠ C₀.root → ¬ (toDD T₀).InT (C₀.par x)) (hC₀ : C₀.root = M.tail d₁)
    (e : Config) (he : WordsBounded W e) {ib p Wz H : ℕ}
    (hH : H = pcoreH D V F (4 * m + 1) (stN (V := V) (F := F) (MSSP.treeW C)) (capR M cp X Y)
      (isoEpsG V F (MSSP.treeW C)))
    (z1 : ∀ r < 1000, e.nreg r = 0)
    (zv : ∀ j < 45, e.nreg (1000 + j) =
      StFix.sVM (37 * m + 13) m (4 * m + 1) H (101 * m + 46) ib (37 * m + 13) j)
    (z50 : e.nreg 9150 = p) (z51 : e.nreg 9151 = 1)
    (hKM : KInM M.dual (enEq h) (fun x => 1 + (τv x : ℕ)) (ιG M h)
      (fun y => 2 * m + 1 + (τf y : ℕ)) (ιE M h) e.nmem ib)
    (hG0 : e.nmem (ib + (12 * m + 1)) = enEq h d₁)
    (hG1 : e.nmem (ib + (12 * m + 1) + 1) = enEq h d₀)
    (hIV : ∀ i (hi : i < ((List.finRange nF).map τv.symm).length),
      e.nmem (ib + (21 * m + 5) + i) = 1 + τv ((List.finRange nF).map τv.symm)[i])
    (hIT : ∀ i (hi : i < ts.length),
      e.nmem (ib + (21 * m + 5) + (4 * m + 1) + i) = enEq h (T₀.par ts[i]))
    (hIF : ∀ i (hi : i < ((List.finRange nV).map τf.symm).length),
      e.nmem (ib + (21 * m + 5) + 2 * (4 * m + 1) + i) =
        2 * m + 1 + τf ((List.finRange nV).map τf.symm)[i])
    (hIC : ∀ i (hi : i < cs.length),
      e.nmem (ib + (21 * m + 5) + 3 * (4 * m + 1) + i) = enEq h (C₀.par cs[i]))
    (hH0 : e.nmem (ib + (21 * m + 5) + 4 * (4 * m + 1)) = ((List.finRange nF).map τv.symm).length)
    (hH1 : e.nmem (ib + (21 * m + 5) + 4 * (4 * m + 1) + 1) = ts.length)
    (hH2 : e.nmem (ib + (21 * m + 5) + 4 * (4 * m + 1) + 2) =
      ((List.finRange nV).map τf.symm).length)
    (hH3 : e.nmem (ib + (21 * m + 5) + 4 * (4 * m + 1) + 3) = cs.length)
    (hbd : ∀ i < 37 * m + 13, e.nmem (ib + i) ≤ 101 * m + 45)
    (hwt : ∀ d, e.nmem (101 * m + 46 + (aWT + enEq h d)) = zres (pstM H)
      (STFlow.wlen (stN (V := V) (F := F) (MSSP.treeW C)) (capR M cp X Y)
        (isoEpsG V F (MSSP.treeW C)) d))
    (hph : ∀ d, e.nmem (101 * m + 46 + (aPH m + enEq h d)) = zres (pstM H)
      (STFlow.wlen (stN (V := V) (F := F) (MSSP.treeW C)) (capR M cp X Y)
        (isoEpsG V F (MSSP.treeW C)) d))
    (hcp' : ∀ d, e.nmem (101 * m + 46 + (aCP m + enEq h d)) = zres (pstM H) (capR M cp X Y d))
    (hrs : ∀ d, e.nmem (101 * m + 46 + (aRS m + enEq h d)) = zres (pstM H) (rsIn M X Y d))
    (hth : e.nmem (101 * m + 46 + aTH m) = zres (pstM H)
      (kTh D F (stN (V := V) (F := F) (MSSP.treeW C)) (capR M cp X Y)
        (isoEpsG V F (MSSP.treeW C))))
    (hh0 : e.nmem (101 * m + 46 + aH0 m) = zres (pstM H)
      (kH0 D F (stN (V := V) (F := F) (MSSP.treeW C)) (capR M cp X Y)
        (isoEpsG V F (MSSP.treeW C))))
    (z0 : ∀ a ≤ 101 * m + 45, e.nmem a = 0)
    (zr : ∀ a ≤ 101 * m + 45, e.nmem (101 * m + 46 + a) < pstM H)
    (zw : ∀ a ≤ pstWN (101 * m + 45) H, e.nmem a ≤ pstWN (101 * m + 45) H)
    (zz : ∀ a ≤ Wz, e.nmem a ≤ Wz)
    (hz : ∀ i, 37 * m + 13 ≤ i → i ≤ pstWN (101 * m + 45) H → e.nmem (ib + i) = 0)
    (hlt : pstWN (101 * m + 45) H < ib) (hle : ib + pstWN (101 * m + 45) H ≤ Wz)
    (hVz : 7 * (4 * m + 1) + 9 * m + (37 * m + 13) + pstM H + H + (101 * m + 46) + ib +
      (37 * m + 13) + 16 ≤ Wz)
    (hp : Wz < p) (hpW : p + 3 * (4 * pcoreB V F m (4 * m + 1) + 3) ≤ W) (hWz : Wz ≤ W) :
    ∃ e' t j, Exec P W stD2 e e' t ∧ t ≤ 3 * (3 * (4 * pcoreB V F m (4 * m + 1) + 3)) ∧
      j ≤ 3 * (4 * pcoreB V F m (4 * m + 1) + 3) ∧
      (∀ i < m, sdec (pstM H) H (e'.nmem (107 * m + 49 + i)) =
        pstflowT M (isoEpsG V F (MSSP.treeW C)) cp X Y (M.tail d₁) d₀ T₀ (en i)) ∧
      LgKeep (fun r => decide (r < 1045)) Wz 9150 p j e e' ∧
      (∀ a ≤ Wz, e'.nmem a ≤ Wz) ∧
      e'.rreg = e.rreg ∧ e'.rmem = e.rmem ∧ e'.output = e.output := by
  classical
  have hface : M.FaceTrans := h.ft
  set U : ℕ → Bool := fun r => decide (r < 1045) with hU
  set d := trunc U Wz e with hd
  have hdr : ∀ r < 1045, d.nreg r = e.nreg r := fun r hr => by simp [hd, trunc, hU, hr]
  have hdm : ∀ a ≤ Wz, d.nmem a = e.nmem a := fun a ha => by simp [hd, trunc, ha]
  have hWN : 202 * m + 91 + pstM H ≤ pstWN (101 * m + 45) H := by unfold pstWN; omega
  -- the bound of the cut configuration
  have hdB : WordsBounded Wz d := wordsBounded_trunc (fun r hr => by
      have hr' : r < 1045 := by simpa [hU] using hr
      by_cases h1 : r < 1000
      · rw [z1 r h1]; exact Nat.zero_le _
      · have := zv (r - 1000) (by omega)
        rw [show 1000 + (r - 1000) = r by omega] at this
        rw [this]
        exact (StFix.sVM_le (by omega)).trans hVz) zz
  have hcF : Fintype.card F = nF := by rw [Fintype.card_congr τv, Fintype.card_fin]
  have hcV : Fintype.card V = nV := by rw [Fintype.card_congr τf, Fintype.card_fin]
  have hFm : nF ≤ m := hcF ▸ card_F_le h
  have hVm : nV ≤ m := hcV ▸ card_V_le h'
  have hw : IsIsoW M (M.tail d₀) (MSSP.treeW C) := by rw [← hCr]; exact isIsoW_treeW C
  have eB : 37 * m + 13 + 16 * (4 * m + 1 + 1) + 1 = 101 * m + 46 := by ring
  have eB' : 37 * m + 13 + 16 * (4 * m + 1 + 1) = 101 * m + 45 := by ring
  have eL : iHD m (4 * m + 1) 2 + 4 = 37 * m + 13 := by unfold iHD iIV; ring
  have eG : iGB m (4 * m + 1) = 12 * m + 1 := by unfold iGB; ring
  have eI : iIV m (4 * m + 1) 2 = 21 * m + 5 := by unfold iIV; ring
  -- the reference run
  obtain ⟨d', k', ex, hk, hOUT, -, -, -, -, ho⟩ :=
    st_sNFM_mem (M := M) (σ := enEq h) (n := 4 * m + 1) (B := 37 * m + 13) (ib := ib) (W' := Wz)
      (ιF := fun x => 1 + (τv x : ℕ)) (ιG := ιG M h) (ιV := fun y => 2 * m + 1 + (τf y : ℕ))
      (ιE := ιE M h) (by omega) (by omega) (by omega) hM hrot hface hcp hXY hd₁ hd₀ hw hroot
      hLI (smLayoutC h (gv := fun x => (τv x : ℕ)) (gf := fun y => (τf y : ℕ))
        (fun x y e' => τv.injective (Fin.ext e')) (fun x y e' => τf.injective (Fin.ext e'))
        (fun x => by have := (τv x).2; omega) (fun y => by have := (τf y).2; omega) le_rfl)
      τv τf (fun x => rfl) (fun v => rfl) (by omega) (by omega)
      (fun e' => by have := ιE_lt h e'; omega) hOT hOC hoff hC₀ P hdB
      (by
        refine hKM.move (β' := ib) (E := 4 * m + 1) (ιE_lt h) (fun i hi => ?_)
        rw [hdm _ (by omega)])
      (by rw [eG, hdm _ (by omega)]; exact hG0)
      (by rw [eG, hdm _ (by omega)]; exact hG1)
      (fun i hi => by rw [eI, hdm _ (by simp at hi; omega)]; exact hIV i hi)
      (fun i hi => by
        have := hOT.ylen
        rw [eI, hdm _ (by rw [hcF] at this; omega)]; exact hIT i hi)
      (fun i hi => by rw [eI, hdm _ (by simp at hi; omega)]; exact hIF i hi)
      (fun i hi => by
        have := hOC.ylen
        rw [eI, hdm _ (by rw [hcV] at this; omega)]; exact hIC i hi)
      (by rw [eI, hdm _ (by omega)]; exact hH0) (by rw [eI, hdm _ (by omega)]; exact hH1)
      (by rw [eI, hdm _ (by omega)]; exact hH2) (by rw [eI, hdm _ (by omega)]; exact hH3)
      (fun i hi => by rw [eL] at hi; rw [eB', hdm _ (by omega)]; exact hbd i hi)
      (by rw [eB', ← hH]; omega)
      (fun r hr => by rw [eB', ← hH, hdr r (by omega), z1 r (by omega)]; exact Nat.zero_le _)
      (fun a ha => by
        rw [eB', ← hH] at ha ⊢; rw [hdm a (by omega)]; exact zw a ha)
      (fun r hr => by rw [eB', hdr r (by omega), z1 r (by omega)]; exact Nat.zero_le _)
      (fun a ha => by rw [eB'] at ha ⊢; rw [hdm a (by omega), z0 a ha]; exact Nat.zero_le _)
      (fun r hr => by
        rw [← hH, hdr _ (by omega), z1 _ (by omega)]; unfold pstM; omega)
      (fun a ha => by
        rw [eB'] at ha; rw [eB, ← hH, hdm _ (by omega)]; exact zr a ha)
      (fun d => by rw [eB, ← hH, hdm _ (by have := (enEq h d).2; unfold aWT; omega)]; exact hwt d)
      (fun d => by rw [eB, ← hH, hdm _ (by have := (enEq h d).2; unfold aPH; omega)]; exact hph d)
      (fun d => by rw [eB, ← hH, hdm _ (by have := (enEq h d).2; unfold aCP; omega)]; exact hcp' d)
      (fun d => by rw [eB, ← hH, hdm _ (by have := (enEq h d).2; unfold aRS; omega)]; exact hrs d)
      (by rw [eB, ← hH, hdm _ (by unfold aTH; omega)]; exact hth)
      (by rw [eB, ← hH, hdm _ (by unfold aH0; omega)]; exact hh0)
      (by rw [eB', ← hH]; exact hlt) (by rw [eB', ← hH]; exact hle)
      (fun i h1 h2 => by
        rw [eL] at h1; rw [eB', ← hH] at h2; rw [hdm _ (by omega)]; exact hz i h1 h2)
      (fun j hj => by
        rw [eB, ← hH, eL, hdr _ (by omega)]; exact zv j hj)
  -- the logged run
  obtain ⟨e', s', j, ex', hs', hj, hA', hm', hK, hr, hrm, L, o1, o2⟩ :=
    StFix.sNFM_lgRun (P' := P) ex (LP := 9150) (ONE := 9151) (by omega) (by omega) (by omega)
      hWz e (fun r hr => (hdr r hr).symm) (fun a ha => (hdm a ha).symm) he z51
      (by rw [z50]; exact hp) (by rw [z50]; omega)
  rw [z50] at hK
  have hL : L = [] := by
    have : d.output = e.output := rfl
    rw [ho] at o1; simpa using o1.symm
  refine ⟨e', s', j, ex', by omega, by omega, fun i hi => ?_, hK, fun a ha => ?_, hr, hrm,
    by rw [o2, hL, List.append_nil]⟩
  · have := hOUT (en i)
    rw [eB, ← hH] at this
    have e1 : ((enEq h (en i)) : ℕ) = i := ixOf_en h hi
    rw [e1] at this
    rw [hm' _ (by omega)]
    rw [show 107 * m + 49 + i = 101 * m + 46 + (aOT m + i) by simp only [aOT]; omega]
    exact this
  · rw [hm' a ha]; exact WordsBounded.nmem ex.wb_right a

end StCall

end BKMNW

end PlanarFlow
