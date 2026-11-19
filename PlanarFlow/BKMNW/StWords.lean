module

public import PlanarFlow.BKMNW.StCallM
public import PlanarFlow.BKMNW.StKInit
public import PlanarFlow.BKMNW.StTreeM

/-!
# The s-t flow call from the words in memory

`STFlow.st_sNFM` takes Klein's input `P` of the s-t flow (`KInput`, `KBnd`, `KInit`) and its image
in memory at `ib` (`InData`) as hypotheses. Here `P` is **the image itself**
(`memIn mem ib len`, `len = iHD nD n 2 + 4`), and these hypotheses are discharged from the
words the encoders write:

* `memIn`, `memIn_getD`, **`inData_memIn`** (the words above `len` up to the word bound zero);
* **`st_sNFM_mem`**: `st_sNFM` with, instead of `hP`, `hK`, `hG`, `hI`, `hIn`: the compact map
  words `KInM M.dual σ ιF ιG ιV ιE` at `ib` (`cmProg_kin`, `ιF = 1 + τv`, `ιV = ofF + τf`), the
  terminal darts at `ib + iGB` (`gbProg_exec`), the order words at `ib + iIV nD n 2 + …`
  (`kiProg_exec`), the words bounded and zero above `len`: `sNFM` ends within
  `3 (4 · pcoreB + 3)` steps with `sdec` of its output words equal to
  **`pstflowT M (isoEpsG V F w) c X Y (tail d₁) d₀ T₀`**.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW Klein DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs WordRAM.Machine.ModNat

/-- The input whose words are the memory `[ib, ib + len)`. -/
def memIn (mem : ℕ → ℕ) (ib len : ℕ) : Input := ⟨(List.range len).map (fun i => mem (ib + i)),
  fun _ => 0⟩

theorem memIn_getD (mem : ℕ → ℕ) (ib len i : ℕ) :
    (memIn mem ib len).data.getD i 0 = if i < len then mem (ib + i) else 0 := by
  unfold memIn
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, show len ≤ i by omega]

theorem memIn_length (mem : ℕ → ℕ) (ib len : ℕ) : (memIn mem ib len).data.length = len := by
  simp [memIn]

/-- **The image in memory is the input of the simulation** when the words above `len` (up to
`Wb`) are zero. -/
theorem inData_memIn {Wb ib len W' : ℕ} (d : Config) (hlt : Wb < ib) (hle : ib + Wb ≤ W')
    (hz : ∀ i, len ≤ i → i ≤ Wb → d.nmem (ib + i) = 0) :
    InData (memIn d.nmem ib len) Wb ib (memIn d.nmem ib len).data.length W' d :=
  ⟨hlt, hle, rfl, fun i hi => by
    rw [memIn_getD]
    split_ifs with h
    · rfl
    · exact hz i (by omega) hi⟩

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {nD : ℕ} {σ : D ≃ Fin nD} {n : ℕ} {ιF : F → ℕ} {ιG : D → ℕ}
  {ιV : V → ℕ} {ιE : D → ℕ} {B : ℕ}

set_option maxHeartbeats 1000000 in
/-- **The s-t flow of explicit choices from the words in memory** (see the module docstring). -/
theorem st_sNFM_mem (hWa : 9 * nD + 7 * n + 6 ≤ B) (hB : n + 2 * nD ≤ B) (hB7 : 7 * nD + 3 ≤ B)
    (hM : M.IsPlane) (hrot : M.RotTrans)
    (hface : M.FaceTrans) {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) {X Y : Finset V} (hXY : Disjoint X Y)
    {d₀ d₁ : D} (hd₁ : M.tail d₁ ∈ X) (hd₀ : M.tail d₀ ∈ Y) {w : D → ℤ}
    (hw : IsIsoW M (M.tail d₀) w) {T₀ : DTree M} (hroot : T₀.root = M.face d₀)
    (hI₀ : LInv (capR M c X Y) (isoEpsG V F w) (M.tail d₁) (M.tail d₀)
      (tSt M (capR M c X Y) (isoEpsG V F w) T₀))
    (hL : Layout M.dual n ιF ιG ιV ιE)
    {nF nV ofF : ℕ} (τv : F ≃ Fin nF) (τf : V ≃ Fin nV) (hιF : ∀ x, ιF x = 1 + τv x)
    (hιV : ∀ v, ιV v = ofF + τf v) (hnF : nF ≤ n) (hnV : nV ≤ n) (hE : ∀ e, ιE e < n)
    {C₀ : DTree M.dual} {ts : List F} {cs : List V}
    (hOT : Klein.Orders (toDD T₀) ((List.finRange nF).map τv.symm) ts)
    (hOC : Klein.Orders C₀ ((List.finRange nV).map τf.symm) cs)
    (hoff : ∀ x, x ≠ C₀.root → ¬ (toDD T₀).InT (C₀.par x)) (hCr : C₀.root = M.tail d₁)
    (P' : Input) {W' ib : ℕ} {d : Config} (hd : WordsBounded W' d)
    (hKM : StEnc.KInM M.dual σ ιF ιG ιV ιE d.nmem ib)
    (hG0 : d.nmem (ib + iGB nD n) = σ d₁) (hG1 : d.nmem (ib + iGB nD n + 1) = σ d₀)
    (hIV : ∀ i (h : i < ((List.finRange nF).map τv.symm).length),
      d.nmem (ib + iIV nD n 2 + i) = 1 + τv ((List.finRange nF).map τv.symm)[i])
    (hIT : ∀ i (h : i < ts.length), d.nmem (ib + iIV nD n 2 + n + i) = σ (T₀.par ts[i]))
    (hIF : ∀ i (h : i < ((List.finRange nV).map τf.symm).length),
      d.nmem (ib + iIV nD n 2 + 2 * n + i) = ofF + τf ((List.finRange nV).map τf.symm)[i])
    (hIC : ∀ i (h : i < cs.length), d.nmem (ib + iIV nD n 2 + 3 * n + i) = σ (C₀.par cs[i]))
    (hH0 : d.nmem (ib + iIV nD n 2 + 4 * n) = ((List.finRange nF).map τv.symm).length)
    (hH1 : d.nmem (ib + iIV nD n 2 + 4 * n + 1) = ts.length)
    (hH2 : d.nmem (ib + iIV nD n 2 + 4 * n + 2) = ((List.finRange nV).map τf.symm).length)
    (hH3 : d.nmem (ib + iIV nD n 2 + 4 * n + 3) = cs.length)
    (hbd : ∀ i < iHD nD n 2 + 4, d.nmem (ib + i) ≤ B + 16 * (n + 1))
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
    (hlt : pstWN (B + 16 * (n + 1))
      (pcoreH D V F n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)) < ib)
    (hle : ib + pstWN (B + 16 * (n + 1))
      (pcoreH D V F n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)) ≤ W')
    (hz : ∀ i, iHD nD n 2 + 4 ≤ i → i ≤ pstWN (B + 16 * (n + 1))
      (pcoreH D V F n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)) →
        d.nmem (ib + i) = 0)
    (hv : ∀ j < 45, d.nreg (1000 + j) = StFix.sVM B nD n
      (pcoreH D V F n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w))
      (B + 16 * (n + 1) + 1) ib (iHD nD n 2 + 4) j) :
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
  set len := iHD nD n 2 + 4 with hlen
  set P := memIn d.nmem ib len with hPdef
  have hgP : ∀ i, i < len → P.data.getD i 0 = d.nmem (ib + i) := fun i hi => by
    rw [hPdef, memIn_getD, ite_eq_left_of_eq_true _ _ (eq_true hi)]
  have hP : ∀ i, P.data.getD i 0 ≤ B + 16 * (n + 1) := fun i => by
    rw [hPdef, memIn_getD]
    split_ifs with h
    · exact hbd i h
    · exact Nat.zero_le _
  have hK : KInput M.dual ∅ 0 σ ιF ιG ιV ιE P :=
    hKM.kInput hE P (fun i hi => hgP i (by simp only [hlen, iHD, iIV]; omega))
  have hG : KBnd 2 (fun i => if i = 0 then d₁ else d₀) σ n P := by
    refine StEnc.kBnd_of σ ?_ ?_
    · rw [hgP _ (by simp only [hlen, iHD, iIV, iGB]; omega)]; exact hG0
    · rw [hgP _ (by simp only [hlen, iHD, iIV, iGB]; omega), ← add_assoc]; exact hG1
  have hι1 : ιF = fun x => 1 + (τv x : ℕ) := funext hιF
  have hι2 : ιV = fun v => ofF + (τf v : ℕ) := funext hιV
  have hI : KInit M.dual σ ιF ιV n 2 (toDD T₀) C₀ ((List.finRange nF).map τv.symm) ts
      ((List.finRange nV).map τf.symm) cs P := by
    rw [hι1, hι2]
    exact StEnc.kInit_of σ τv τf hOT hOC hIV hIT hIF hIC hH0 hH1 hH2 hH3 P
      (fun j hj => hgP j hj) hnF hnV
  have hIn := inData_memIn (len := len) d hlt hle hz
  have hv' : ∀ j < 45, d.nreg (1000 + j) = StFix.sVM B nD n
      (pcoreH D V F n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w))
      (B + 16 * (n + 1) + 1) ib P.data.length j := by
    rw [hPdef, memIn_length]; exact hv
  exact st_sNFM hWa hB hB7 hP hM hrot hface hc hXY hd₁ hd₀ hw hroot hI₀ hL hK hG hI hoff hCr P'
    hd hWW hdr4 hdm4 hdr hdm hrr hrm hwt hph hcp hrsm hth hh0 hIn hv'

/-- **The initial dual tree of the s-t flow from the parent words of Dijkstra's run** on the
perturbed lengths `wlen (stN w) (capR c X Y) (isoEpsG w)` (`NegSSSP.stdP_exec` on `M.dual` from
the face of `d₀`): a tree `T₀` rooted at `face d₀` with `PAR[ιF x] = σ (T₀.par x)` meeting the
invariant `hI₀` of `st_sNFM`. -/
theorem t0_of_par (hM : M.IsPlane) {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) (X Y : Finset V) {w : D → ℤ}
    {t : V} (hw : IsIsoW M t w) (d₀ : D) {mem : ℕ → ℕ} {Pb : ℕ}
    (hpar : ∀ x, x ≠ M.face d₀ → ∃ d, mem (Pb + ιF x) = σ d ∧ M.face (M.rev d) = x ∧
      MSSP.dist (dG M (wlen (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)))
          (M.face d₀) (M.face d) +
        wlen (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w) d =
      MSSP.dist (dG M (wlen (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)))
        (M.face d₀) x) :
    ∃ T₀ : DTree M, T₀.root = M.face d₀ ∧ (∀ x, x ≠ M.face d₀ → mem (Pb + ιF x) = σ (T₀.par x)) ∧
      ∀ s t', LInv (capR M c X Y) (isoEpsG V F w) s t'
        (tSt M (capR M c X Y) (isoEpsG V F w) T₀) := by
  have hε : ∀ d, 1 ≤ isoEpsG V F w d := fun d => (isoEpsG_bounds hM hw d).1
  have hS : 0 ≤ ∑ d, isoEpsG V F w d := Finset.sum_nonneg fun d _ => (zero_le_one.trans (hε d))
  have hN : (Fintype.card F + 1) * ∑ d, isoEpsG V F w d + 1 ≤ stN (V := V) (F := F) w := by
    unfold stN lexR
    have : (0 : ℤ) ≤ (Fintype.card F + 1) * ∑ d, isoEpsG V F w d :=
      mul_nonneg (by positivity) hS
    linarith
  exact stTree_of_par hM (capR_nonneg hc X Y) hε hN (M.face d₀) d₀ σ hpar

end STFlow

end PlanarFlow
