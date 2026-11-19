module

public import PlanarFlow.BKMNW.StRankM
public import PlanarFlow.NegSSSP.Enc.VTree
public import PlanarFlow.NegSSSP.IsoWProg
public import PlanarFlow.BKMNW.StIsoG

/-!
# The isolating weight of the s-t flow on the machine

The perturbation of the s-t flow (`STFlow.isoEpsG V F w`) needs an isolating weight `w` with the
exceptional vertex the sink `t = tail d₀` (`STFlow.IsIsoW M t w`). For any spanning tree
`C : DTree M.dual` of the vertices rooted at `t`, `MSSP.treeW C` is one
(`STFlow.isIsoW_treeW`). Here the machine computes such a tree and its weight, from the compact
words of Klein's encoding of `M.dual` (`NF[σ d] = of + τ (tail d)`, `RV[σ d] = σ (rev d)`) and the
number `σ d₀` of the sink dart (all fixed programs, parameters in registers, natural words only):

* `ivPrep`: the arrays `Tv[i] = NF[i] - of`, `K[i] = 1`, `Hv[i] = NF[RV[i]] - of`
  (`ivPrep_exec`, `16 nD + 4` steps);
* `ivSet1` (the registers of the search, `τ t = NF[σ d₀] - of`), `osProg ; ctProg`
  (`NegSSSP.vtSearch_exec`: a tree `C` of the vertices rooted at `t`, its parents at `PA`);
* `ivSet2` (the registers of the orders), `toProg` (`NegSSSP.toProg_orders`: an order `cs` of
  `C` by depth, the parent darts `IT`, the length `HD[1]`);
* `ivSet3` (the registers of the weights), `iwProg` (`NegSSSP.iwProg_treeW`):
  `WT[σ d] = B + treeW C d`.
* **`ivProg`**, **`ivProg_exec`**: on a plane map, within `ivCost nD nV` (`O(nD + nV)`) steps,
  a tree `C : DTree M.dual` with `C.root = tail d₀` and `WT[σ d] = B + treeW C d` at `Wb`, so
  `IsIsoW M (tail d₀) (treeW C)`; the memory changes only in the scratch
  `[Z, Z + 4 nD + 19 nV + 5)` and `[Wb, Wb + nD)`.

Registers: natural `7960 … 7968` (inputs `nD`, `NFb`, `RVb`, `of`, `nV`, `Gp` (the address of
`σ d₀`), `Z`, `Wb`, `B`), `7970 … 7979` (scratch), and those of the called programs
(`1400 … 1420`, `1500 … 1520`, `1600 … 1634`, `1700 … 1718`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

namespace StEnc

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP

/-! ### The programs -/

/-- One step of the preparation at `i = r7970`. -/
def ivPrepBody : Stmt := block [
  .addN 7972 7961 7970, .loadN 7973 7972, .subN 7973 7973 7963, .addN 7974 7962 7970,
  .loadN 7974 7974, .addN 7974 7961 7974, .loadN 7974 7974, .subN 7974 7974 7963,
  .addN 7972 7966 7970, .storeN 7972 7973, .addN 7972 7972 7960, .storeN 7972 7971,
  .addN 7972 7972 7960, .storeN 7972 7974, .addN 7970 7970 7971]

/-- **The arrays of the search**: `Tv`, `K`, `Hv` at `Z`, `Z + nD`, `Z + 2 nD`. -/
def ivPrep : Stmt :=
  .seq (block [.constN 7971 1, .constN 7970 0]) (.whileLtN 7970 7960 ivPrepBody)

/-- The registers of the search (`Z' = Z + 3 nD`). -/
def ivSet1 : Stmt := block [
  .copyN 1500 7960, .copyN 1501 7964, .copyN 1502 7966, .addN 1504 7966 7960,
  .addN 1505 1504 7960, .addN 1505 1505 7960, .constN 7976 1, .addN 1506 1505 7964,
  .addN 1506 1506 7976, .addN 1507 1506 7964, .addN 1508 1507 7964, .addN 1509 1508 7964,
  .copyN 1400 7964, .loadN 7975 7965, .addN 7975 7961 7975, .loadN 7975 7975,
  .subN 1401 7975 7963, .copyN 1402 1507, .copyN 1403 1508, .copyN 1404 1509,
  .addN 1405 1504 7960, .addN 1406 1509 7960, .addN 1407 1406 7964, .addN 1408 1407 7964]

/-- The registers of the orders (`Sb = Z' + 7 nV + nD + 2`); the parent word of the root set to
`0` (a dart number). -/
def ivSet2 : Stmt := block [
  .copyN 1600 7964, .copyN 1601 1401, .copyN 1602 1408, .copyN 1603 7961, .copyN 1604 7963,
  .addN 1605 1408 7964, .addN 1605 1605 7976, .addN 1605 1605 7976, .addN 1606 1605 7964,
  .addN 1607 1606 7964, .addN 1608 1607 7964, .addN 1608 1608 7976, .addN 1609 1608 7964,
  .addN 1610 1609 7964, .addN 1611 1610 7964, .addN 1612 1611 7964, .addN 1613 1612 7964,
  .addN 1614 1613 7964, .addN 1615 1614 7964, .addN 7978 1408 1401, .constN 7979 0,
  .storeN 7978 7979]

/-- The registers of the weights. -/
def ivSet3 : Stmt := block [
  .copyN 1700 7964, .copyN 1701 7960, .addN 7977 1615 7976, .loadN 1702 7977,
  .copyN 1703 7966, .copyN 1704 7962, .copyN 1705 1614, .addN 1706 7977 7976,
  .copyN 1707 7967, .copyN 1708 7968]

/-- **The isolating weight of the sink.** -/
def ivProg : Stmt :=
  .seq (.seq ivPrep (.seq ivSet1 (.seq osProg ctProg))) (.seq ivSet2 (.seq toProg
    (.seq ivSet3 iwProg)))

theorem ivProg_natOnly : Klein.natOnly ivProg = true := by kernel_rfl

variable {P : Input} {W : ℕ}

/-! ### The preparation -/

theorem ivPrep_exec {nD NFb RVb of Z : ℕ} {NF RV : ℕ → ℕ} (c : Config) (hc : WordsBounded W c)
    (h60 : c.nreg 7960 = nD) (h61 : c.nreg 7961 = NFb) (h62 : c.nreg 7962 = RVb)
    (h63 : c.nreg 7963 = of) (h66 : c.nreg 7966 = Z)
    (hNF : ∀ i < nD, c.nmem (NFb + i) = NF i) (hRV : ∀ i < nD, c.nmem (RVb + i) = RV i)
    (hRVlt : ∀ i < nD, RV i < nD) (lN : NFb + nD ≤ Z) (lR : RVb + nD ≤ Z)
    (wZ : Z + 3 * nD ≤ W) (w1 : 1 ≤ W) :
    ∃ c' t, Exec P W ivPrep c c' t ∧ t ≤ 17 * nD + 4 ∧
      ((∀ i < nD, c'.nmem (Z + i) = NF i - of) ∧ (∀ i < nD, c'.nmem (Z + nD + i) = 1) ∧
        (∀ i < nD, c'.nmem (Z + 2 * nD + i) = NF (RV i) - of) ∧
        (∀ a, (a < Z ∨ Z + 3 * nD ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 7970 ∨ 7979 < r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
        c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold ivPrep
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ j < i, c'.nmem (Z + j) = NF j - of) ∧ (∀ j < i, c'.nmem (Z + nD + j) = 1) ∧
      (∀ j < i, c'.nmem (Z + 2 * nD + j) = NF (RV j) - of) ∧
      (∀ a, (a < Z ∨ Z + 3 * nD ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ j, i ≤ j → j < nD → c'.nmem (Z + j) = c.nmem (Z + j) ∧
        c'.nmem (Z + nD + j) = c.nmem (Z + nD + j) ∧
        c'.nmem (Z + 2 * nD + j) = c.nmem (Z + 2 * nD + j)) ∧
      c'.nreg 7971 = 1 ∧ (∀ r, r < 7970 ∨ 7979 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 7970) (bR := 7960) J (K := 15) (n := nD) _ ‹_›
    (by config_simp) (by config_simp; exact h60) ?_
    (fun i c₁ hi hw ha hb ⟨g0, g1, g2, g3, g4, g71, gn, gr, grm, go⟩ => by
      have e61 : c₁.nreg 7961 = NFb := (gn _ (by omega)).trans h61
      have e62 : c₁.nreg 7962 = RVb := (gn _ (by omega)).trans h62
      have e63 : c₁.nreg 7963 = of := (gn _ (by omega)).trans h63
      have e66 : c₁.nreg 7966 = Z := (gn _ (by omega)).trans h66
      have e60 : c₁.nreg 7960 = nD := hb
      have eN : c₁.nmem (NFb + i) = NF i := by rw [g3 _ (by omega)]; exact hNF i hi
      have eR : c₁.nmem (RVb + i) = RV i := by rw [g3 _ (by omega)]; exact hRV i hi
      have hr := hRVlt i hi
      have eNR : c₁.nmem (NFb + RV i) = NF (RV i) := by rw [g3 _ (by omega)]; exact hNF _ hr
      exec_block
      all_goals try ((try config_simp); (try simp only [e60, e61, e62, e63, e66, ha, g71, eN]);
                     (try simp only [eR, eNR]); omega)
      refine ⟨by omega, by config_simp; simp only [ha, g71], by config_simp; exact hb, ?_⟩
      dsimp only [J]
      refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun a ha' => ?_,
        fun j h1 h2 => ?_, by config_simp; exact g71, fun r hr => ?_, by config_simp; exact gr,
        by config_simp; exact grm, by config_simp; exact go⟩ <;> config_simp <;>
        simp only [e60, e61, e62, e63, e66, ha, g71, eN, eR, upd_apply]
      · split_ifs with p q r
        · omega
        · omega
        · have : j = i := by omega
          subst this; rfl
        · exact g0 j (by omega)
      · split_ifs with p q r
        · omega
        · have : j = i := by omega
          subst this; rfl
        · omega
        · exact g1 j (by omega)
      · split_ifs with p q r
        · have : j = i := by omega
          subst this; rw [eNR]
        · omega
        · omega
        · exact g2 j (by omega)
      · split_ifs with p q r
        · omega
        · omega
        · omega
        · exact g3 a ha'
      · obtain ⟨k1, k2, k3⟩ := g4 j (by omega) h2
        split_ifs <;> first | omega | exact ⟨k1, k2, k3⟩
      · split_ifs <;> first | omega | exact gn r hr)) ?_
  · dsimp only [J]
    refine ⟨fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
      fun j hj => absurd hj (by omega), fun a _ => by config_simp,
      fun j _ _ => ⟨rfl, rfl, rfl⟩, by config_simp,
      fun r hr => ?_, by config_simp, by config_simp, by config_simp⟩
    config_simp; simp only [upd_apply]; split_ifs <;> omega
  intro c₂ k₂ hk₂ _ ⟨_, g0, g1, g2, g3, _, _, gn, gr, grm, go⟩
  exact ⟨by omega, g0, g1, g2, g3, gn, gr, grm, go⟩

/-! ### The registers -/

theorem ivSet1_exec {nD NFb of nV Gp Z g : ℕ} (c : Config) (hc : WordsBounded W c)
    (h60 : c.nreg 7960 = nD) (h61 : c.nreg 7961 = NFb) (h63 : c.nreg 7963 = of)
    (h64 : c.nreg 7964 = nV) (h65 : c.nreg 7965 = Gp) (h66 : c.nreg 7966 = Z)
    (hg : c.nmem Gp = g) (hgW : NFb + g ≤ W) (wZ : Z + 4 * nD + 7 * nV + 2 ≤ W) :
    ∃ c' t, Exec P W ivSet1 c c' t ∧ t = 24 ∧
      (c'.nreg 1500 = nD ∧ c'.nreg 1501 = nV ∧ c'.nreg 1502 = Z ∧ c'.nreg 1504 = Z + nD ∧
        c'.nreg 1505 = Z + 3 * nD ∧ c'.nreg 1506 = Z + 3 * nD + nV + 1 ∧
        c'.nreg 1507 = Z + 3 * nD + 2 * nV + 1 ∧ c'.nreg 1508 = Z + 3 * nD + 3 * nV + 1 ∧
        c'.nreg 1509 = Z + 3 * nD + 4 * nV + 1 ∧ c'.nreg 1400 = nV ∧
        c'.nreg 1401 = c.nmem (NFb + g) - of ∧
        c'.nreg 1402 = Z + 3 * nD + 2 * nV + 1 ∧ c'.nreg 1403 = Z + 3 * nD + 3 * nV + 1 ∧
        c'.nreg 1404 = Z + 3 * nD + 4 * nV + 1 ∧ c'.nreg 1405 = Z + 2 * nD ∧
        c'.nreg 1406 = Z + 3 * nD + 4 * nV + 1 + nD ∧
        c'.nreg 1407 = Z + 3 * nD + 5 * nV + 1 + nD ∧
        c'.nreg 1408 = Z + 3 * nD + 6 * nV + 1 + nD ∧ c'.nreg 7976 = 1 ∧
        (∀ r, r < 1400 ∨ (1408 < r ∧ r < 1500) ∨ (1509 < r ∧ r < 7975) ∨ 7976 < r →
          c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold ivSet1
  exec_block
  all_goals try ((try config_simp); (try simp only [h60, h61, h63, h64, h65, h66, hg]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r hr => ?_, rfl, rfl, rfl, rfl⟩ <;> config_simp <;>
    (try simp only [h60, h61, h63, h64, h65, h66, hg]) <;> (try omega)
  repeat (rw [upd_other _ _ _ (by omega)])

theorem ivSet2_exec {ru PDb NFb of nV : ℕ} (c : Config) (hc : WordsBounded W c)
    (h01 : c.nreg 1401 = ru) (h08 : c.nreg 1408 = PDb) (h61 : c.nreg 7961 = NFb)
    (h63 : c.nreg 7963 = of) (h64 : c.nreg 7964 = nV) (h76 : c.nreg 7976 = 1)
    (wZ : PDb + 11 * nV + 3 ≤ W) (hru : ru < nV) :
    ∃ c' t, Exec P W ivSet2 c c' t ∧ t = 22 ∧
      (ToRegs nV ru (PDb + nV + 2) PDb NFb (PDb + 9 * nV + 3) (PDb + 10 * nV + 3)
          (PDb + 11 * nV + 3) of c' ∧
        c'.nmem = upd c.nmem (PDb + ru) 0 ∧
        (∀ r, r < 1600 ∨ (1615 < r ∧ r < 7978) ∨ 7979 < r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold ivSet2
  exec_block
  all_goals try ((try config_simp); (try simp only [h01, h08, h61, h63, h64, h76]); omega)
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_,
    fun r hr => ?_, rfl, rfl, rfl⟩ <;> config_simp <;>
    (try simp only [h01, h08, h61, h63, h64, h76]) <;> (try omega)
  repeat (rw [upd_other _ _ _ (by omega)])

theorem ivSet3_exec {nV nD HDb Z RVb ITb Wb B : ℕ} (c : Config) (hc : WordsBounded W c)
    (h60 : c.nreg 7960 = nD) (h62 : c.nreg 7962 = RVb) (h64 : c.nreg 7964 = nV)
    (h66 : c.nreg 7966 = Z) (h67 : c.nreg 7967 = Wb) (h68 : c.nreg 7968 = B)
    (h76 : c.nreg 7976 = 1) (h14 : c.nreg 1614 = ITb) (h15 : c.nreg 1615 = HDb)
    (wZ : HDb + 2 ≤ W) :
    ∃ c' t, Exec P W ivSet3 c c' t ∧ t = 10 ∧
      (c'.nreg 1700 = nV ∧ c'.nreg 1701 = nD ∧ c'.nreg 1702 = c.nmem (HDb + 1) ∧
        c'.nreg 1703 = Z ∧ c'.nreg 1704 = RVb ∧ c'.nreg 1705 = ITb ∧ c'.nreg 1706 = HDb + 2 ∧
        c'.nreg 1707 = Wb ∧ c'.nreg 1708 = B ∧
        (∀ r, r < 1700 ∨ (1708 < r ∧ r < 7977) ∨ 7977 < r → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold ivSet3
  exec_block
  all_goals try ((try config_simp); (try simp only [h15, h76]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩ <;>
    config_simp <;> (try simp only [h60, h62, h64, h66, h67, h68, h76, h14, h15]) <;> (try omega)
  simp only [upd_apply]; split_ifs <;> first | omega | rfl

/-! ### The whole program -/

/-- The cost bound of `ivProg`. -/
def ivCost (nD nV : ℕ) : ℕ := 70 * nD + 220 * nV + 172

section Map

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-- The search: the tree `C` of the vertices rooted at `t = tail d₀` and its parent words. -/
theorem ivA_exec [Nonempty D] (hM : M.IsPlane) {nD nV : ℕ} (σ : D ≃ Fin nD) (τ : V ≃ Fin nV)
    (d₀ : D) {NFb RVb of Gp Z : ℕ} (c : Config) (hc : WordsBounded W c)
    (h60 : c.nreg 7960 = nD) (h61 : c.nreg 7961 = NFb) (h62 : c.nreg 7962 = RVb)
    (h63 : c.nreg 7963 = of) (h64 : c.nreg 7964 = nV) (h65 : c.nreg 7965 = Gp)
    (h66 : c.nreg 7966 = Z)
    (hNF : ∀ d, c.nmem (NFb + σ d) = of + τ (M.tail d))
    (hRV : ∀ d, c.nmem (RVb + σ d) = σ (M.rev d)) (hG : c.nmem Gp = σ d₀)
    (lN : NFb + nD ≤ Z) (lR : RVb + nD ≤ Z) (lG : Gp < Z)
    (wZ : Z + 4 * nD + 7 * nV + 2 ≤ W) :
    ∃ c' t, Exec P W (.seq ivPrep (.seq ivSet1 (.seq osProg ctProg))) c c' t ∧
      t ≤ 17 * nD + 4 + (24 + (osCost nD nV + (35 * nV + 19 * nD + 12))) ∧
      ∃ C : STFlow.DTree M.dual, C.root = M.tail d₀ ∧
        (∀ y, y ≠ C.root → c'.nmem (Z + 4 * nD + 6 * nV + 1 + τ y) = σ (C.par y)) ∧
        (∀ i < nD, c'.nmem (Z + i) = c.nmem (NFb + i) - of) ∧
        (∀ a, a < Z ∨ Z + 4 * nD + 7 * nV + 1 ≤ a → c'.nmem a = c.nmem a) ∧
        c'.nreg 1401 = τ (M.tail d₀) ∧ c'.nreg 1408 = Z + 4 * nD + 6 * nV + 1 ∧
        c'.nreg 7976 = 1 ∧
        (∀ r, r < 1400 ∨ (1420 < r ∧ r < 1500) ∨ (1520 < r ∧ r < 7970) ∨ 7979 < r →
          c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hD : 0 < nD := Fin.pos (σ (Classical.arbitrary D))
  have hNFi : ∀ i (hi : i < nD), c.nmem (NFb + i) = of + τ (M.tail (σ.symm ⟨i, hi⟩)) :=
    fun i hi => by have := hNF (σ.symm ⟨i, hi⟩); rwa [Equiv.apply_symm_apply] at this
  have hRVi : ∀ i (hi : i < nD), c.nmem (RVb + i) = σ (M.rev (σ.symm ⟨i, hi⟩)) :=
    fun i hi => by have := hRV (σ.symm ⟨i, hi⟩); rwa [Equiv.apply_symm_apply] at this
  obtain ⟨c₁, t₁, e₁, ht₁, p0, p1, p2, pm, pn, pr, prm, po⟩ := ivPrep_exec (P := P)
    (NF := fun i => c.nmem (NFb + i)) (RV := fun i => c.nmem (RVb + i)) c hc h60 h61 h62 h63 h66
    (fun i _ => rfl) (fun i _ => rfl) (fun i hi => by rw [hRVi i hi]; exact (σ _).2) lN lR
    (by omega) (by omega)
  have hg : c₁.nmem Gp = σ d₀ := by rw [pm _ (Or.inl lG)]; exact hG
  have hgW : NFb + σ d₀ ≤ W := by have := (σ d₀).2; omega
  obtain ⟨c₂, t₂, e₂, ht₂, s00, s01, s02, s04, s05, s06, s07, s08, s09, b00, b01, b02, b03, b04,
    b05, b06, b07, b08, s76, sn, sm, sr, srm, so⟩ := ivSet1_exec (P := P) c₁ e₁.wb_right
    ((pn _ (by omega)).trans h60) ((pn _ (by omega)).trans h61) ((pn _ (by omega)).trans h63)
    ((pn _ (by omega)).trans h64) ((pn _ (by omega)).trans h65) ((pn _ (by omega)).trans h66) hg
    hgW (by omega)
  have b01' : c₂.nreg 1401 = τ (M.tail d₀) := by
    rw [b01, pm _ (Or.inl (by have := (σ d₀).2; omega)), hNF]; omega
  have hNT : ∀ d, c₂.nmem (Z + σ d) = τ (M.tail d) := fun d => by
    rw [sm, p0 _ (σ d).2, hNF]; omega
  have hK : ∀ d, c₂.nmem (Z + nD + σ d) = 1 := fun d => by rw [sm, p1 _ (σ d).2]
  have hNH : ∀ d, c₂.nmem (Z + 2 * nD + σ d) = τ (M.head d) := fun d => by
    rw [sm, p2 _ (σ d).2, hRV, hNF]; simp only [CombMap.head]; omega
  obtain ⟨c₃, t₃, e₃, ht₃, ⟨C, hCr, hPA⟩, m₃, n₃, rr₃, rm₃, o₃⟩ :=
    vtSearch_exec (P := P) hM σ τ (M.tail d₀) c₂ e₂.wb_right s00 s01 s02 s04 s05 s06 s07 s08 s09
      b00 (b01'.trans rfl) b02 b03 b04 (by rw [b05]) (by rw [b06]) (by rw [b07])
      (by rw [b08]) hNT hK hNH (by omega) (by omega) (by omega) (by omega)
  refine ⟨c₃, t₁ + (t₂ + t₃), Exec.seq e₁ (Exec.seq e₂ e₃), by omega, C, hCr,
    fun y hy => ?_, fun i hi => ?_, fun a ha => ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · have := hPA y hy; rwa [show Z + 3 * nD + 6 * nV + 1 + nD = Z + 4 * nD + 6 * nV + 1 by ring]
      at this
  · rw [m₃ _ (Or.inl (by omega)), sm, p0 i hi]
  · rw [m₃ _ (by omega), sm, pm _ (by omega)]
  · rw [n₃ _ (by omega)]; exact b01'
  · rw [n₃ _ (by omega), b08]; ring
  · rw [n₃ _ (by omega)]; exact s76
  · rw [n₃ _ (by omega), sn _ (by omega), pn _ (by omega)]
  · rw [rr₃, sr, pr]
  · rw [rm₃, srm, prm]
  · rw [o₃, so, po]

/-- **The isolating weight of the sink on the machine** (see the module docstring): on a plane
map, from the compact face words of Klein's encoding of `M.dual` (`NF[σ d] = of + τ (tail d)`),
the reverses and the number of the sink dart `d₀`, `ivProg` ends within `ivCost nD nV` steps
with **a tree `C : DTree M.dual` of the vertices rooted at `tail d₀`** and the words
`B + treeW C d` at `Wb + σ d`; `treeW C` is an isolating weight of the sink
(`STFlow.isIsoW_treeW`), of absolute value at most `#V`. The memory changes only in the scratch
`[Z, Z + 4 nD + 18 nV + 6)` and in `[Wb, Wb + nD)`. -/
theorem ivProg_exec [Nonempty D] (hM : M.IsPlane) {nD nV : ℕ} (σ : D ≃ Fin nD) (τ : V ≃ Fin nV)
    (d₀ : D) {NFb RVb of Gp Z Wb B : ℕ} (c : Config) (hc : WordsBounded W c)
    (h60 : c.nreg 7960 = nD) (h61 : c.nreg 7961 = NFb) (h62 : c.nreg 7962 = RVb)
    (h63 : c.nreg 7963 = of) (h64 : c.nreg 7964 = nV) (h65 : c.nreg 7965 = Gp)
    (h66 : c.nreg 7966 = Z) (h67 : c.nreg 7967 = Wb) (h68 : c.nreg 7968 = B)
    (hNF : ∀ d, c.nmem (NFb + σ d) = of + τ (M.tail d))
    (hRV : ∀ d, c.nmem (RVb + σ d) = σ (M.rev d)) (hG : c.nmem Gp = σ d₀)
    (lN : NFb + nD ≤ Z) (lR : RVb + nD ≤ Z) (lG : Gp < Z)
    (lW : Wb + nD ≤ Z ∨ Z + 4 * nD + 18 * nV + 6 ≤ Wb) (lWR : Wb + nD ≤ RVb ∨ RVb + nD ≤ Wb)
    (hB : Fintype.card V ≤ B) (wB : B + Fintype.card V ≤ W) (wW : Wb + nD ≤ W)
    (wZ : Z + 4 * nD + 18 * nV + 6 ≤ W) (wo : of + nV ≤ W) :
    ∃ c' t, Exec P W ivProg c c' t ∧ t ≤ ivCost nD nV ∧
      ∃ C : STFlow.DTree M.dual, C.root = M.tail d₀ ∧
        (∀ d, (c'.nmem (Wb + σ d) : ℤ) = B + MSSP.treeW C d) ∧
        (∀ a, a < Z ∨ Z + 4 * nD + 18 * nV + 6 ≤ a → a < Wb ∨ Wb + nD ≤ a →
          c'.nmem a = c.nmem a) ∧
        (∀ r, r < 1400 ∨ (1420 < r ∧ r < 1500) ∨ (1520 < r ∧ r < 1600) ∨
          (1634 < r ∧ r < 1700) ∨ (1718 < r ∧ r < 7970) ∨ 7979 < r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hD : 0 < nD := Fin.pos (σ (Classical.arbitrary D))
  have hV : 0 < nV := Fin.pos (τ (M.tail (Classical.arbitrary D)))
  set PDb := Z + 4 * nD + 6 * nV + 1 with hPDb
  obtain ⟨c₁, t₁, e₁, ht₁, C, hCr, hPA, hTv, m₁, r01, r08, r76, n₁, rr₁, rm₁, o₁⟩ :=
    ivA_exec (P := P) hM σ τ d₀ c hc h60 h61 h62 h63 h64 h65 h66 hNF hRV hG lN lR lG (by omega)
  have q : ∀ r, 7960 ≤ r → r ≤ 7968 → c₁.nreg r = c.nreg r := fun r h1 h2 => n₁ r (by omega)
  have hru : (τ (M.tail d₀) : ℕ) < nV := (τ _).2
  obtain ⟨c₂, t₂, e₂, ht₂, hR₂, m₂, n₂, rr₂, rm₂, o₂⟩ := ivSet2_exec (P := P) c₁ e₁.wb_right
    r01 r08 ((q _ (by omega) (by omega)).trans h61) ((q _ (by omega) (by omega)).trans h63)
    ((q _ (by omega) (by omega)).trans h64) r76 (by omega) hru
  have hL₂ : ToLay nV nD (τ C.root) (PDb + nV + 2) PDb NFb (PDb + 9 * nV + 3) (PDb + 10 * nV + 3)
      (PDb + 11 * nV + 3) of W := by
    rw [hCr]
    exact ⟨hV, hru, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inr (by omega),
      by omega, by omega, by omega, by omega, by omega, by omega, wo⟩
  have hPD₂ : ∀ y, y ≠ C.root → c₂.nmem (PDb + τ y) = σ (C.par y) := fun y hy => by
    have hne : (τ y : ℕ) ≠ τ (M.tail d₀) := fun h => hy (by rw [hCr]; exact τ.injective (Fin.ext h))
    rw [m₂, upd_other _ _ _ (by omega)]; exact hPA y hy
  have hPDr : c₂.nmem (PDb + τ C.root) < nD := by rw [m₂, hCr, upd_same]; exact hD
  have hA₂ : ∀ d, c₂.nmem (NFb + σ d) = of + τ ((M.dual).face d) := fun d => by
    have := (σ d).2
    rw [m₂, upd_other _ _ _ (by omega), m₁ _ (Or.inl (by omega))]; exact hNF d
  obtain ⟨c₃, t₃, e₃, ht₃, ys, hO, -, hIT, -, hH1, m₃, n₃, rr₃, rm₃, o₃⟩ :=
    toProg_orders (P := P) (M := M.dual) C σ τ hL₂ c₂ e₂.wb_right (by rw [hCr]; exact hR₂) hPD₂
      hPDr hA₂
  have q₃ : ∀ r, (7960 ≤ r ∧ r ≤ 7968) ∨ r = 7976 ∨ r = 1614 ∨ r = 1615 →
      c₃.nreg r = c₂.nreg r := fun r hr => n₃ r (by omega)
  obtain ⟨c₄, t₄, e₄, ht₄, w00, w01, w02, w03, w04, w05, w06, w07, w08, n₄, m₄, rr₄, rm₄, o₄⟩ :=
    ivSet3_exec (P := P) (nV := nV) (nD := nD) (Z := Z) (RVb := RVb) (Wb := Wb) (B := B)
      (ITb := PDb + 10 * nV + 3) (HDb := PDb + 11 * nV + 3) c₃ e₃.wb_right
      (by rw [q₃ _ (by omega), n₂ _ (by omega), q _ (by omega) (by omega)]; exact h60)
      (by rw [q₃ _ (by omega), n₂ _ (by omega), q _ (by omega) (by omega)]; exact h62)
      (by rw [q₃ _ (by omega), n₂ _ (by omega), q _ (by omega) (by omega)]; exact h64)
      (by rw [q₃ _ (by omega), n₂ _ (by omega), q _ (by omega) (by omega)]; exact h66)
      (by rw [q₃ _ (by omega), n₂ _ (by omega), q _ (by omega) (by omega)]; exact h67)
      (by rw [q₃ _ (by omega), n₂ _ (by omega), q _ (by omega) (by omega)]; exact h68)
      (by rw [q₃ _ (by omega), n₂ _ (by omega)]; exact r76)
      (by rw [q₃ _ (by omega)]; exact hR₂.r14) (by rw [q₃ _ (by omega)]; exact hR₂.r15)
      (by omega)
  have hlc : ys.length ≤ nV := by
    rw [orders_ylen_eq hO]; have := Fintype.card_fin nV ▸ Fintype.card_congr τ; omega
  -- the memory of the stages before the weights
  have mm : ∀ a, a < Z + 3 * nD → c₄.nmem a = c₁.nmem a := fun a ha => by
    rw [m₄, m₃ a (Or.inl (by omega)) (Or.inl (by omega)), m₂, upd_other _ _ _ (by omega)]
  have hFC : ∀ i < nD, c₄.nmem (Z + i) = iwFC (M.dual) σ (fun v => (τ v : ℕ)) i := fun i hi => by
    rw [mm _ (by omega), hTv i hi]
    simp only [iwFC, hi, ↓reduceDIte]
    have := hNF (σ.symm ⟨i, hi⟩); rw [Equiv.apply_symm_apply] at this
    rw [this]; simp only [CombMap.dual]; omega
  have hRVw : ∀ i < nD, c₄.nmem (RVb + i) = iwRV (M.dual) σ i := fun i hi => by
    rw [mm _ (by omega), m₁ _ (Or.inl (by omega))]
    simp only [iwRV, hi, ↓reduceDIte]
    have := hRV (σ.symm ⟨i, hi⟩); rw [Equiv.apply_symm_apply] at this
    rw [this]; rfl
  have hCS : ∀ i < ys.length, c₄.nmem (PDb + 10 * nV + 3 + i) = iwCS C σ ys i := fun i hi => by
    rw [m₄, hIT i hi, iwCS_apply C σ ys hi]
  have hL₄ : IwLay nV nD ys.length Z RVb (PDb + 10 * nV + 3) (PDb + 11 * nV + 5) Wb W
      (iwFC (M.dual) σ (fun v => (τ v : ℕ))) (iwRV (M.dual) σ) (iwCS C σ ys) := by
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, Or.inr (by omega), Or.inr (by omega),
      Or.inr (by omega), by omega, lWR, by omega, by omega, by omega, by omega, by omega,
      by omega, wW, by omega, by omega, by omega⟩
    · simp only [iwFC, hi, ↓reduceDIte]; exact (τ _).2
    · simp only [iwRV, hi, ↓reduceDIte]; exact (σ _).2
    · simp only [iwCS, hi, ↓reduceDIte]; exact (σ _).2
  have hI₄ : IwIn nV nD ys.length Z RVb (PDb + 10 * nV + 3) (PDb + 11 * nV + 5) Wb B
      (iwFC (M.dual) σ (fun v => (τ v : ℕ))) (iwRV (M.dual) σ) (iwCS C σ ys) c₄ :=
    ⟨w00, w01, by rw [w02, hH1], w03, w04, w05, by rw [w06], w07, w08, hFC, hRVw, hCS⟩
  obtain ⟨c₅, t₅, e₅, ht₅, hWT, m₅, n₅, rr₅, rm₅, o₅⟩ :=
    iwProg_treeW (P := P) C ys σ (fun v => (τ v : ℕ)) hO.ynd hO.ymem hO.ypw
      (fun a b h => τ.injective (Fin.ext h)) (fun v => (τ v).2) hB wB hL₄ c₄ e₄.wb_right hI₄
  refine ⟨c₅, t₁ + (t₂ + (t₃ + (t₄ + t₅))),
    Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ e₅))), ?_, C, hCr, hWT,
    fun a h1 h2 => ?_, fun r hr => ?_, by rw [rr₅, rr₄, rr₃, rr₂, rr₁],
    by rw [rm₅, rm₄, rm₃, rm₂, rm₁], by rw [o₅, o₄, o₃, o₂, o₁]⟩
  · unfold ivCost; unfold osCost at ht₁; unfold toCost at ht₃; omega
  · rw [m₅ a (by omega) h2, m₄, m₃ a (by omega) (by omega), m₂, upd_other _ _ _ (by omega),
      m₁ a (by omega)]
  · rw [n₅ r (by omega), n₄ r (by omega), n₃ r (by omega), n₂ r (by omega), n₁ r (by omega)]

end Map

end StEnc

end BKMNW

end PlanarFlow
