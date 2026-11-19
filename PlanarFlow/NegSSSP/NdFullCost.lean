module

public import PlanarFlow.NegSSSP.NdFullHF
public import PlanarFlow.NegSSSP.NdCost

/-!
# The full branch: its cost `O(m log m + b² log b)`

On the parameter envelope `FsEnv`, the step count `fsCost` of the full branch is at most
**`fsNcF m b = 10¹⁷ · m lg m + 10⁸ · (b + 1)² lg b + fsKC`** (`fsCost_le`): Klein's MSSP at the
node's size (`partNCost`, `12 · 32886 · 2372500000 · m lg m`, tripled by the store log and the
clearing of the log), the encoders (`feCostDk = O(m log m)`), Dijkstra (`dij (w+1) (m+w) = O(m log m)`),
Bellman–Ford over the dense distance graphs (`bfCostP b ≤ 7900 (b+1)² lg b`), the split and the
node's preparation (`O(m log m)`), every linear term charged to `m lg m` (`lg ≥ 1`) and every
`b²` to `(b+1)² lg b`, `C.k² ≤ 1200 m`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset BKMNW WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- The constant part of the cost of the full branch. -/
def fsKC : ℕ :=
  10 ^ 9 + 27 * (pcCost pnL1 + pcCost pnL2 + hpCost (hfPrmL 0) + hpCost (hfPrmL 0) +
    hpCost hnPrmL)

/-- **The cost bound of the full branch** at a node of `m` darts and `b` boundary vertices. -/
def fsNcF (m b : ℕ) : ℕ := 10 ^ 17 * (m * lg m) + 10 ^ 8 * ((b + 1) ^ 2 * lg b) + fsKC

theorem fe_env_le {m : ℕ} (hm : 1 ≤ m) :
    (3114 * m + 13) * (Nat.log 2 m + 8) + 444800 * m + 1384 ≤ 470000 * (m * lg m) + 1384 := by
  have h1 : 3114 * m + 13 ≤ 3127 * m := by omega
  have h2 : Nat.log 2 m + 8 ≤ 8 * lg m := by unfold lg; omega
  have h3 := Nat.mul_le_mul h1 h2
  have h4 : m ≤ m * lg m := Nat.le_mul_of_pos_right _ (one_le_lg m)
  have : 3127 * m * (8 * lg m) = 25016 * (m * lg m) := by ring
  omega

theorem dij_env_le (C : ℕ) {m w : ℕ} (hm : 1 ≤ m) (hw : w ≤ 2 * m) :
    (cNegMach C).dij (w + 1) (m + w) ≤ 113400 * (m * lg m) := by
  show 6300 * (w + 1 + (m + w)) * lg (w + 1) ≤ _
  have hl : lg (w + 1) ≤ 3 * lg m := (lg_mono (by omega : w + 1 ≤ 3 * m)).trans (lg_three_mul m)
  have h := Nat.mul_le_mul (Nat.mul_le_mul_left 6300 (by omega : w + 1 + (m + w) ≤ 6 * m)) hl
  have : 6300 * (6 * m) * (3 * lg m) = 113400 * (m * lg m) := by ring
  omega

theorem fsP1_le {m k w : ℕ} (hm : 1 ≤ m) (hk : k ≤ 2 * m) (hw : w ≤ 2 * m) :
    Frame.fsP1Cost m k ≤ 200000 * (m * lg m) := by
  have := Frame.nd_cost_le hm hk hw
  unfold Frame.fsP1Cost
  unfold Frame.splitSCost Frame.ndCost at this
  omega

set_option maxHeartbeats 4000000 in
theorem partN_env_le {m k Ck b : ℕ} {p : FeP} (hm : 1 ≤ m) (hk : k ≤ 2 * m) (hCk : Ck ≤ k)
    (hCk2 : Ck ^ 2 ≤ 1200 * m) (hpk : p.k = Ck) (hnD : p.nD ≤ 3 * k) (hnV : p.nV ≤ p.nD)
    (hnF : p.nF ≤ p.nD) :
    partNCost m Ck b p.Kw p.N ≤ 12 * (32886 * 2372500000) * (m * lg m) + 100000 * m +
      36 * (b * b) + 10 * b + 1000 := by
  have hKw : p.Kw = 14 * p.N + 24 * p.NN + 3 * p.k + 23 + p.k * p.k := by
    simp only [FeP.Kw, FeP.Bw, Klein.kBL, Klein.aOUT]; ring
  have hNN : p.NN = 2 * (p.nV + 2 * p.k + (p.nD + 8 * p.k) + (p.nF + 2 * p.k)) := rfl
  have hN : p.N = p.nD + 8 * p.k := rfl
  have hsq : Ck * Ck ≤ 1200 * m := by rw [← pow_two]; exact hCk2
  unfold partNCost
  rw [hKw, hNN, hN, hpk]
  have : 12 * (32886 * 2372500000 * m * lg m) = 12 * (32886 * 2372500000) * (m * lg m) := by ring
  rw [this]
  generalize 12 * (32886 * 2372500000) * (m * lg m) = X
  generalize Ck * Ck = q at hsq ⊢
  generalize b * b = bb
  omega

set_option maxHeartbeats 8000000 in
theorem ndRun_env_le (C : ℕ) {m k w b m' nV nF Ck : ℕ} {p₀ p₁ : FeP}
    (h : FsEnv m k w b m' nV nF Ck p₀ p₁) :
    ndRunCost C m m w b Ck Ck p₀ p₁ ≤ 2 * (12 * (32886 * 2372500000)) * (m * lg m) +
      3000000 * (m * lg m) + 4 * bfCostP b + 300 * (b * b) + 1000 * b +
      (pcCost pnL1 + pcCost pnL2 + hpCost (hfPrmL 0) + hpCost (hfPrmL 0) + hpCost hnPrmL) +
      50000 := by
  have hm : 1 ≤ m := by have := h.hbig; omega
  have hmX : m ≤ m * lg m := Nat.le_mul_of_pos_right _ (one_le_lg m)
  have fe0 := h.hfe₀.trans (fe_env_le hm)
  have fe1 := h.hfe₁.trans (fe_env_le hm)
  have hnD₀ : p₀.nD ≤ 3 * k := by have := h.hnD₀; have := h.hm'; omega
  have hnD₁ : p₁.nD ≤ 3 * k := by have := h.hnD₁; have := h.hm'; omega
  have pa0 := partN_env_le (b := b) hm h.hk2 h.hCk h.hCk2 h.hk₀ hnD₀ h.hnV₀ h.hnF₀
  have pa1 := partN_env_le (b := b) hm h.hk2 h.hCk h.hCk2 h.hk₁ hnD₁ h.hnV₁ h.hnF₁
  have dj := dij_env_le C hm h.hw2
  have hk2 := h.hk2
  have hw2 := h.hw2
  have hbw := h.hbw
  unfold ndRunCost pnCost bfWP
  generalize m * lg m = X at *
  generalize b * b = bb at *
  generalize (cNegMach C).dij (w + 1) (m + w) = dd at *
  generalize partNCost m Ck b p₀.Kw p₀.N = q₀ at *
  generalize partNCost m Ck b p₁.Kw p₁.N = q₁ at *
  generalize feCostDk p₀ = r₀ at *
  generalize feCostDk p₁ = r₁ at *
  omega

set_option maxHeartbeats 8000000 in
/-- **The cost of the full branch** (see the module docstring). -/
theorem fsCost_le (C : ℕ) {m k w b m' nV nF Ck : ℕ} {p₀ p₁ : FeP}
    (h : FsEnv m k w b m' nV nF Ck p₀ p₁) : fsCost C m k w b m' nV nF Ck p₀ p₁ ≤ fsNcF m b := by
  have hm : 1 ≤ m := by have := h.hbig; omega
  have hmX : m ≤ m * lg m := Nat.le_mul_of_pos_right _ (one_le_lg m)
  have hR := ndRun_env_le C h
  have P1 := fsP1_le hm h.hk2 h.hw2
  have sp := Frame.spWs_le hm h.hk2
  have rn := Frame.rnCost_le hm h.hw2
  have bf := bfCostP_le b
  have hbb : b * b ≤ (b + 1) ^ 2 * lg b := by
    have := one_le_lg b
    calc b * b ≤ (b + 1) ^ 2 * 1 := by nlinarith
      _ ≤ (b + 1) ^ 2 * lg b := Nat.mul_le_mul_left _ this
  have hbfY : 7900 * (b + 1) ^ 2 * lg b = 7900 * ((b + 1) ^ 2 * lg b) := by ring
  have hlg : m * (Nat.log 2 m + 1) = m * lg m := rfl
  -- the node area `END₁ − Z`
  have hE₀ := pn_end p₀
  have hE₁ := pn_end p₁
  have hI0₀ := h.hI0₀
  have hI0₁ := h.hI0₁
  have hYZ : fbY (Frame.spB0 k) k m w b p₀ p₁ =
      fbZ (Frame.spB0 k) k m w b p₀ p₁ + 22 * (m + w + 1) := rfl
  have hS : fbS w b p₀ p₁ = w + b * b + p₀.k + p₁.k := rfl
  have hk0 : p₀.k * p₀.k ≤ 1200 * m := by rw [h.hk₀, ← pow_two]; exact h.hCk2
  have hk1 : p₁.k * p₁.k ≤ 1200 * m := by rw [h.hk₁, ← pow_two]; exact h.hCk2
  have hEZ : p₁.END - fbZ (Frame.spB0 k) k m w b p₀ p₁ ≤ 100000 * m + 16 * (b * b) := by
    have := h.hnD₀; have := h.hnD₁; have := h.hnV₀; have := h.hnV₁; have := h.hnF₀
    have := h.hnF₁; have := h.hk₀; have := h.hk₁; have := h.hCk; have := h.hm'
    have := h.hk2; have := h.hw2
    rw [hYZ, hS] at hI0₀
    generalize fbZ (Frame.spB0 k) k m w b p₀ p₁ = z at *
    generalize b * b = bb at *
    generalize p₀.k * p₀.k = q₀ at *
    generalize p₁.k * p₁.k = q₁ at *
    omega
  have hk2 := h.hk2
  have hw2 := h.hw2
  have hbw := h.hbw
  have hm' := h.hm'
  have hVF := h.hVF
  have hCk := h.hCk
  have hnD₀ := h.hnD₀
  have hnD₁ := h.hnD₁
  unfold fsCost fsMidCost fsP3aCost fbJCost fbC1Cost fbC2Cost pnCost Frame.wsCost fbPreCost
    fsNodeCost fbYesCost fbClrCost fbRCost fsNcF fsKC
  generalize ndRunCost C m m w b Ck Ck p₀ p₁ = R at *
  generalize p₁.END - fbZ (Frame.spB0 k) k m w b p₀ p₁ = ez at *
  rw [hlg] at sp rn
  rw [hbfY] at bf
  generalize m * lg m = X at *
  generalize (b + 1) ^ 2 * lg b = Y at *
  generalize b * b = bb at *
  generalize Frame.fsP1Cost m k = f1 at *
  generalize bfCostP b = bc at *
  generalize Frame.spWs k = sw at *
  generalize rnCost m w = rc at *
  omega

/-- **The cost bound against the node's charge**: `fsNcF m b ≤ 10¹² · node + fsKC`
(`sep m = C m lg m` with `C ≥ 200000`, `bf b = 7900 (b+1)² lg b`). -/
theorem fsNcF_node {C : ℕ} (hC : 200000 ≤ C) (m b m₀ w₀ m₁ w₁ : ℕ) :
    fsNcF m b ≤ 10 ^ 12 * (cNegMach C).node m b m₀ w₀ m₁ w₁ + fsKC := by
  have hs : 200000 * (m * lg m) ≤ (cNegMach C).sep m := by
    show _ ≤ C * m * lg m
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hC
  have hb : 7900 * ((b + 1) ^ 2 * lg b) = (cNegMach C).bf b := by
    show _ = 7900 * (b + 1) ^ 2 * lg b; ring
  have hn : (cNegMach C).sep m + (cNegMach C).bf b ≤ (cNegMach C).node m b m₀ w₀ m₁ w₁ := by
    unfold NegCosts.node; omega
  unfold fsNcF
  generalize (cNegMach C).node m b m₀ w₀ m₁ w₁ = nd at hn ⊢
  generalize (cNegMach C).sep m = sp at hs hn
  generalize (cNegMach C).bf b = bf at hb hn
  generalize m * lg m = X at hs
  generalize (b + 1) ^ 2 * lg b = Y at hb
  omega

/-- The room bound of the full branch (closed, monotone). -/
def fsRoomB (m k w b : ℕ) : ℕ :=
  200 * k + Frame.spWs k + (2 * (12 * (32886 * 2372500000)) + 3000000) * (m * lg m) +
    4 * (7900 * ((b + 1) ^ 2 * lg b)) + 300 * (b * b) + 1000 * b +
    (pcCost pnL1 + pcCost pnL2 + hpCost (hfPrmL 0) + hpCost (hfPrmL 0) + hpCost hnPrmL) + 50000 +
    5 * (m + w) + 8 * (w + 1) + 1

theorem fsRoom_le (C : ℕ) {m k w b m' nV nF Ck : ℕ} {p₀ p₁ : FeP}
    (h : FsEnv m k w b m' nV nF Ck p₀ p₁) : fsRoom C m k w b Ck p₀ p₁ ≤ fsRoomB m k w b := by
  have hR := ndRun_env_le C h
  have bf := bfCostP_le b
  have hbfY : 7900 * (b + 1) ^ 2 * lg b = 7900 * ((b + 1) ^ 2 * lg b) := by ring
  rw [hbfY] at bf
  unfold fsRoom fsRoomB
  generalize ndRunCost C m m w b Ck Ck p₀ p₁ = R at *
  generalize bfCostP b = bc at *
  omega

theorem fsRoomB_mono {m k w b m' k' w' b' : ℕ} (hm : m ≤ m') (hk : k ≤ k') (hw : w ≤ w')
    (hb : b ≤ b') : fsRoomB m k w b ≤ fsRoomB m' k' w' b' := by
  unfold fsRoomB
  have h1 := Frame.spWs_mono hk
  have h2 : m * lg m ≤ m' * lg m' := Nat.mul_le_mul hm (lg_mono hm)
  have h3 : (b + 1) ^ 2 * lg b ≤ (b' + 1) ^ 2 * lg b' :=
    Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) (lg_mono hb)
  have h4 : b * b ≤ b' * b' := Nat.mul_le_mul hb hb
  gcongr

end NegSSSP

end PlanarFlow
