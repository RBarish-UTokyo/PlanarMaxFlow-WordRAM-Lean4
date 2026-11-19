module

public import PlanarFlow.BKMNW.MfStep

/-!
# The steps of `stepPO` against the charge of the node runs, and the whole program

* `nodeRuns_eq_sum` (the charge `SubCosts.nodeRuns` as a sum over the parts);
* **`stTO_le`**: when every subroutine program runs within its field of the charge of the article
  (`fixRun` for FixConservationOnPath, `c2sRun` for each of `c2s`/`s2c`, `pushRun + lin` for each
  push-back) and `lin N ≥ 8`, the steps of `stepPO` are at most
  `cnT x + 4 + runsCharge c x` (`cnT` the steps of the counts);
* **`mfDriveFrame_cMachX`**: `mfDriveFrame_cMach` with the step allowed
  `runsCharge + cs m + 100 m + 100 k + 106` steps (`m` darts, `k` holes, `cs` a share of the
  separator's budget: `sT m + cs m ≤ C m lg m`), for `C ≥ 100`;
* **`mfMain_cMachX`**: the same for the whole program `rfProg ; driver …` (`mfMain_cMach`);
* **`mfMain_cMachO`**: the whole program with the concrete step
  `stepPO cntP fixP c2sP s2cP retP frmP`: hypotheses `SepPSpec sepP` and the six specifications of
  the subroutine programs of the step with their costs in the fields of `cMach`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine NegSSSP.Driver

universe w

/-- **The charge of the parts as a sum.** -/
lemma nodeRuns_eq_sum (c : SubCosts) (n nf N h a : ℕ) : ∀ L : List (ℕ × ℕ),
    c.nodeRuns n nf N h a L = ∑ j ∈ range L.length,
      c.nodeRun n nf N (L.getD j (0, 0)).1 (L.getD j (0, 0)).2 (h + (L.length - (j + 1)))
        (a + (L.length - (j + 1)))
  | [] => rfl
  | xk :: L => by
    rw [SubCosts.nodeRuns, nodeRuns_eq_sum c n nf N h a L, List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    have e1 : L.length + 1 - (0 + 1) = L.length := by omega
    rw [e1, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have e2 : L.length + 1 - (j + 1 + 1) = L.length - (j + 1) := by omega
    rw [e2]

section Gen

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable {O : PlaneOracles.{w}} {u : D → ℤ} {S T : Finset V} {cnT : MCall M → ℕ}
  {fT rtT fmT : MCall M → ℕ → ℕ} {cT sT : MCall M → ℕ → ℕ → ℕ}

/-- **The steps of `stepPO` against the charge of the node runs** (see the module docstring). -/
theorem stTO_le (c : SubCosts) {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D}
    (h : SCond M l r π Hs σ)
    (hlin : 0 < (pdarts M (l.piece ∪ r.piece) Hs).card →
      8 ≤ c.lin (psize M σ (pdarts M (l.piece ∪ r.piece) Hs)))
    (hf : ∀ j πj, (xCtx M O u S T l r π Hs σ h).L[j]? = some πj →
      fT (.node l r π, Hs, σ) j ≤ c.fixRun (pdarts M (l.piece ∪ r.piece) Hs).card
        πj.faces.card πj.k (psize M σ (pdarts M (l.piece ∪ r.piece) Hs)))
    (hc : ∀ j πj i, (xCtx M O u S T l r π Hs σ h).L[j]? = some πj →
      cT (.node l r π, Hs, σ) j i ≤ c.c2sRun (pdarts M (l.piece ∪ r.piece) Hs).card
        (nOrb (σ * revPerm M) (pdarts M (l.piece ∪ r.piece) Hs))
        (psize M σ (pdarts M (l.piece ∪ r.piece) Hs)) πj.faces.card πj.k)
    (hs : ∀ j πj i, (xCtx M O u S T l r π Hs σ h).L[j]? = some πj →
      sT (.node l r π, Hs, σ) j i ≤ c.c2sRun (pdarts M (l.piece ∪ r.piece) Hs).card
        (nOrb (σ * revPerm M) (pdarts M (l.piece ∪ r.piece) Hs))
        (psize M σ (pdarts M (l.piece ∪ r.piece) Hs)) πj.faces.card πj.k)
    (hr : ∀ j πj, (xCtx M O u S T l r π Hs σ h).L[j]? = some πj →
      rtT (.node l r π, Hs, σ) j ≤ c.pushRun (pdarts M (l.piece ∪ r.piece) Hs).card
        (nOrb (σ * revPerm M) (pdarts M (l.piece ∪ r.piece) Hs))
        (psize M σ (pdarts M (l.piece ∪ r.piece) Hs)) +
        c.lin (psize M σ (pdarts M (l.piece ∪ r.piece) Hs)))
    (hm : ∀ j πj, (xCtx M O u S T l r π Hs σ h).L[j]? = some πj →
      fmT (.node l r π, Hs, σ) j ≤ c.pushRun (pdarts M (l.piece ∪ r.piece) Hs).card
        (nOrb (σ * revPerm M) (pdarts M (l.piece ∪ r.piece) Hs))
        (psize M σ (pdarts M (l.piece ∪ r.piece) Hs)) +
        c.lin (psize M σ (pdarts M (l.piece ∪ r.piece) Hs))) :
    stTO M cnT fT cT sT rtT fmT (.node l r π, Hs, σ) ≤
      cnT (.node l r π, Hs, σ) + 4 + runsCharge M c l r π Hs σ := by
  have h' : PieceInv M (l.piece ∪ r.piece) Hs σ ∧
      ∀ s ∈ π.segs, SegIn M (l.piece ∪ r.piece) Hs s := h
  have hLs : (segsP h.1 π.segs h.2).length = π.segs.length := length_segsP h.1 π.segs h.2
  have hL'len : ((segsP h.1 π.segs h.2).map fun s => (s.faces.card, s.k)).length =
      π.segs.length := by rw [List.length_map]; exact hLs
  show stCost cnT fT cT sT rtT fmT (.node l r π, Hs, σ) π.segs.length
      (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs).length ≤ _
  unfold runsCharge
  rw [dite_of_pos h', nodeRuns_eq_sum, hL'len]
  unfold stCost
  have arith : ∀ x SA SB : ℕ, SA ≤ SB → x + 2 + (SA + 2) ≤ x + 4 + SB := by intros; omega
  refine arith _ _ _ (Finset.sum_le_sum fun j hj => ?_)
  rw [mem_range] at hj
  obtain ⟨πj, hj'⟩ : ∃ πj, (segsP h.1 π.segs h.2)[j]? = some πj :=
    ⟨_, List.getElem?_eq_getElem (by rw [hLs]; exact hj)⟩
  have hget : ((segsP h.1 π.segs h.2).map fun s => (s.faces.card, s.k)).getD j (0, 0) =
      (πj.faces.card, πj.k) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hj']; rfl
  rw [hget]
  -- the piece map has a dart
  have hn : 0 < (pdarts M (l.piece ∪ r.piece) Hs).card := by
    have hmem : π.segs[j]'hj ∈ π.segs := List.getElem_mem _
    obtain ⟨x, -⟩ := (h.2 _ hmem).1
    exact Finset.card_pos.2 ⟨x.1, x.2⟩
  have h8 := hlin hn
  have f1 := hf j πj hj'
  have f2 := hr j πj hj'
  have f3 := hm j πj hj'
  have hhl : hlCost cT sT (.node l r π, Hs, σ) j
      ((pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs).length + (π.segs.length - (j + 1))) ≤
      ((pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs).length + (π.segs.length - (j + 1))) *
        (2 * c.c2sRun (pdarts M (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm M) (pdarts M (l.piece ∪ r.piece) Hs))
          (psize M σ (pdarts M (l.piece ∪ r.piece) Hs)) πj.faces.card πj.k + 3) := by
    unfold hlCost
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) (by rw [sum_const, card_range, smul_eq_mul])
    have := hc j πj i hj'; have := hs j πj i hj'; omega
  unfold sgCost SubCosts.nodeRun
  dsimp only
  generalize (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs).length +
    (π.segs.length - (j + 1)) = nH at hhl ⊢
  generalize c.c2sRun (pdarts M (l.piece ∪ r.piece) Hs).card
    (nOrb (σ * revPerm M) (pdarts M (l.piece ∪ r.piece) Hs))
    (psize M σ (pdarts M (l.piece ∪ r.piece) Hs)) πj.faces.card πj.k = X at hhl ⊢
  generalize c.lin (psize M σ (pdarts M (l.piece ∪ r.piece) Hs)) = Ln at h8 f2 f3 ⊢
  have a1 : nH * (2 * X + 3) = nH * (2 * X) + nH * 3 := by ring
  have a2 : nH * (2 * X + Ln) = nH * (2 * X) + nH * Ln := by ring
  have a3 : nH * 3 ≤ nH * Ln := Nat.mul_le_mul_left _ (by omega)
  omega

end Gen

section Head

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **`mfDriveFrame_cMach` with room for the counts of the step** (see the module docstring):
the step may take `runsCharge + cs m + 100 m + 100 k + 106` steps at a node call (`m` the darts of
its piece map, `k` its holes), with `sT m + cs m ≤ C m lg m` and `C ≥ 100`; same conclusion and
bound. -/
theorem mfDriveFrame_cMachX (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _) {C C₀ : ℕ} (hC : 100 ≤ C)
    (hC₀ : 20 ≤ C₀) {I : Input} {W Hb Z : ℕ} {gid : _ → ℕ} {sepP stepP : Stmt} {sT cs : ℕ → ℕ}
    {sR : ℕ → ℕ → ℕ} {stT rT : MCall (lpreMap M) → ℕ} {RS RT : ℕ} (hZ : 2 * Z ≤ W) :
    let pc := pcChoiceE (lpreMap M) (pendQ _) e n d₀
    let sc := fun Hs A W => scChoiceE (lpreMap M) (sepM (lpreMap M)) e n Hs A W
    let τ := decS (lpreMap M) (spSR (lpreMap M) pc sc (pendQ _))
      (spHR (lpreMap M) pc sc (pendQ _))
      (smD (lpreMap M) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMap M) (pendQ _)) 100000 univ [] (rootRot (lpreMap M) (pendQ _)) true
    let u' := preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)
    let S' := preTerm (nlTerm M S)
    let T' := preTerm (nlTerm M T)
    let Reach := Calls (lpreMap M) τ [] (rotPerm (lpreMap M))
    let N := τ.piece.card
    SepPSpec (lpreMap M) Reach gid u' S' T' Z I W sepP sT sR →
    StepPSpec (lpreMap M) (planeOracles fun X => frRef X) Reach gid u' S' T' Z I W stepP stT rT →
    (∀ m, sT m + cs m ≤ C * m * lg m) →
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      stT (.node l r π, Hs, σ) ≤ runsCharge (lpreMap M) (cMach C C₀) l r π Hs σ +
        cs (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card +
        100 * (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card + 100 * Hs.length + 106) →
    (∀ m k, m ≤ N → k ≤ N → sR m k ≤ RS) → (∀ x, Reach x → rT x ≤ RT) →
    0 < Hb → ∀ {eF h : ℕ} (c₀ : Config), WordsBounded W c₀ → c₀.nreg 3000 = 0 →
    c₀.nreg 3001 = 1 → c₀.nreg 3002 = Hb → c₀.nreg 3003 = h → c₀.nmem Hb = 0 →
    c₀.nmem (Hb + 1) = 0 → c₀.nmem (Hb + 2) = eF → Hb + 5 ≤ eF → eF ≤ h →
    h + (2 * N + 1) * (39 * N + 20 + RS + RT) ≤ W →
    FInL (lpreMap M) Reach gid u' S' T' Z (τ, [], rotPerm (lpreMap M)) (Hb + 5) eF c₀ →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (driver mtProg mlProg (splitS sepP) (nodeSF stepP)) c₀ c' t ∧
      t ≤ (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C * Fintype.card D *
            lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        1000 * (2 * N + 1) + 2 ∧
      FOutL (lpreMap M) gid u' S' T' Z (τ, [], rotPerm (lpreMap M))
        (arunL (lpreMap M) (planeOracles fun X => frRef X) u' S' T' τ [] (rotPerm (lpreMap M)))
        (Hb + 5) eF c' ∧
      IsMax M u S T (nlRun M u S T τ (planeOracles fun X => frRef X)) := by
  intro pc sc τ u' S' T' Reach N hsep hstep hsT hstT hsR hrT hHb eF h c₀ hc₀ r0 r1 r2 r3 m0 m1
    m2 he hh hroom hin
  obtain ⟨hbal, hmax, hcost⟩ := maxflow_plane_cost_decM hM hrot hface hu hST e hsurj d₀
    (cMach_bounds C C₀)
  have hcore := ADec.BalA.core hbal.2.2.2.2
  have hsz := asize_le hcore
  have hok0 := hin.2.1
  have hsize : ∀ x, Reach x → (pdarts (lpreMap M) x.1.piece x.2.1).card ≤ N ∧
      x.2.1.length ≤ N ∧ x.1.piece.card ≤ N := fun x hx => by
    have h1 := calls_size τ [] _ x hcore hx
    have h2 := card_le_card (pdarts_subset (M := lpreMap M) x.1.piece x.2.1)
    simp only [List.length_nil, zero_add] at h1
    exact ⟨by omega, by omega, by omega⟩
  have hR : ∀ x, Reach x → rSp (lpreMap M) sR x + rT x ≤ 39 * N + 20 + RS + RT := fun x hx => by
    obtain ⟨a1, a2, -⟩ := hsize x hx
    have := hsR _ _ a1 a2
    have := hrT x hx
    unfold rSp; omega
  have hrm := roomC_le_on (M := lpreMap M) (rL := fun _ => 0) (rS := rSp (lpreMap M) sR)
    (rN := rT) Reach (fun _ _ => Nat.zero_le _) hR τ [] (rotPerm (lpreMap M)) (fun x hx => hx)
  have hsz' := Nat.mul_le_mul_right (39 * N + 20 + RS + RT) hsz
  obtain ⟨c', t, ex, ht, hout, -, -⟩ := mfDriveFrame hsep
    (fun l r π Hs σ hx => calls_child τ [] _ l r π Hs σ hx) hZ (nodeSF_spec (Hb := Hb) hstep)
    hHb τ [] (rotPerm (lpreMap M)) c₀ hc₀ r0 r1 r2 r3 m0 m1 m2 he hh
    ((Nat.add_le_add_left (hrm.trans hsz') h).trans hroom) hin
  have hm := mcost_le_on (M := lpreMap M) (tc := fun _ => 3)
    (lc := fun x => 20 * (pdarts (lpreMap M) x.1.piece x.2.1).card + 17)
    (sc := scp (lpreMap M) sT) (nc := ncF (lpreMap M) stT) (cMach C C₀) (A := 1) (B := 1000)
    Reach (fun Q Hs σ _ => by
      have := Nat.mul_le_mul_right (pdarts (lpreMap M) Q Hs).card hC₀
      simp only [cMach, ADec.piece]; omega)
    (fun l r π Hs σ hx => by
      have hok := callOk_calls τ [] _ _ hok0 hx
      have hcond := callOk_cond hok
      rw [nodeCharge_eq _ hcond]
      obtain ⟨a1, a2, a3⟩ := hsize _ hx
      have hs := hstT l r π Hs σ hx
      simp only [ADec.piece] at a1 a3
      set P := (l.piece ∪ r.piece).card with hP
      set m := (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card with hmdef
      have hmP : m ≤ P := card_le_card (pdarts_subset _ _)
      have e1 : sT m + cs m ≤ C * P * lg P := (hsT m).trans
        (Nat.mul_le_mul (Nat.mul_le_mul_left _ hmP) (lg_mono hmP))
      have e2 : 644 * m + 121 * Hs.length ≤ 8 * (C * (P + Hs.length)) := by
        have h1 : 100 * P ≤ C * P := Nat.mul_le_mul_right P hC
        have h2 : 100 * Hs.length ≤ C * Hs.length := Nat.mul_le_mul_right _ hC
        rw [Nat.mul_add C P Hs.length]
        omega
      have es : (cMach C C₀).sep P = C * P * lg P := rfl
      have el : (cMach C C₀).lin (P + Hs.length) = C * (P + Hs.length) := rfl
      rw [es, el]
      simp only [scp, ncF, ADec.piece]
      rw [← hmdef]
      omega)
    τ [] (rotPerm (lpreMap M)) (fun x hx => hx)
  have ha : arunLCost (lpreMap M) (cMach C C₀) τ [] (rotPerm (lpreMap M)) ≤
      runLCost (lpreMap M) (cMach C C₀) τ := by
    unfold runLCost; omega
  have hB : 1000 * asize τ ≤ 1000 * (2 * N + 1) := Nat.mul_le_mul_left 1000 hsz
  refine ⟨hbal.1, c', t, ex, ?_, hout, hmax⟩
  have := ha.trans hcost
  omega

end Head

end MfDrv

end BKMNW

end PlanarFlow
