module

public import PlanarFlow.BKMNW.LsO
public import PlanarFlow.BKMNW.SmSegsW
public import PlanarFlow.BKMNW.LrW

/-!
# **`SepPSpecXLS' sepL`**

**`sepL_spec`** (see `LsO.lean`): the large-piece separator program meets `SepPSpecXLS'` with
steps `sTL n k = 1010000 n lg n + 400 k` and room `sRL`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- **The large-piece separator program meets `SepPSpecXLS'`** (see `LsO.lean`). -/
theorem sepL_spec {gid : D → ℕ} {ν : V → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {ds : DSys M}
    {Reach : MCall M → Prop} {κ : ℕ} {eG : ℕ → D} {N : ℕ} {d₀ : D}
    (hF : SplitFnsS M S T κ ds.s (CInvS M ds.Q)
      (spSR M (pcChoiceE M ds.Q eG N d₀) (s5sc M eG N) ds.Q)
      (spHR M (pcChoiceE M ds.Q eG N d₀) (s5sc M eG N) ds.Q) (smD M ds.pk S T) (chRot M ds.Q))
    (hsm : ∀ P Hs, RevClosed M P → (smD M ds.pk S T P Hs).piece = P)
    (hdS : ds.spS = guardS M (gSz M S T ds.s (CInvS M ds.Q))
      (spSR M (pcChoiceE M ds.Q eG N d₀) (s5sc M eG N) ds.Q))
    (hdH : ds.spH = guardS M (gHl M S T ds.s (CInvS M ds.Q))
      (spHR M (pcChoiceE M ds.Q eG N d₀) (s5sc M eG N) ds.Q))
    (hdC : ds.chS = chRot M ds.Q) (hds : ds.s = 100000)
    (hdpk : ds.pk = (pcChoiceE M ds.Q eG N d₀).pick)
    (hSTQ : S ∪ T ⊆ ds.Q) (hloopM : ∀ d, M.head d ≠ M.tail d)
    (hQdeg : ∀ q ∈ ds.Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ ds.Q ∧ M.head d ∈ ds.Q)) (hTS : TailSorted M gid ν)
    (hQ : QPar ds.Q ν) (hν : Injective ν) (hgid : Injective gid)
    (he : ∀ i < N, gid (eG i) = i) (hesurj : ∀ d, ∃ i < N, eG i = d) (hsW : 100000 ≤ W) :
    SepPSpecXLS' M ds Reach gid ν u S T Z I W sepL sTL sRL := by
  intro l r π Hs σ d e h Sb m en c hin hLy hph0 hlarge hc r4 r5 r3 r50 heh hhS hw
  obtain ⟨hReach, hok, m', en', n, g, hL', hp1, hsz, hLR⟩ := hin
  have hmm : m' = m := hL'.card.trans hLy.card.symm
  subst hmm
  have hf : fsz m' = 4 + 7 * m' := rfl
  obtain ⟨R, hRdef⟩ : ∃ R, c.nmem (d + fsz m') = R := ⟨_, rfl⟩
  rw [hRdef] at hp1 hsz hLR hph0 hlarge
  have hRn : c.nmem R = n := hLR.hn
  have hA := hLR.arr (by rw [hph0]; omega)
  have hnc : n = (l.piece ∪ r.piece).card := hA.card
  have hmn : m' ≤ n := by rw [hLy.card, hnc]; exact card_le_card (pdarts_subset _ _)
  have hsz' : R + (3 + 6 * n + m') ≤ e := by
    have : rszL (c.nmem (R + 1)) n m' = 3 + 6 * n + m' := by
      unfold rszL; rw [iteT (by rw [hph0]; omega)]
    rw [← this]; exact hsz
  have lR : R + 3 + 6 * n + m' ≤ Sb := by omega
  have hs : ds.s < (ADec.node l r π).piece.card := by
    show ds.s < (l.piece ∪ r.piece).card; rw [← hnc, ← hRn]; exact hlarge
  have hs' : 100000 < (l.piece ∪ r.piece).card := by rw [← hds]; exact hs
  -- the state of the call
  have hph := hLR.ph
  rw [hph0] at hph
  obtain ⟨st, hPc0, hCI0, hnt0, hSP0, hnode⟩ := s5_state_of_phOk hF hsm hdS hdH hdC hph hs
  have hPc : PcOK M S T (l.piece ∪ r.piece) Hs := hPc0
  have hCI : CInvS M ds.Q (l.piece ∪ r.piece) Hs st := hCI0
  have hnt : nTouch M (l.piece ∪ r.piece) Hs ≤ 6 := hnt0
  have hSP : ∀ i < n, g i ∈ pdarts M (core M ds.Q (l.piece ∪ r.piece)) Hs →
      c.nmem (R + 3 + 5 * n + i) < n ∧ g (c.nmem (R + 3 + 5 * n + i)) = st (g i) := hSP0
  clear hPc0 hCI0 hnt0 hSP0
  set bfl := c.nmem (R + 2) with hbfl
  have hb : bfl ≤ 1 := hLR.hb
  have hdec : decS M (guardS M (gSz M S T ds.s (CInvS M ds.Q))
      (spSR M (pcChoiceE M ds.Q eG N d₀) (s5sc M eG N) ds.Q))
      (guardS M (gHl M S T ds.s (CInvS M ds.Q))
        (spHR M (pcChoiceE M ds.Q eG N d₀) (s5sc M eG N) ds.Q)) (smD M ds.pk S T) (chRot M ds.Q)
      ds.s (l.piece ∪ r.piece) Hs st (decide (bfl = 1)) = .node l r π := by
    have := hnode.symm
    unfold DSys.dec at this
    rw [hdS, hdH, hdC] at this
    exact this
  obtain ⟨-, -, h6, h5, hsplit, hok', el, er, -, -⟩ := decS_node_guard hF hsm hs hdec
  obtain ⟨hlargeL, hlargeR⟩ := guard_kid_ntag hF hsm hs hdec
  obtain ⟨Nf, ρ, Ic, hcert, hPC, hlp, hrp, hπ, hY, hC, hNf, hAw, htH, hA2⟩ :=
    ls_split hSTQ hloopM hQdeg hQ5 hPc hCI hs' h6 h5 hesurj d₀ hsplit
  have hNfe : Nf = pcNf M ds.Q (l.piece ∪ r.piece) Hs := by
    rcases ls_cert_cases hcert with ⟨-, h1, -⟩ | ⟨h0, h1, -⟩
    · exact h1
    · rw [h1, pcNf_of_core_empty h0]
  have hρπ : π.path = ρ := by rw [hπ]
  have hpk := pkMin_pcChoiceE (M := M) (Q := ds.Q) hesurj he d₀
  have hKA := ls_KA_le (b := decide (bfl = 1)) hnt
  have hFX : ∀ i < m', g (c.nmem (R + 3 + 6 * n + i)) = en i := hA.fx_en hLy
  -- word bounds
  have hW1 : Sb + sRL (l.piece ∪ r.piece).card m' Hs.length ≤ W := hw
  rw [← hnc] at hW1
  have hEB : encB' (s5Wv M (l.piece ∪ r.piece) Hs (decide (bfl = 1))) ≤ encB' (223 * n + 84) :=
    lsEncB_mono (by rw [hnc]; exact hKA.2.2)
  have hKn : s5Kv M (l.piece ∪ r.piece) Hs (decide (bfl = 1)) *
      nTouch M (l.piece ∪ r.piece) Hs ≤ s5Kv M (l.piece ∪ r.piece) Hs (decide (bfl = 1)) * 6 :=
    Nat.mul_le_mul_left _ hnt
  rw [← hnc] at hKA
  unfold sRL at hW1
  have hn1 : 1 ≤ n := by omega
  have hRm : c.nmem (d + 7 * m' + 4) = R := by
    rw [show d + 7 * m' + 4 = d + fsz m' by rw [hf]; omega]; exact hRdef
  have w5 : Sb + 21 * m' + 38 * n + 8 * Hs.length + 24 + 4 * n + 3 + 600 * n + 10 * Hs.length +
      2 * encB' (s5Wv M (l.piece ∪ r.piece) Hs (decide (bfl = 1))) +
      20 * s5Wv M (l.piece ∪ r.piece) Hs (decide (bfl = 1)) +
      s5Kv M (l.piece ∪ r.piece) Hs (decide (bfl = 1)) +
      s5Av M (l.piece ∪ r.piece) Hs (decide (bfl = 1)) + 400 ≤ W := by
    have a1 := hKA; have a2 := hEB; have a3 := hW1
    clear_value bfl
    clear * - a1 a2 a3
    generalize s5Kv M (l.piece ∪ r.piece) Hs (decide (bfl = 1)) = K at a1 a2 a3 ⊢
    generalize s5Av M (l.piece ∪ r.piece) Hs (decide (bfl = 1)) = A at a1 a2 a3 ⊢
    generalize encB' (s5Wv M (l.piece ∪ r.piece) Hs (decide (bfl = 1))) = EB at a1 a2 a3 ⊢
    generalize s5Wv M (l.piece ∪ r.piece) Hs (decide (bfl = 1)) = W₀ at a1 a2 a3 ⊢
    generalize encB' (223 * n + 84) = EB' at a1 a2 a3 ⊢
    omega
  have wK : s5Kv M (l.piece ∪ r.piece) Hs (decide (bfl = 1)) *
      nTouch M (l.piece ∪ r.piece) Hs ≤ W := by
    have a1 := hKA.1; have a3 := hW1; have a4 := hKn
    clear_value bfl
    clear * - a1 a3 a4
    generalize s5Kv M (l.piece ∪ r.piece) Hs (decide (bfl = 1)) = K at a1 a3 a4 ⊢
    generalize K * nTouch M (l.piece ∪ r.piece) Hs = KT at a1 a3 a4 ⊢
    generalize encB' (223 * n + 84) = EB' at a1 a3 a4 ⊢
    omega
  have wA : 3 * s5Av M (l.piece ∪ r.piece) Hs (decide (bfl = 1)) ≤ W := by
    have a1 := hKA.2.1; have a3 := hW1
    clear_value bfl
    clear * - a1 a3
    generalize s5Av M (l.piece ∪ r.piece) Hs (decide (bfl = 1)) = A at a1 a3 ⊢
    generalize encB' (223 * n + 84) = EB' at a1 a3 ⊢
    omega
  have w : Sb + 21 * m' + 38 * n + 8 * Hs.length + 24 + 4 * n + 3 + 55 * n + 9 * Hs.length + 17 ≤
      W := by
    have a3 := hW1
    clear * - a3
    generalize encB' (223 * n + 84) = EB' at a3 ⊢
    omega
  obtain ⟨c₁, t₁, e₁, ht₁, hR1, hL1, v59, v71, n1, n2, ix, ixp, hPD, LF, DF, VF, CC, HT, M1, F1,
    rr1, rm1, o1⟩ := lsHalf1_exec (I := I) (Q := ds.Q) (xc := (.node l r π, Hs, σ)) (en := en)
      (k := Hs.length) hloopM c hc r4 r50 hLy.hm hLy.hk hRm hRn hA rfl hFX lR
      (by omega) hTS hQ hν hPc hQdeg hQ5 hCI hnt hSP he hesurj d₀ rfl hb hgid hpk hcert hNfe hY
      hC hNf hAw htH hn1 w5 w wK wA (by omega)
  have hlr : ∀ i < n, g i ∈ r.piece ↔ g i ∉ l.piece := fun i hi => by
    have hg : g i ∈ l.piece ∪ r.piece := hA.g_mem i hi
    rw [mem_union] at hg
    constructor
    · intro h1 h2; exact disjoint_left.1 hok'.disj h2 h1
    · intro h1; rcases hg with h | h
      · exact absurd h h1
      · exact h
  have hflag : ∀ X : Finset D, decide (1 - c₁.nreg 8559 = 1) =
      !holeStep M (l.piece ∪ r.piece) Hs (decide (bfl = 1)) := fun _ => by
    rw [v59]; unfold bf; exact dec_flag_eq _
  have hl' : l = ds.dec S T l.piece (childHoles Hs π.path.mverts)
      (childRot M st (pdarts M (core M ds.Q (l.piece ∪ r.piece)) Hs) π.path.darts
        (pdarts M (core M ds.Q l.piece) (childHoles Hs π.path.mverts)))
        (decide (1 - c₁.nreg 8559 = 1)) := by
    rw [hflag l.piece]; unfold DSys.dec; rw [hdS, hdH, hdC]; exact el
  have hr' : r = ds.dec S T r.piece (childHoles Hs π.path.mverts)
      (childRot M st (pdarts M (core M ds.Q (l.piece ∪ r.piece)) Hs) π.path.darts
        (pdarts M (core M ds.Q r.piece) (childHoles Hs π.path.mverts)))
        (decide (1 - c₁.nreg 8559 = 1)) := by
    rw [hflag r.piece]; unfold DSys.dec; rw [hdS, hdH, hdC]; exact er
  have hm0 : m' = 0 → π.segs = [] := fun h0 => by
    have hLc : m' = (pdarts M (l.piece ∪ r.piece) Hs).card := hLy.card
    have hpe : pdarts M (l.piece ∪ r.piece) Hs = ∅ := by
      rw [← card_eq_zero, ← hLc, h0]
    have hB0 : pdarts M (core M ds.Q (l.piece ∪ r.piece)) Hs = ∅ :=
      Finset.subset_empty.1 (hpe ▸ core_sub_pdarts)
    rcases ls_cert_cases hcert with ⟨hne, -⟩ | ⟨-, -, hρ⟩
    · rw [hB0] at hne; exact absurd hne (by simp)
    · rw [hπ]
      show segsF ρ Hs = []
      rw [hρ, pemptyD_path, iteF (by rw [hpe]; simp)]
      apply segsF_point_hole
      have hP0 : (l.piece ∪ r.piece).Nonempty := card_pos.1 (by omega)
      have hp := (hpk _ hP0).1
      have hnp : (pcChoiceE M ds.Q eG N d₀).pick (l.piece ∪ r.piece) ∉
          pdarts M (l.piece ∪ r.piece) Hs := by rw [hpe]; exact notMem_empty _
      rw [mem_pdarts] at hnp
      have hin : Inner M Hs ((pcChoiceE M ds.Q eG N d₀).pick (l.piece ∪ r.piece)) := by
        by_contra hc'; exact hnp ⟨hp, hc'⟩
      obtain ⟨H, hH, ht, -⟩ := hin
      exact mem_hunion.2 ⟨H, hH, ht⟩
  have M1' : ∀ a, a < Sb → c₁.nmem a = c.nmem a := M1
  have hU : Sb + 21 * m' + 38 * n + 8 * Hs.length + 24 + 4 * n + 3 =
      Sb + 21 * m' + 38 * n + 8 * Hs.length + 24 + 4 * n + 3 := rfl
  obtain ⟨c₂, t₂, e₂, ht₂, O1, O2, O3, O4, tl, tr, hRO, hSO, M2, F2, rr2, rm2, o2⟩ :=
    lsHalf2_exec (I := I) (ds := ds) (en := en) (g := g) (st := st) (σ := σ)
      (hi := Sb + sRL (l.piece ∪ r.piece).card m' Hs.length) c₁ e₁.wb_right hR1 hL1 rfl
      ((F1 _ (by omega) (by omega)).trans r4) (by rw [M1' _ (by omega)]; exact hLy.hm)
      (by rw [M1' _ (by omega)]; exact hLy.hk) (by rw [M1' _ (by omega)]; exact hRm)
      (by rw [M1' _ (by omega)]; exact hRn) lR (by rw [hf] at hp1; omega) w (by omega)
      (by rw [← hnc]; unfold sRL; omega)
      (hA.congr fun a h1 h2 => M1' a (by omega)) rfl hPc.disj
      (disjoint_left.2 fun v hv hv' => disjoint_left.1 hok'.sepT hv' (mem_union_left _ hv))
      (disjoint_left.2 fun v hv hv' => disjoint_left.1 hok'.sepT hv' (mem_union_right _ hv))
      (disjoint_left.2 fun v hv hv' => disjoint_left.1 hPc.term hv' (mem_union_left _ hv))
      hCI.pmap.stable
      (fun i hi hg => by rw [M1' _ (by omega)]; exact hSP i hi hg)
      (fun i hi => (LF i hi).trans (by rw [hlp]; try rfl))
      (fun i hi => (VF i hi).trans (by rw [hρπ]; try rfl)) (fun j hj => (HT j hj).trans (by rw [hρπ]; try rfl))
      (fun i hi => (DF i hi).trans (by rw [hρπ]; try rfl)) CC hlr hok'.lrev hok'.rrev hl' hr' hν
      (by rw [hdpk]; exact hpk) hloopM hds hsW hlargeL hlargeR
      (fun i hi => by rw [M1' _ (by omega)]; exact ⟨hA.fx i hi, hFX i hi⟩) rfl v71 n2 n1 ix
      (fun hm q hq => hLy.en_surj _ (ixp hm q hq)) (by rw [hρπ]; exact hPD) hok'.simple
      (by rw [hπ]) hm0 (fun i hi => by rw [M1' _ (by omega)]; exact hA.hp i hi)
      (fun i hi j hj h => by
        rcases lt_trichotomy i j with hij | rfl | hij
        · have := hLy.en_mono i j hij hj; rw [h] at this; omega
        · rfl
        · have := hLy.en_mono j i hij hi; rw [h] at this; omega)
  have hBn : (pdarts M (core M ds.Q (l.piece ∪ r.piece)) Hs).card ≤ n := by
    rw [hnc]; exact card_le_card fun y hy => (mem_core.1 (mem_pdarts.1 hy).1).1
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, ?_, fun x h1 h2 => ?_, fun a ha => ⟨?_, ?_⟩, by rw [o2, o1],
    O1, O2, O3, O4, tl, tr, hRO, hSO⟩
  · rw [← hnc]; exact sepL_time hn1 hmn hBn hKA.2.2 ht₁ ht₂
  · rw [F2 x h1 h2, F1 x h1 h2]
  · rw [M2 a ha, M1' a ha]
  · rw [rm2, rm1]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
