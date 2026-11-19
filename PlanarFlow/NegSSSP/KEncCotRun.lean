module

public import PlanarFlow.NegSSSP.KEncCot

/-!
# The search recording its parents: the loops, and the tree of the recorded parents

Continuing `PlanarFlow/NegSSSP/KEncCot.lean`:

* `ctVert_exec`: **the vertex at the head of the queue** (`bfsVert_exec` with `CtSt`), within
  `9 + 17 deg` steps.
* `ctProg_exec`: **the whole search with its parents**: within `35 nV + 19 m + 12` steps, the
  queue holds exactly the vertices reached from the source, every one but the source with its
  recorded parent arc out of an earlier queued vertex (`CtSt`), the marks are the reach bits.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Relation WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge

variable {P : Input} {W : ℕ}

variable {nV m nA s OBb OEb OLb HDb Mb Qb Ib PAb : ℕ} {ob oe ol hd : ℕ → ℕ}

/-! ### One vertex -/

set_option maxHeartbeats 2000000 in
/-- **The vertex at the head of the queue**: dequeued, its out-arcs scanned (`ctArc_exec`); then
its out-neighbours are queued, with their parent arcs, within `9 + 17 deg` steps. -/
theorem ctVert_exec (hL : BfsLay nV m nA OBb OEb OLb HDb Mb Qb Ib W) (hqp : Qb + nV ≤ PAb)
    (hpw : PAb + nV ≤ W) (c : Config)
    (hc : WordsBounded W c) (hR : BfsRegs OBb OEb OLb HDb Mb Qb c) (r08 : c.nreg 1408 = PAb)
    (hI : BfsIn nV m nA s OBb OEb OLb HDb ob oe ol hd c.nmem) {qh qt : ℕ}
    (hS : CtSt nV s Mb Qb PAb qt ob oe ol hd c.nmem)
    (hcl : BfsClosed Qb qh qt (BfsAdj ob oe ol hd) c.nmem) (hq : qh < qt)
    (r13 : c.nreg 1413 = qh) (r14 : c.nreg 1414 = qt) :
    ∃ c' t, Exec P W ctVert c c' t ∧
      t ≤ 9 + 17 * (oe (c.nmem (Qb + qh)) - ob (c.nmem (Qb + qh))) ∧
      (BfsRegs OBb OEb OLb HDb Mb Qb c' ∧
        (∀ a, a < Mb ∨ Qb + nV ≤ a → a < PAb ∨ PAb + nV ≤ a → c'.nmem a = c.nmem a) ∧
        c'.nreg 1413 = qh + 1 ∧
        ∃ qt', qt ≤ qt' ∧ c'.nreg 1414 = qt' ∧
          CtSt nV s Mb Qb PAb qt' ob oe ol hd c'.nmem ∧
          (∀ j < qt, c'.nmem (Qb + j) = c.nmem (Qb + j)) ∧
          BfsClosed Qb (qh + 1) qt' (BfsAdj ob oe ol hd) c'.nmem) ∧
        (∀ r, r < 1410 ∨ 1420 < r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
        c'.output = c.output := by
  classical
  have := hL.ob; have := hL.oe; have := hL.ol; have := hL.hd; have := hL.im; have := hL.mq
  have := hL.qw
  have hqt := hS.st.le
  set u := c.nmem (Qb + qh) with hu_def
  have hu : u < nV := hS.st.qlt qh hq
  have xo : c.nmem (OBb + u) = ob u := hI.hob u hu
  have xe : c.nmem (OEb + u) = oe u := hI.hoe u hu
  have hbe := hI.ble u hu
  have hem := hI.ole u hu
  obtain ⟨r02, r03, r04, r05, r06, r07, r10, r19⟩ := hR
  unfold ctVert
  refine spec_seq ?_
  exec_block
  all_goals try ((try config_simp); (try simp only [r02, r03, r07, r10, r13, ← hu_def]); omega)
  -- the scan of the out-arcs
  let I : Config → Prop := fun d =>
    WordsBounded W d ∧ BfsRegs OBb OEb OLb HDb Mb Qb d ∧
      (∀ a, a < Mb ∨ Qb + nV ≤ a → a < PAb ∨ PAb + nV ≤ a → d.nmem a = c.nmem a) ∧
      d.nreg 1413 = qh + 1 ∧ d.nreg 1416 = oe u ∧ ob u ≤ d.nreg 1411 ∧ d.nreg 1411 ≤ oe u ∧
      (∃ qt', qt ≤ qt' ∧ d.nreg 1414 = qt' ∧ CtSt nV s Mb Qb PAb qt' ob oe ol hd d.nmem ∧
        (∀ j < qt, d.nmem (Qb + j) = c.nmem (Qb + j)) ∧
        BfsClosed Qb qh qt' (BfsAdj ob oe ol hd) d.nmem ∧
        ∀ i, ob u ≤ i → i < d.nreg 1411 → ∃ j < qt', d.nmem (Qb + j) = hd (ol i)) ∧
      (∀ r, r < 1410 ∨ 1420 < r → d.nreg r = c.nreg r) ∧ d.rreg = c.rreg ∧ d.rmem = c.rmem ∧
      d.output = c.output
  refine spec_while I (fun d => 17 * (oe u - d.nreg 1411)) (fun d h => h.1) ?_ ?_ ?_
  · intro d ⟨hw, hRd, hmd, d13, d16, d11a, d11b, ⟨qt', hqt', d14, hSd, hpre, hcld, hsc⟩, dn, drr,
      drm, dout⟩ hlt
    rw [d16] at hlt
    have hId := hI.frame hL fun a ha => hmd a (Or.inl ha) (Or.inl (by omega))
    have d08 : d.nreg 1408 = PAb := (dn 1408 (by omega)).trans r08
    have hQu : d.nmem (Qb + qh) = u := hpre qh hq
    obtain ⟨d', k, ex, hk, ⟨qt'', hq'', e14, hS'', hin, hpre'⟩, e11, en, em, err, erm, eo⟩ :=
      ctArc_exec (P := P) (qh := qh) hL hqp hpw d hw hRd d08 hId hSd (by omega) (by rw [hQu]; exact d11a)
        (by rw [hQu]; exact hlt) rfl d14
    refine ⟨d', k, ex, ⟨ex.wb_right, hRd.frame fun r h1 h2 => en r (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), fun a ha ha' => by rw [em a ha ha', hmd a ha ha'],
      by rw [en _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), d13],
      by rw [en _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), d16],
      by omega, by omega, ⟨qt'', by omega, e14, hS'', fun j hj => by
        rw [hpre' j (by omega), hpre j hj], fun j hj v hv => ?_, fun i h1 h2 => ?_⟩,
      fun r hr => by
        rw [en r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), dn r hr],
      by rw [err, drr], by rw [erm, drm], by rw [eo, dout]⟩, by omega⟩
    · rw [hpre' j (by omega)] at hv
      obtain ⟨j', hj', e⟩ := hcld j hj v hv
      exact ⟨j', by omega, by rw [hpre' j' hj']; exact e⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 (show i < d.nreg 1411 + 1 by omega) with h2 | rfl
      · obtain ⟨j', hj', e⟩ := hsc i h1 h2
        exact ⟨j', by omega, by rw [hpre' j' hj']; exact e⟩
      · exact hin
  · refine ⟨‹_›, ⟨by config_simp; exact r02, by config_simp; exact r03, by config_simp; exact r04,
      by config_simp; exact r05, by config_simp; exact r06, by config_simp; exact r07,
      by config_simp; exact r10, by config_simp; exact r19⟩, fun _ _ _ => rfl,
      by config_simp; simp only [r10, r13], by config_simp; simp only [r03, r07, r13, ← hu_def, xe],
      by config_simp; simp only [r02, r07, r13, ← hu_def, xo]; omega,
      by config_simp; simp only [r02, r07, r13, ← hu_def, xo]; omega,
      ⟨qt, le_rfl, by config_simp; exact r14, hS, fun _ _ => rfl, hcl, fun i h1 h2 => absurd h2
        (by config_simp; simp only [r02, r07, r13, ← hu_def, xo]; omega)⟩,
      fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> omega,
      rfl, rfl, rfl⟩
  · intro d k ⟨hw, hRd, hmd, d13, d16, d11a, d11b, ⟨qt', hqt', d14, hSd, hpre, hcld, hsc⟩, dn,
      drr, drm, dout⟩ hn hk
    rw [d16] at hn
    have d11 : d.nreg 1411 = oe u := by omega
    have hk' : k ≤ 17 * (oe u - ob u) + 2 := by
      config_simp at hk; simp only [r02, r07, r13, ← hu_def, xo] at hk; exact hk
    refine ⟨by omega, ⟨hRd, hmd, d13, qt', hqt', d14, hSd, hpre, fun j hj v hv => ?_⟩, dn, drr,
      drm, dout⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact hcld j hj v hv
    · rw [hpre j hq, ← hu_def] at hv
      obtain ⟨i, h1, h2, rfl⟩ := hv
      exact hsc i h1 (by omega)

/-! ### The whole search -/

set_option maxHeartbeats 2000000 in
open Classical in
/-- **The search with its parents.** With `r1400 … r1408` = `nV, s, OBb, OEb, OLb, HDb, Mb, Qb,
PAb` and the inputs below `Mb` (`BfsIn`), `ctProg` ends within `35 nV + 19 m + 12` steps with a
queue of `qt` vertices closed under `BfsAdj` with their recorded parents (`CtSt`), the word at
`Mb + v` equal to `1` if `v` is reached from `s` along `BfsAdj ob oe ol hd` and `0` otherwise,
for every `v < nV`; the natural memory below `Mb`, from `Qb + nV` to `PAb` and from `PAb + nV`
on, the natural registers below `1410`, the real registers and memory and the output are
kept. -/
theorem ctProg_exec (hL : BfsLay nV m nA OBb OEb OLb HDb Mb Qb Ib W) (hqp : Qb + nV ≤ PAb)
    (hpw : PAb + nV ≤ W) (c : Config)
    (hc : WordsBounded W c) (h00 : c.nreg 1400 = nV) (h01 : c.nreg 1401 = s)
    (h02 : c.nreg 1402 = OBb) (h03 : c.nreg 1403 = OEb) (h04 : c.nreg 1404 = OLb)
    (h05 : c.nreg 1405 = HDb) (h06 : c.nreg 1406 = Mb) (h07 : c.nreg 1407 = Qb)
    (h08 : c.nreg 1408 = PAb)
    (hI : BfsIn nV m nA s OBb OEb OLb HDb ob oe ol hd c.nmem) :
    ∃ c' t, Exec P W ctProg c c' t ∧ t ≤ 35 * nV + 19 * m + 12 ∧
      ((∃ qt, CtSt nV s Mb Qb PAb qt ob oe ol hd c'.nmem ∧
          BfsClosed Qb qt qt (BfsAdj ob oe ol hd) c'.nmem) ∧
        (∀ v < nV, c'.nmem (Mb + v) = if ReflTransGen (BfsAdj ob oe ol hd) s v then 1 else 0) ∧
        (∀ a, a < Mb ∨ Qb + nV ≤ a → a < PAb ∨ PAb + nV ≤ a → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 1410 ∨ 1420 < r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
        c'.output = c.output) := by
  classical
  have := hL.ob; have := hL.oe; have := hL.ol; have := hL.hd; have := hL.im; have := hL.mq
  have := hL.qw
  have hs := hI.s_lt
  unfold ctProg bfsClear
  refine spec_seq ?_
  refine spec_seq ?_
  exec_block
  all_goals try omega
  -- the marks cleared
  let J : ℕ → Config → Prop := fun i d =>
    (∀ v < i, d.nmem (Mb + v) = 0) ∧ (∀ a, a < Mb ∨ Mb + nV ≤ a → d.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 1410 → r ≠ 1411 → r ≠ 1412 → r ≠ 1419 → d.nreg r = c.nreg r) ∧
      d.nreg 1410 = 1 ∧ d.nreg 1419 = 0 ∧ d.rreg = c.rreg ∧ d.rmem = c.rmem ∧
      d.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 1411) (bR := 1400)
    (body := block [.addN 1412 1406 1411, .storeN 1412 1419, .addN 1411 1411 1410]) J (K := 3)
    (n := nV) _ ‹_› (by config_simp) (by config_simp; exact h00) ?_
    (fun i d hi hw ha hb ⟨g, gm, gn, g10, g19, gr, grm, go⟩ => by
      have e06 : d.nreg 1406 = Mb := (gn 1406 (by omega) (by omega) (by omega) (by omega)).trans h06
      exec_block
      all_goals try ((try config_simp); (try simp only [e06, ha, g10]); omega)
      dsimp only [J]
      refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, gr, grm, go⟩
      · config_simp; simp only [ha, g10]
      · config_simp; rw [gn 1400 (by omega) (by omega) (by omega) (by omega)]; exact h00
      · intro v hv
        simp only [e06, ha, g19, upd_apply]
        split_ifs with hvi
        · rfl
        · exact g v (by omega)
      · intro a ha'
        simp only [e06, ha, upd_apply, show a ≠ Mb + i by omega, ↓reduceIte]; exact gm a ha'
      · intro r h1 h2 h3 h4
        simp only [upd_apply, h2, h3, ↓reduceIte]; exact gn r h1 h2 h3 h4
      · config_simp; exact g10
      · config_simp; exact g19)) ?_
  · refine ⟨fun v hv => absurd hv (by omega), fun _ _ => rfl, fun r h1 h2 h3 h4 => ?_, ?_, ?_,
      rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply, h1, h2, h4, ↓reduceIte]
  intro c₁ k₁ hk₁ hw₁ ⟨_, g, gm, gn, g10, g19, gr, grm, go⟩
  -- the source marked and queued
  have q01 : c₁.nreg 1401 = s := (gn 1401 (by omega) (by omega) (by omega) (by omega)).trans h01
  have q06 : c₁.nreg 1406 = Mb := (gn 1406 (by omega) (by omega) (by omega) (by omega)).trans h06
  have q07 : c₁.nreg 1407 = Qb := (gn 1407 (by omega) (by omega) (by omega) (by omega)).trans h07
  unfold bfsStart
  refine spec_seq ?_
  exec_block
  all_goals try ((try config_simp); (try simp only [q01, q06]); omega)
  -- the queue processed
  let D : Config → ℕ := fun d =>
    ∑ j ∈ range (d.nreg 1413), (oe (d.nmem (Qb + j)) - ob (d.nmem (Qb + j)))
  let I : Config → Prop := fun d =>
    WordsBounded W d ∧ BfsRegs OBb OEb OLb HDb Mb Qb d ∧
      (∀ a, a < Mb ∨ Qb + nV ≤ a → a < PAb ∨ PAb + nV ≤ a → d.nmem a = c.nmem a) ∧
      d.nreg 1413 ≤ d.nreg 1414 ∧
      CtSt nV s Mb Qb PAb (d.nreg 1414) ob oe ol hd d.nmem ∧
      BfsClosed Qb (d.nreg 1413) (d.nreg 1414) (BfsAdj ob oe ol hd) d.nmem ∧
      (∀ r, r < 1410 ∨ 1420 < r → d.nreg r = c.nreg r) ∧ d.rreg = c.rreg ∧ d.rmem = c.rmem ∧
      d.output = c.output
  refine spec_while I (fun d => 30 * (nV - d.nreg 1413) + 19 * (m - D d)) (fun d h => h.1) ?_
    ?_ ?_
  · intro d ⟨hw, hRd, hmd, hle, hSd, hcld, dn, drr, drm, dout⟩ hlt
    have hId := hI.frame hL fun a ha => hmd a (Or.inl ha) (Or.inl (by omega))
    have d08 : d.nreg 1408 = PAb := (dn 1408 (by omega)).trans h08
    obtain ⟨d', k, ex, hk, ⟨hR', hm', e13, qt', hqt', e14, hS', hpre, hcl'⟩, en, err, erm, eo⟩ :=
      ctVert_exec (P := P) hL hqp hpw d hw hRd d08 hId hSd hcld hlt rfl rfl
    have hqn := hSd.st.le
    have hsum := hSd.st.sum_le (t := d.nreg 1413 + 1) (by omega) (fun u => oe u - ob u)
    rw [sum_range_succ] at hsum
    have hD' : D d' = D d + (oe (d.nmem (Qb + d.nreg 1413)) - ob (d.nmem (Qb + d.nreg 1413))) := by
      simp only [D, e13, sum_range_succ]
      congr 1
      · exact sum_congr rfl fun j hj => by rw [hpre j (by have := mem_range.1 hj; omega)]
      · rw [hpre _ hlt]
    have hdeg := hI.deg
    refine ⟨d', k, ex, ⟨ex.wb_right, hR', fun a ha ha' => by rw [hm' a ha ha', hmd a ha ha'], by omega,
      e14 ▸ hS', e14 ▸ e13 ▸ hcl', fun r hr => by rw [en r hr, dn r hr], by rw [err, drr],
      by rw [erm, drm], by rw [eo, dout]⟩, ?_⟩
    rw [hD', e13]
    simp only [D] at hsum ⊢
    omega
  · have G : ∀ r, 1401 ≤ r → r ≤ 1407 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
      gn r (by omega) (by omega) (by omega) (by omega)
    have hQ0 : ∀ j < 1, upd (upd c₁.nmem (Mb + s) 1) Qb s (Qb + j) = s := fun j hj => by
      rw [show j = 0 by omega]; simp
    refine ⟨‹_›, ?_, ?_, ?_, ?_, ?_, ?_, gr, grm, go⟩
    · exact ⟨by config_simp; rw [G _ (by omega) (by omega)]; exact h02,
        by config_simp; rw [G _ (by omega) (by omega)]; exact h03,
        by config_simp; rw [G _ (by omega) (by omega)]; exact h04,
        by config_simp; rw [G _ (by omega) (by omega)]; exact h05,
        by config_simp; rw [G _ (by omega) (by omega)]; exact h06,
        by config_simp; rw [G _ (by omega) (by omega)]; exact h07,
        by config_simp; exact g10, by config_simp; exact g19⟩
    · intro a ha _
      config_simp
      simp only [q01, q06, q07, g10, upd_apply, show a ≠ Qb by omega, show a ≠ Mb + s by omega,
        ↓reduceIte]
      exact gm a (by omega)
    · config_simp; omega
    · config_simp
      simp only [q01, q06, q07, g10]
      refine ⟨?_, fun j hj hj' => by omega⟩
      refine ⟨by omega, by omega, ?_, fun j hj => ?_, fun j hj j' hj' _ => by omega,
        fun v hv => ?_, fun j hj => ?_⟩
      · have := hQ0 0 (by omega); rw [Nat.add_zero] at this; exact this
      · rw [hQ0 j hj]; exact hs
      · have hiff : (∃ j < 1, upd (upd c₁.nmem (Mb + s) 1) Qb s (Qb + j) = v) ↔ s = v :=
          ⟨fun ⟨j, hj, e⟩ => by rw [hQ0 j hj] at e; exact e, fun e => ⟨0, by omega, by
            rw [hQ0 0 (by omega)]; exact e⟩⟩
        simp only [hiff]
        simp only [upd_apply, show Mb + v ≠ Qb by omega]
        by_cases hsv : s = v
        · subst hsv; simp
        · simp only [show Mb + v ≠ Mb + s by omega, hsv, ↓reduceIte]
          exact g v hv
      · rw [hQ0 j hj]
    · config_simp; intro j hj; omega
    · intro r hr
      config_simp
      simp only [upd_apply]
      split_ifs <;> first | omega | exact gn r (by omega) (by omega) (by omega) (by omega)
  · intro d k ⟨hw, hRd, hmd, hle, hSd, hcld, dn, drr, drm, dout⟩ hn hk
    have e : d.nreg 1413 = d.nreg 1414 := by omega
    rw [e] at hcld
    refine ⟨?_, ⟨_, hSd, hcld⟩, fun v hv => ?_, hmd, dn, drr, drm, dout⟩
    · simp only [D] at hk
      config_simp at hk
      simp only [range_zero, sum_empty] at hk
      omega
    · rw [hSd.st.mark v hv]
      simp only [hSd.st.reach_iff hcld v]

/-! ### The tree of the recorded parents -/

section Tree

variable {D X Y : Type*} [Fintype D] [DecidableEq D] [Fintype Y] [DecidableEq Y]
  {N : CombMap D X Y}

/-- **The search follows the darts**: with the nodes numbered by `τ` and the darts by `σ`, the
out-list of `τ y` listing (at least) the numbers of the darts `d` with `A d` of face `y`, and the
head of the arc `σ d` the number of the face of the reverse of `d`, a face reached from `r`
through darts satisfying `A` is reached by `BfsAdj` from `τ r`. -/
theorem bfsAdj_of_conn {nV nD : ℕ} (τ : Y ≃ Fin nV) (σ : D ≃ Fin nD) {A : D → Prop} {r y : Y}
    (hcmp : ∀ d, A d → ∃ i, ob (τ (N.face d)) ≤ i ∧ i < oe (τ (N.face d)) ∧ ol i = σ d)
    (hhd : ∀ d, A d → hd (σ d) = τ (N.face (N.rev d)))
    (h : ReflTransGen (fun a b => ∃ d, A d ∧ N.face d = a ∧ N.face (N.rev d) = b) r y) :
    ReflTransGen (BfsAdj ob oe ol hd) (τ r) (τ y) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih =>
    obtain ⟨d, hd', rfl, rfl⟩ := hbc
    obtain ⟨i, h1, h2, e⟩ := hcmp d hd'
    exact ih.tail ⟨i, h1, h2, by rw [e, hhd d hd']⟩

/-- **The tree of the recorded parents**: at the end of the search from `τ r` (`CtSt`) with
every node queued, on out-lists listing only darts `d` with `A d` of the face of the node and
heads the faces of the reverses, the recorded parent arcs `PA[τ y] = σ (C.par y)` are the parent
darts of a tree `C` rooted at `r`, all satisfying `A`. -/
theorem dtree_of_ct [Nonempty D] {nV nD qt : ℕ} {mem : ℕ → ℕ} (τ : Y ≃ Fin nV)
    (σ : D ≃ Fin nD) {A : D → Prop} (r : Y)
    (hsnd : ∀ y i, ob (τ y) ≤ i → i < oe (τ y) → ∃ d, A d ∧ N.face d = y ∧ ol i = σ d)
    (hhd : ∀ d, A d → hd (σ d) = τ (N.face (N.rev d)))
    (hS : CtSt nV (τ r) Mb Qb PAb qt ob oe ol hd mem)
    (hall : ∀ y, ∃ j < qt, mem (Qb + j) = τ y) :
    ∃ C : STFlow.DTree N, C.root = r ∧ (∀ y, y ≠ C.root → A (C.par y)) ∧
      ∀ y, y ≠ C.root → mem (PAb + τ y) = σ (C.par y) := by
  classical
  choose pos hpos using hall
  have hpos_eq : ∀ y j, j < qt → mem (Qb + j) = τ y → pos y = j := fun y j hj e =>
    hS.st.qinj _ (hpos y).1 _ hj ((hpos y).2.trans e.symm)
  have hq : ∀ y, y ≠ r → ∃ d, A d ∧ mem (PAb + τ y) = σ d ∧ N.face (N.rev d) = y ∧
      pos (N.face d) < pos y := by
    intro y hy
    have hp0 : 0 < pos y := by
      by_contra h0
      have e : pos y = 0 := by omega
      have e1 := (hpos y).2
      rw [e, Nat.add_zero, hS.st.q0] at e1
      exact hy (τ.injective (Fin.ext e1.symm))
    obtain ⟨p, hp, i, h1, h2, h3, h4⟩ := hS.par (pos y) hp0 (hpos y).1
    have hplt : mem (Qb + p) < nV := hS.st.qlt p (by have := (hpos y).1; omega)
    set z := τ.symm ⟨mem (Qb + p), hplt⟩ with hz
    have hτz : (τ z : ℕ) = mem (Qb + p) := by simp [hz]
    rw [← hτz] at h1 h2
    obtain ⟨d, hA, hfd, hol⟩ := hsnd z i h1 h2
    rw [(hpos y).2] at h3 h4
    refine ⟨d, hA, by rw [h3, hol], ?_, ?_⟩
    · have := hhd d hA
      rw [← hol, h4] at this
      exact τ.injective (Fin.ext this.symm)
    · rw [hfd, hpos_eq z p (by have := (hpos y).1; omega) hτz.symm]; exact hp
  choose! q hq using hq
  let par : Y → D := fun y => if y = r then Classical.arbitrary D else q y
  have hpar : ∀ y, y ≠ r → par y = q y := fun y hy => by simp only [par, hy, ↓reduceIte]
  have hhead : ∀ y, y ≠ r → N.face (N.rev (par y)) = y := fun y hy => by
    rw [hpar y hy]; exact (hq y hy).2.2.1
  have hreach : ∀ y, ∃ m, (STFlow.upF N r par)^[m] y = r := by
    intro y
    induction hn : pos y using Nat.strong_induction_on generalizing y with
    | _ m ih =>
      by_cases hy : y = r
      · exact ⟨0, hy⟩
      obtain ⟨m', hm'⟩ := ih _ (hn ▸ (hq y hy).2.2.2) (N.face (q y)) rfl
      refine ⟨m' + 1, ?_⟩
      rw [Function.iterate_succ_apply]
      have : STFlow.upF N r par y = N.face (q y) := by
        simp [STFlow.upF, hy, hpar y hy]
      rw [this]; exact hm'
  refine ⟨⟨r, par, hhead, hreach⟩, rfl, fun y hy => ?_, fun y hy => ?_⟩
  · have hy' : y ≠ r := hy
    show A (par y)
    rw [hpar y hy']; exact (hq y hy').1
  · have hy' : y ≠ r := hy
    show mem (PAb + τ y) = σ (par y)
    rw [hpar y hy']; exact (hq y hy').2.1

/-- **All nodes are queued** at the end of the search, when every face is reached from `r`
through darts satisfying `A` (listed in the out-lists, with their heads). -/
theorem ct_all {nV nD qt : ℕ} {mem : ℕ → ℕ} (τ : Y ≃ Fin nV) (σ : D ≃ Fin nD) {A : D → Prop}
    (r : Y)
    (hcmp : ∀ d, A d → ∃ i, ob (τ (N.face d)) ≤ i ∧ i < oe (τ (N.face d)) ∧ ol i = σ d)
    (hhd : ∀ d, A d → hd (σ d) = τ (N.face (N.rev d)))
    (hconn : ∀ y, ReflTransGen (fun a b => ∃ d, A d ∧ N.face d = a ∧ N.face (N.rev d) = b) r y)
    (hS : CtSt nV (τ r) Mb Qb PAb qt ob oe ol hd mem)
    (hcl : BfsClosed Qb qt qt (BfsAdj ob oe ol hd) mem) :
    ∀ y, ∃ j < qt, mem (Qb + j) = τ y := fun y =>
  (hS.st.reach_iff hcl _).2 (bfsAdj_of_conn τ σ hcmp hhd (hconn y))

end Tree

end NegSSSP

end PlanarFlow
