module

public import PlanarFlow.NegSSSP.KEncOrdRun

/-!
# A search recording its parents: the cotree of the one-face encoding, on the machine

The encoding of a one-face instance (`Klein.KVal`) needs an initial cotree `C` of the spanning
tree `T`: a tree of the faces rooted at the face of `g 0` whose parent darts are off `T`
(`∀ x ≠ C.root, ¬ T.InT (C.par x)`). Here the breadth-first search of
`PlanarFlow/NegSSSP/KEncReach.lean` is extended to record, for every vertex it queues, the arc
along which it was reached (`ctProg`, natural words only):

* `ctArc`, `ctVert`, `ctProg`: the program (`bfsProg` with the parent arc of a newly queued
  vertex stored at `PAb + v`).
* `CtSt`: the state of the search (`BfsSt`) and the parents: every queued vertex but the source
  was reached along an arc `PA[v] = ol i` out of an earlier queued vertex.
* `CtSt.push`, `ctArc_exec`: **the scan of one arc keeps `CtSt`** (within 15 steps).

Not yet done here: the loops (`ctVert_exec`, `ctProg_exec`, as `bfsVert_exec`, `bfsProg_exec`
with `CtSt` in place of `BfsSt`) and the tree built from the recorded parents on the dual
out-lists (`exists_dtree_of_conn`, `cotree_conn`: every face is reached, and the parent of a
queued face is at an earlier position, so the parents reach the root).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Relation WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge

variable {P : Input} {W : ℕ}

/-! ### The program -/

/-- The arc at position `i = r1411` out of the current vertex: its head `v` (`r1418`) is
marked, queued and given the parent arc `a` (`r1417`, at `PAb + v`) if it was not marked. -/
def ctArc : Stmt :=
  .seq (block [.addN 1412 1404 1411, .loadN 1417 1412, .addN 1412 1405 1417, .loadN 1418 1412,
    .addN 1412 1406 1418, .loadN 1420 1412]) <|
  .seq (.ifLtN 1419 1420 .skip
    (block [.storeN 1412 1410, .addN 1412 1407 1414, .storeN 1412 1418, .addN 1412 1408 1418,
      .storeN 1412 1417, .addN 1414 1414 1410]))
    (block [.addN 1411 1411 1410])

/-- The vertex at the head of the queue: dequeued, its out-arcs scanned. -/
def ctVert : Stmt :=
  .seq (block [.addN 1412 1407 1413, .loadN 1415 1412, .addN 1413 1413 1410,
    .addN 1412 1402 1415, .loadN 1411 1412, .addN 1412 1403 1415, .loadN 1416 1412])
    (.whileLtN 1411 1416 ctArc)

/-- **Breadth-first search recording the parents** (the marks cleared and the source queued as
in `bfsProg`). -/
def ctProg : Stmt := .seq bfsClear (.seq bfsStart (.whileLtN 1413 1414 ctVert))

/-! ### The state -/

variable {nV m nA s OBb OEb OLb HDb Mb Qb Ib PAb : ℕ} {ob oe ol hd : ℕ → ℕ}

/-- **The state of the search with its parents**: `BfsSt`, and every queued vertex `Q j`,
`j > 0`, has a recorded arc `PA[Q j] = ol i` out of an earlier queued vertex `Q p`, `p < j`,
with head `Q j`. -/
structure CtSt (nV s Mb Qb PAb qt : ℕ) (ob oe ol hd : ℕ → ℕ) (mem : ℕ → ℕ) : Prop where
  st : BfsSt nV s Mb Qb qt (BfsAdj ob oe ol hd) mem
  par : ∀ j, 0 < j → j < qt → ∃ p < j, ∃ i, ob (mem (Qb + p)) ≤ i ∧ i < oe (mem (Qb + p)) ∧
    mem (PAb + mem (Qb + j)) = ol i ∧ hd (ol i) = mem (Qb + j)

/-- `BfsSt` depends only on the marks and the queue. -/
theorem BfsSt.congr {qt : ℕ} {Adj : ℕ → ℕ → Prop} {mem mem' : ℕ → ℕ}
    (h : BfsSt nV s Mb Qb qt Adj mem) (hm : ∀ v < nV, mem' (Mb + v) = mem (Mb + v))
    (hq : ∀ j < qt, mem' (Qb + j) = mem (Qb + j)) : BfsSt nV s Mb Qb qt Adj mem' := by
  refine ⟨h.pos, h.le, ?_, fun j hj => ?_, fun j hj j' hj' e => ?_, fun v hv => ?_,
    fun j hj => ?_⟩
  · have := hq 0 h.pos; rw [Nat.add_zero] at this; rw [this]; exact h.q0
  · rw [hq j hj]; exact h.qlt j hj
  · rw [hq j hj, hq j' hj'] at e; exact h.qinj j hj j' hj' e
  · have hiff : (∃ j < qt, mem' (Qb + j) = v) ↔ ∃ j < qt, mem (Qb + j) = v :=
      ⟨fun ⟨j, hj, e⟩ => ⟨j, hj, by rw [← hq j hj]; exact e⟩,
        fun ⟨j, hj, e⟩ => ⟨j, hj, by rw [hq j hj]; exact e⟩⟩
    rw [hm v hv, h.mark v hv]
    simp only [hiff]
  · rw [hq j hj]; exact h.reach j hj

/-- **Queueing a vertex with its parent arc**: the head `v = hd (ol i)` of the arc at position
`i` out of the queued vertex `Q qh`, not yet marked, is marked, queued, and given the parent
arc `ol i`. -/
theorem CtSt.push {qt qh i : ℕ} {mem : ℕ → ℕ} (h : CtSt nV s Mb Qb PAb qt ob oe ol hd mem)
    (hmq : Mb + nV ≤ Qb) (hqp : Qb + nV ≤ PAb) (hqh : qh < qt)
    (hi1 : ob (mem (Qb + qh)) ≤ i) (hi2 : i < oe (mem (Qb + qh))) (hv : hd (ol i) < nV)
    (hn : ¬ ∃ j < qt, mem (Qb + j) = hd (ol i))
    (hr : ReflTransGen (BfsAdj ob oe ol hd) s (hd (ol i))) :
    CtSt nV s Mb Qb PAb (qt + 1) ob oe ol hd
      (upd (upd (upd mem (Mb + hd (ol i)) 1) (Qb + qt) (hd (ol i))) (PAb + hd (ol i)) (ol i)) := by
  classical
  have hlt := h.st.lt_of_not_mem hv hn
  have hS := h.st.push hmq hv hn hr
  set v := hd (ol i) with hvd
  set mem₁ := upd (upd mem (Mb + v) 1) (Qb + qt) v with hm₁
  have hQ1 : ∀ j < qt + 1, upd mem₁ (PAb + v) (ol i) (Qb + j) = mem₁ (Qb + j) := fun j hj => by
    simp only [upd_apply, show Qb + j ≠ PAb + v by omega, ↓reduceIte]
  have hQ : ∀ j < qt, mem₁ (Qb + j) = mem (Qb + j) := fun j hj => by
    simp only [hm₁, upd_apply, show Qb + j ≠ Qb + qt by omega, show Qb + j ≠ Mb + v by omega,
      ↓reduceIte]
  refine ⟨hS.congr (fun w hw => by simp only [upd_apply, show Mb + w ≠ PAb + v by omega,
    ↓reduceIte]) hQ1, fun j hj hj' => ?_⟩
  rw [hQ1 j hj']
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | hjq
  · obtain ⟨p, hp, i', h1, h2, h3, h4⟩ := h.par j hj hj'
    have hne : mem (Qb + j) ≠ v := fun e => hn ⟨j, hj', e⟩
    refine ⟨p, hp, i', ?_, ?_, ?_, ?_⟩
    · rw [hQ1 p (by omega), hQ p (by omega)]; exact h1
    · rw [hQ1 p (by omega), hQ p (by omega)]; exact h2
    · rw [hQ j hj']
      have hql := h.st.qlt j hj'
      simp only [hm₁, upd_apply, show PAb + mem (Qb + j) ≠ PAb + v by omega,
        show PAb + mem (Qb + j) ≠ Qb + qt by omega,
        show PAb + mem (Qb + j) ≠ Mb + v by omega, ↓reduceIte]
      exact h3
    · rw [hQ j hj']; exact h4
  · rw [hjq]
    have hQt : mem₁ (Qb + qt) = v := by simp [hm₁]
    refine ⟨qh, hqh, i, ?_, ?_, ?_, ?_⟩
    · rw [hQ1 qh (by omega), hQ qh hqh]; exact hi1
    · rw [hQ1 qh (by omega), hQ qh hqh]; exact hi2
    · rw [hQt]; simp
    · rw [hQt]

/-! ### One arc -/

set_option maxHeartbeats 1000000 in
/-- **The scan of the arc at position `i`** out of the queued vertex `u = Q qh`: its head is
marked, queued and given its parent arc unless it was marked. -/
theorem ctArc_exec (hL : BfsLay nV m nA OBb OEb OLb HDb Mb Qb Ib W) (hqp : Qb + nV ≤ PAb)
    (hpw : PAb + nV ≤ W) (c : Config)
    (hc : WordsBounded W c) (hR : BfsRegs OBb OEb OLb HDb Mb Qb c) (r08 : c.nreg 1408 = PAb)
    (hI : BfsIn nV m nA s OBb OEb OLb HDb ob oe ol hd c.nmem) {qt qh : ℕ}
    (hS : CtSt nV s Mb Qb PAb qt ob oe ol hd c.nmem) (hqh : qh < qt) {i : ℕ}
    (hi1 : ob (c.nmem (Qb + qh)) ≤ i) (hi2 : i < oe (c.nmem (Qb + qh)))
    (r11 : c.nreg 1411 = i) (r14 : c.nreg 1414 = qt) :
    ∃ c' t, Exec P W ctArc c c' t ∧ t ≤ 15 ∧
      ((∃ qt', (qt' = qt ∨ qt' = qt + 1) ∧ c'.nreg 1414 = qt' ∧
          CtSt nV s Mb Qb PAb qt' ob oe ol hd c'.nmem ∧
          (∃ j < qt', c'.nmem (Qb + j) = hd (ol i)) ∧
          ∀ j < qt, c'.nmem (Qb + j) = c.nmem (Qb + j)) ∧
        c'.nreg 1411 = i + 1 ∧
        (∀ r, r ≠ 1411 → r ≠ 1412 → r ≠ 1414 → r ≠ 1417 → r ≠ 1418 → r ≠ 1420 →
          c'.nreg r = c.nreg r) ∧
        (∀ a, a < Mb ∨ Qb + nV ≤ a → a < PAb ∨ PAb + nV ≤ a → c'.nmem a = c.nmem a) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  classical
  have := hL.ob; have := hL.oe; have := hL.ol; have := hL.hd; have := hL.im; have := hL.mq
  have := hL.qw
  have hu : c.nmem (Qb + qh) < nV := hS.st.qlt qh hqh
  have hru := hS.st.reach qh hqh
  have hi_m : i < m := lt_of_lt_of_le hi2 (hI.ole _ hu)
  have ha : ol i < nA := hI.ol_lt i hi_m
  have hv : hd (ol i) < nV := hI.hd_lt _ ha
  have hqt := hS.st.le
  have x1 : c.nmem (OLb + i) = ol i := hI.hol i hi_m
  have x2 : c.nmem (HDb + ol i) = hd (ol i) := hI.hhd _ ha
  have hr : ReflTransGen (BfsAdj ob oe ol hd) s (hd (ol i)) := hru.tail ⟨i, hi1, hi2, rfl⟩
  obtain ⟨r02, r03, r04, r05, r06, r07, r10, r19⟩ := hR
  unfold ctArc
  refine spec_seq ?_
  exec_block
  all_goals try ((try config_simp); (try simp only [r04, r05, r06, r11, x1, x2]); omega)
  refine spec_seq ?_
  by_cases hm : 0 < c.nmem (Mb + hd (ol i))
  · have hin : ∃ j < qt, c.nmem (Qb + j) = hd (ol i) := by
      by_contra hn
      have := hS.st.mark _ hv
      simp only [hn, ↓reduceIte] at this
      omega
    refine spec_ifLtN_true (by config_simp; simp only [r19, r04, r05, r06, r11, x1, x2]; omega)
      (spec_skip ‹_› ?_)
    exec_block
    all_goals try ((try config_simp); (try simp only [r10, r11]); omega)
    refine ⟨by omega, ⟨qt, Or.inl rfl, by config_simp; exact r14, hS, hin, fun _ _ => rfl⟩,
      by config_simp; simp only [r10, r11], fun r h1 h2 h3 h4 h5 h6 => ?_, fun _ _ _ => rfl, rfl,
      rfl, rfl⟩
    config_simp; simp only [upd_apply, h1, h2, h4, h5, h6, ↓reduceIte]
  · have hn : ¬ ∃ j < qt, c.nmem (Qb + j) = hd (ol i) := by
      intro hin
      have := hS.st.mark _ hv
      simp only [hin, ↓reduceIte] at this
      omega
    have hlt := hS.st.lt_of_not_mem hv hn
    refine spec_ifLtN_false (by config_simp; simp only [r19, r04, r05, r06, r11, x1, x2]; omega) ?_
    exec_block
    all_goals try ((try config_simp); (try simp only [r04, r05, r07, r08, r10, r14, r11, x1, x2]); omega)
    refine ⟨by omega, ⟨qt + 1, Or.inr rfl, by config_simp; simp only [r10, r14], ?_, ?_,
      fun j hj => ?_⟩, by config_simp; simp only [r10, r11], fun r h1 h2 h3 h4 h5 h6 => ?_,
      fun a ha' ha'' => ?_, rfl, rfl, rfl⟩
    · config_simp; simp only [r04, r05, r06, r07, r08, r10, r11, r14, x1, x2]
      exact hS.push hL.mq hqp hqh hi1 hi2 hv hn hr
    · refine ⟨qt, by omega, ?_⟩
      config_simp; simp only [r04, r05, r06, r07, r08, r10, r11, r14, x1, x2]
      simp only [upd_apply, show Qb + qt ≠ PAb + hd (ol i) by omega, ↓reduceIte]
    · config_simp; simp only [r04, r05, r06, r07, r08, r10, r11, r14, x1, x2]
      simp only [upd_apply, show Qb + j ≠ Qb + qt by omega,
        show Qb + j ≠ Mb + hd (ol i) by omega, show Qb + j ≠ PAb + hd (ol i) by omega,
        ↓reduceIte]
    · config_simp; simp only [upd_apply, h1, h2, h3, h4, h5, h6, ↓reduceIte]
    · config_simp; simp only [r04, r05, r06, r07, r08, r10, r11, r14, x1, x2]
      simp only [upd_apply, show a ≠ Qb + qt by omega, show a ≠ Mb + hd (ol i) by omega,
        show a ≠ PAb + hd (ol i) by omega, ↓reduceIte]

end NegSSSP

end PlanarFlow
