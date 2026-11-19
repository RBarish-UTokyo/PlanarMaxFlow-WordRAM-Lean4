module

public import PlanarFlow.NegSSSP.KEncProg

/-!
# The reach bits of the one-face encoding, on the machine

The encoding of a one-face instance needs reach bits: the targets reached from the first root
(`Klein.kRegsX`, `KTgt`) and the darts whose tail is reached from the target of the first move
(the weights `Klein.tripWt`, `kcProg_kslot`). Here a breadth-first search writes them, on index
functions: `nV` vertices, the out-arcs of the vertex `u` listed at positions
`ob u ≤ i < oe u` of the list `ol` of arcs, the head `hd a` of every arc.

* `bfsProg`: the marks cleared, the source queued, then the queue processed: for every arc out
  of the vertex at the head of the queue, its head is marked and queued if it was not marked.
* `bfsProg_exec`: **the marks are the reach bits**: the word at `Mb + v` is `1` exactly when `v`
  is reached from the source along `BfsAdj` (`Relation.ReflTransGen`), within
  `35 nV + 17 m + 12` steps (`m` the length of the list of arcs, the out-lists of the vertices
  having total length at most `m`).

Registers: natural `1400 … 1407` (inputs `nV`, `s`, `OBb`, `OEb`, `OLb`, `HDb`, `Mb`, `Qb`),
`1410 … 1419` (scratch). Natural memory is written only in the marks `[Mb, Mb + nV)` and the
queue `[Qb, Qb + nV)`; real registers and memory are not touched.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Relation WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge

variable {P : Input} {W : ℕ}

/-! ### The program -/

/-- The marks cleared (`r1411` from `0` to `nV`). -/
def bfsClear : Stmt :=
  .seq (block [.constN 1410 1, .constN 1419 0, .constN 1411 0])
    (.whileLtN 1411 1400 (block [.addN 1412 1406 1411, .storeN 1412 1419, .addN 1411 1411 1410]))

/-- The source marked and queued: `qh = r1413 = 0`, `qt = r1414 = 1`. -/
def bfsStart : Stmt :=
  block [.addN 1412 1406 1401, .storeN 1412 1410, .storeN 1407 1401, .constN 1413 0,
    .constN 1414 1]

/-- The arc at position `i = r1411` out of the current vertex: its head `v` (`r1417`) is marked
and queued if it was not marked. -/
def bfsArc : Stmt :=
  .seq (block [.addN 1412 1404 1411, .loadN 1417 1412, .addN 1412 1405 1417, .loadN 1417 1412,
    .addN 1412 1406 1417, .loadN 1418 1412]) <|
  .seq (.ifLtN 1419 1418 .skip
    (block [.storeN 1412 1410, .addN 1412 1407 1414, .storeN 1412 1417, .addN 1414 1414 1410]))
    (block [.addN 1411 1411 1410])

/-- The vertex at the head of the queue (`u = r1415`): dequeued, its out-arcs scanned. -/
def bfsVert : Stmt :=
  .seq (block [.addN 1412 1407 1413, .loadN 1415 1412, .addN 1413 1413 1410,
    .addN 1412 1402 1415, .loadN 1411 1412, .addN 1412 1403 1415, .loadN 1416 1412])
    (.whileLtN 1411 1416 bfsArc)

/-- **Breadth-first search.** -/
def bfsProg : Stmt := .seq bfsClear (.seq bfsStart (.whileLtN 1413 1414 bfsVert))

/-! ### The data -/

/-- The arcs out of `u` reach `v`. -/
def BfsAdj (ob oe ol hd : ℕ → ℕ) (u v : ℕ) : Prop := ∃ i, ob u ≤ i ∧ i < oe u ∧ hd (ol i) = v

/-- The layout of `bfsProg`: the inputs below `Ib ≤ Mb`, the marks then the queue. -/
structure BfsLay (nV m nA OBb OEb OLb HDb Mb Qb Ib W : ℕ) : Prop where
  ob : OBb + nV ≤ Ib
  oe : OEb + nV ≤ Ib
  ol : OLb + m ≤ Ib
  hd : HDb + nA ≤ Ib
  im : Ib ≤ Mb
  mq : Mb + nV ≤ Qb
  qw : Qb + nV + 1 ≤ W

/-- The inputs of `bfsProg` (index functions), kept in the memory below `Mb`. -/
structure BfsIn (nV m nA s OBb OEb OLb HDb : ℕ) (ob oe ol hd : ℕ → ℕ) (mem : ℕ → ℕ) : Prop where
  s_lt : s < nV
  hob : ∀ u < nV, mem (OBb + u) = ob u
  hoe : ∀ u < nV, mem (OEb + u) = oe u
  ble : ∀ u < nV, ob u ≤ oe u
  ole : ∀ u < nV, oe u ≤ m
  hol : ∀ i < m, mem (OLb + i) = ol i
  ol_lt : ∀ i < m, ol i < nA
  hhd : ∀ a < nA, mem (HDb + a) = hd a
  hd_lt : ∀ a < nA, hd a < nV
  deg : ∑ u ∈ range nV, (oe u - ob u) ≤ m

/-- The state of the search: the queue `[Qb, Qb + qt)` holds distinct vertices reached from the
source `s` (first), and the marks are its indicator. -/
structure BfsSt (nV s Mb Qb qt : ℕ) (Adj : ℕ → ℕ → Prop) (mem : ℕ → ℕ) : Prop where
  pos : 0 < qt
  le : qt ≤ nV
  q0 : mem Qb = s
  qlt : ∀ j < qt, mem (Qb + j) < nV
  qinj : ∀ j < qt, ∀ j' < qt, mem (Qb + j) = mem (Qb + j') → j = j'
  mark : ∀ v < nV, mem (Mb + v) = if ∃ j < qt, mem (Qb + j) = v then 1 else 0
  reach : ∀ j < qt, ReflTransGen Adj s (mem (Qb + j))

variable {nV m nA s OBb OEb OLb HDb Mb Qb Ib : ℕ} {ob oe ol hd : ℕ → ℕ}

/-- A vertex off a queue of distinct vertices leaves room in the queue. -/
theorem BfsSt.lt_of_not_mem {qt : ℕ} {Adj : ℕ → ℕ → Prop} {mem : ℕ → ℕ}
    (h : BfsSt nV s Mb Qb qt Adj mem) {v : ℕ} (hv : v < nV)
    (hn : ¬ ∃ j < qt, mem (Qb + j) = v) : qt < nV := by
  classical
  have hsub : insert v ((range qt).image fun j => mem (Qb + j)) ⊆ range nV := by
    intro x hx
    rcases mem_insert.1 hx with rfl | hx
    · exact mem_range.2 hv
    · obtain ⟨j, hj, rfl⟩ := mem_image.1 hx
      exact mem_range.2 (h.qlt j (mem_range.1 hj))
  have hnot : v ∉ (range qt).image fun j => mem (Qb + j) := fun hx => by
    obtain ⟨j, hj, e⟩ := mem_image.1 hx
    exact hn ⟨j, mem_range.1 hj, e⟩
  have hcard := card_le_card hsub
  rw [card_insert_of_notMem hnot, card_image_of_injOn (fun j hj j' hj' e =>
    h.qinj j (mem_range.1 hj) j' (mem_range.1 hj') e), card_range, card_range] at hcard
  omega

/-- **Queueing a vertex** `v` reached from the source and not yet marked: mark it and put it at
the end of the queue. -/
theorem BfsSt.push {qt : ℕ} {Adj : ℕ → ℕ → Prop} {mem : ℕ → ℕ}
    (h : BfsSt nV s Mb Qb qt Adj mem) (hmq : Mb + nV ≤ Qb) {v : ℕ} (hv : v < nV)
    (hn : ¬ ∃ j < qt, mem (Qb + j) = v) (hr : ReflTransGen Adj s v) :
    BfsSt nV s Mb Qb (qt + 1) Adj (upd (upd mem (Mb + v) 1) (Qb + qt) v) := by
  classical
  have hlt := h.lt_of_not_mem hv hn
  have hQ : ∀ j < qt, upd (upd mem (Mb + v) 1) (Qb + qt) v (Qb + j) = mem (Qb + j) :=
    fun j hj => by
      simp only [upd_apply, show Qb + j ≠ Qb + qt by omega, show Qb + j ≠ Mb + v by omega,
        ↓reduceIte]
  have hQt : upd (upd mem (Mb + v) 1) (Qb + qt) v (Qb + qt) = v := by simp
  refine ⟨by omega, by omega, ?_, fun j hj => ?_, fun j hj j' hj' e => ?_, fun w hw => ?_,
    fun j hj => ?_⟩
  · have e0 := hQ 0 h.pos
    rw [Nat.add_zero] at e0
    rw [e0]; exact h.q0
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [hQ j hj]; exact h.qlt j hj
    · rw [hQt]; exact hv
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl <;>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
    · rw [hQ j hj, hQ j' hj'] at e; exact h.qinj j hj j' hj' e
    · rw [hQ j hj, hQt] at e; exact absurd ⟨j, hj, e⟩ hn
    · rw [hQt, hQ j' hj'] at e; exact absurd ⟨j', hj', e.symm⟩ hn
    · rfl
  · have e1 : upd (upd mem (Mb + v) 1) (Qb + qt) v (Mb + w) = upd mem (Mb + v) 1 (Mb + w) := by
      simp only [upd_apply, show Mb + w ≠ Qb + qt by omega, ↓reduceIte]
    rw [e1]
    by_cases hwv : w = v
    · subst hwv
      have l : upd mem (Mb + w) 1 (Mb + w) = 1 := by simp
      have hx : ∃ j < qt + 1, upd (upd mem (Mb + w) 1) (Qb + qt) w (Qb + j) = w :=
        ⟨qt, by omega, hQt⟩
      rw [l]
      simp only [hx, ↓reduceIte]
    · have l : upd mem (Mb + v) 1 (Mb + w) = mem (Mb + w) := by
        simp only [upd_apply, show Mb + w ≠ Mb + v by omega, ↓reduceIte]
      have hiff : (∃ j < qt + 1, upd (upd mem (Mb + v) 1) (Qb + qt) v (Qb + j) = w) ↔
          ∃ j < qt, mem (Qb + j) = w := by
        constructor
        · rintro ⟨j, hj, e⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact ⟨j, hj, by rw [← hQ j hj]; exact e⟩
          · rw [hQt] at e; exact absurd e.symm hwv
        · rintro ⟨j, hj, e⟩; exact ⟨j, by omega, by rw [hQ j hj]; exact e⟩
      rw [l, h.mark w hw]
      simp only [hiff]
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [hQ j hj]; exact h.reach j hj
    · rw [hQt]; exact hr

/-! ### One arc -/

/-- The registers of the scan of an arc. -/
structure BfsRegs (OBb OEb OLb HDb Mb Qb : ℕ) (c : Config) : Prop where
  r02 : c.nreg 1402 = OBb
  r03 : c.nreg 1403 = OEb
  r04 : c.nreg 1404 = OLb
  r05 : c.nreg 1405 = HDb
  r06 : c.nreg 1406 = Mb
  r07 : c.nreg 1407 = Qb
  r10 : c.nreg 1410 = 1
  r19 : c.nreg 1419 = 0

theorem BfsRegs.frame {c c' : Config} (h : BfsRegs OBb OEb OLb HDb Mb Qb c)
    (hn : ∀ r, 1402 ≤ r → r ≤ 1407 ∨ r = 1410 ∨ r = 1419 → c'.nreg r = c.nreg r) :
    BfsRegs OBb OEb OLb HDb Mb Qb c' :=
  ⟨(hn _ (by omega) (by omega)).trans h.r02, (hn _ (by omega) (by omega)).trans h.r03,
    (hn _ (by omega) (by omega)).trans h.r04, (hn _ (by omega) (by omega)).trans h.r05,
    (hn _ (by omega) (by omega)).trans h.r06, (hn _ (by omega) (by omega)).trans h.r07,
    (hn _ (by omega) (by omega)).trans h.r10, (hn _ (by omega) (by omega)).trans h.r19⟩

set_option maxHeartbeats 1000000 in
/-- **The scan of the arc at position `i`** out of a vertex `u` reached from the source: its head
is marked and queued unless it was marked; the queue grows by at most one. -/
theorem bfsArc_exec (hL : BfsLay nV m nA OBb OEb OLb HDb Mb Qb Ib W) (c : Config)
    (hc : WordsBounded W c) (hR : BfsRegs OBb OEb OLb HDb Mb Qb c)
    (hI : BfsIn nV m nA s OBb OEb OLb HDb ob oe ol hd c.nmem) {qt : ℕ}
    (hS : BfsSt nV s Mb Qb qt (BfsAdj ob oe ol hd) c.nmem) {u i : ℕ} (hu : u < nV)
    (hru : ReflTransGen (BfsAdj ob oe ol hd) s u) (hi1 : ob u ≤ i) (hi2 : i < oe u)
    (r11 : c.nreg 1411 = i) (r14 : c.nreg 1414 = qt) :
    ∃ c' t, Exec P W bfsArc c c' t ∧ t ≤ 13 ∧
      ((∃ qt', (qt' = qt ∨ qt' = qt + 1) ∧ c'.nreg 1414 = qt' ∧
          BfsSt nV s Mb Qb qt' (BfsAdj ob oe ol hd) c'.nmem ∧
          (∃ j < qt', c'.nmem (Qb + j) = hd (ol i)) ∧
          ∀ j < qt, c'.nmem (Qb + j) = c.nmem (Qb + j)) ∧
        c'.nreg 1411 = i + 1 ∧
        (∀ r, r ≠ 1411 → r ≠ 1412 → r ≠ 1414 → r ≠ 1417 → r ≠ 1418 → c'.nreg r = c.nreg r) ∧
        (∀ a, a < Mb ∨ Qb + nV ≤ a → c'.nmem a = c.nmem a) ∧ c'.rreg = c.rreg ∧
        c'.rmem = c.rmem ∧ c'.output = c.output) := by
  classical
  have := hL.ob; have := hL.oe; have := hL.ol; have := hL.hd; have := hL.im; have := hL.mq
  have := hL.qw
  have hi_m : i < m := lt_of_lt_of_le hi2 (hI.ole u hu)
  have ha : ol i < nA := hI.ol_lt i hi_m
  have hv : hd (ol i) < nV := hI.hd_lt _ ha
  have hqt := hS.le
  have x1 : c.nmem (OLb + i) = ol i := hI.hol i hi_m
  have x2 : c.nmem (HDb + ol i) = hd (ol i) := hI.hhd _ ha
  have hr : ReflTransGen (BfsAdj ob oe ol hd) s (hd (ol i)) := hru.tail ⟨i, hi1, hi2, rfl⟩
  obtain ⟨r02, r03, r04, r05, r06, r07, r10, r19⟩ := hR
  unfold bfsArc
  refine spec_seq ?_
  exec_block
  all_goals try ((try config_simp); (try simp only [r04, r05, r06, r11, x1, x2]); omega)
  refine spec_seq ?_
  by_cases hm : 0 < c.nmem (Mb + hd (ol i))
  · have hin : ∃ j < qt, c.nmem (Qb + j) = hd (ol i) := by
      by_contra hn
      have := hS.mark _ hv
      simp only [hn, ↓reduceIte] at this
      omega
    refine spec_ifLtN_true (by config_simp; simp only [r19, r04, r05, r06, r11, x1, x2]; omega)
      (spec_skip ‹_› ?_)
    exec_block
    all_goals try ((try config_simp); (try simp only [r10, r11]); omega)
    refine ⟨by omega, ⟨qt, Or.inl rfl, by config_simp; exact r14, hS, hin, fun _ _ => rfl⟩,
      by config_simp; simp only [r10, r11], fun r h1 h2 h3 h4 h5 => ?_, fun _ _ => rfl, rfl, rfl,
      rfl⟩
    config_simp; simp only [upd_apply, h1, h2, h4, h5, ↓reduceIte]
  · have hn : ¬ ∃ j < qt, c.nmem (Qb + j) = hd (ol i) := by
      intro hin
      have := hS.mark _ hv
      simp only [hin, ↓reduceIte] at this
      omega
    have hlt := hS.lt_of_not_mem hv hn
    refine spec_ifLtN_false (by config_simp; simp only [r19, r04, r05, r06, r11, x1, x2]; omega) ?_
    exec_block
    all_goals try ((try config_simp); (try simp only [r07, r10, r14, r11]); omega)
    refine ⟨by omega, ⟨qt + 1, Or.inr rfl, by config_simp; simp only [r10, r14], ?_, ?_,
      fun j hj => ?_⟩, by config_simp; simp only [r10, r11], fun r h1 h2 h3 h4 h5 => ?_,
      fun a ha' => ?_, rfl, rfl, rfl⟩
    · config_simp; simp only [r04, r05, r06, r07, r10, r11, r14, x1, x2]
      exact hS.push hL.mq hv hn hr
    · refine ⟨qt, by omega, ?_⟩
      config_simp; simp only [r04, r05, r06, r07, r10, r11, r14, x1, x2]; simp
    · config_simp; simp only [r04, r05, r06, r07, r10, r11, r14, x1, x2]
      simp only [upd_apply, show Qb + j ≠ Qb + qt by omega,
        show Qb + j ≠ Mb + hd (ol i) by omega, ↓reduceIte]
    · config_simp; simp only [upd_apply, h1, h2, h3, h4, h5, ↓reduceIte]
    · config_simp; simp only [r04, r05, r06, r07, r10, r11, r14, x1, x2]
      simp only [upd_apply, show a ≠ Qb + qt by omega, show a ≠ Mb + hd (ol i) by omega,
        ↓reduceIte]

/-! ### One vertex -/

/-- The vertices at the positions `j < qh` of the queue have all their out-neighbours queued. -/
def BfsClosed (Qb qh qt : ℕ) (Adj : ℕ → ℕ → Prop) (mem : ℕ → ℕ) : Prop :=
  ∀ j < qh, ∀ v, Adj (mem (Qb + j)) v → ∃ j' < qt, mem (Qb + j') = v

theorem BfsIn.frame {mem mem' : ℕ → ℕ} (hL : BfsLay nV m nA OBb OEb OLb HDb Mb Qb Ib W)
    (h : BfsIn nV m nA s OBb OEb OLb HDb ob oe ol hd mem) (hm : ∀ a < Mb, mem' a = mem a) :
    BfsIn nV m nA s OBb OEb OLb HDb ob oe ol hd mem' := by
  have := hL.ob; have := hL.oe; have := hL.ol; have := hL.hd; have := hL.im
  exact ⟨h.s_lt, fun u hu => by rw [hm _ (by omega)]; exact h.hob u hu,
    fun u hu => by rw [hm _ (by omega)]; exact h.hoe u hu, h.ble, h.ole,
    fun i hi => by rw [hm _ (by omega)]; exact h.hol i hi, h.ol_lt,
    fun a ha => by rw [hm _ (by omega)]; exact h.hhd a ha, h.hd_lt, h.deg⟩

set_option maxHeartbeats 2000000 in
/-- **The vertex at the head of the queue**: dequeued, its out-arcs scanned (`bfsArc_exec`); then
its out-neighbours are queued, within `9 + 15 deg` steps. -/
theorem bfsVert_exec (hL : BfsLay nV m nA OBb OEb OLb HDb Mb Qb Ib W) (c : Config)
    (hc : WordsBounded W c) (hR : BfsRegs OBb OEb OLb HDb Mb Qb c)
    (hI : BfsIn nV m nA s OBb OEb OLb HDb ob oe ol hd c.nmem) {qh qt : ℕ}
    (hS : BfsSt nV s Mb Qb qt (BfsAdj ob oe ol hd) c.nmem)
    (hcl : BfsClosed Qb qh qt (BfsAdj ob oe ol hd) c.nmem) (hq : qh < qt)
    (r13 : c.nreg 1413 = qh) (r14 : c.nreg 1414 = qt) :
    ∃ c' t, Exec P W bfsVert c c' t ∧
      t ≤ 9 + 15 * (oe (c.nmem (Qb + qh)) - ob (c.nmem (Qb + qh))) ∧
      (BfsRegs OBb OEb OLb HDb Mb Qb c' ∧ (∀ a, a < Mb ∨ Qb + nV ≤ a → c'.nmem a = c.nmem a) ∧
        c'.nreg 1413 = qh + 1 ∧
        ∃ qt', qt ≤ qt' ∧ c'.nreg 1414 = qt' ∧
          BfsSt nV s Mb Qb qt' (BfsAdj ob oe ol hd) c'.nmem ∧
          (∀ j < qt, c'.nmem (Qb + j) = c.nmem (Qb + j)) ∧
          BfsClosed Qb (qh + 1) qt' (BfsAdj ob oe ol hd) c'.nmem) ∧
        (∀ r, r < 1410 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
        c'.output = c.output := by
  classical
  have := hL.ob; have := hL.oe; have := hL.ol; have := hL.hd; have := hL.im; have := hL.mq
  have := hL.qw
  have hqt := hS.le
  set u := c.nmem (Qb + qh) with hu_def
  have hu : u < nV := hS.qlt qh hq
  have hru : ReflTransGen (BfsAdj ob oe ol hd) s u := hS.reach qh hq
  have xo : c.nmem (OBb + u) = ob u := hI.hob u hu
  have xe : c.nmem (OEb + u) = oe u := hI.hoe u hu
  have hbe := hI.ble u hu
  have hem := hI.ole u hu
  obtain ⟨r02, r03, r04, r05, r06, r07, r10, r19⟩ := hR
  unfold bfsVert
  refine spec_seq ?_
  exec_block
  all_goals try ((try config_simp); (try simp only [r02, r03, r07, r10, r13, ← hu_def]); omega)
  -- the scan of the out-arcs
  let I : Config → Prop := fun d =>
    WordsBounded W d ∧ BfsRegs OBb OEb OLb HDb Mb Qb d ∧
      (∀ a, a < Mb ∨ Qb + nV ≤ a → d.nmem a = c.nmem a) ∧
      d.nreg 1413 = qh + 1 ∧ d.nreg 1416 = oe u ∧ ob u ≤ d.nreg 1411 ∧ d.nreg 1411 ≤ oe u ∧
      (∃ qt', qt ≤ qt' ∧ d.nreg 1414 = qt' ∧ BfsSt nV s Mb Qb qt' (BfsAdj ob oe ol hd) d.nmem ∧
        (∀ j < qt, d.nmem (Qb + j) = c.nmem (Qb + j)) ∧
        BfsClosed Qb qh qt' (BfsAdj ob oe ol hd) d.nmem ∧
        ∀ i, ob u ≤ i → i < d.nreg 1411 → ∃ j < qt', d.nmem (Qb + j) = hd (ol i)) ∧
      (∀ r, r < 1410 → d.nreg r = c.nreg r) ∧ d.rreg = c.rreg ∧ d.rmem = c.rmem ∧
      d.output = c.output
  refine spec_while I (fun d => 15 * (oe u - d.nreg 1411)) (fun d h => h.1) ?_ ?_ ?_
  · intro d ⟨hw, hRd, hmd, d13, d16, d11a, d11b, ⟨qt', hqt', d14, hSd, hpre, hcld, hsc⟩, dn, drr,
      drm, dout⟩ hlt
    rw [d16] at hlt
    have hId := hI.frame hL fun a ha => hmd a (Or.inl ha)
    obtain ⟨d', k, ex, hk, ⟨qt'', hq'', e14, hS'', hin, hpre'⟩, e11, en, em, err, erm, eo⟩ :=
      bfsArc_exec (P := P) hL d hw hRd hId hSd hu hru d11a hlt rfl d14
    refine ⟨d', k, ex, ⟨ex.wb_right, hRd.frame fun r h1 h2 => en r (by omega) (by omega)
      (by omega) (by omega) (by omega), fun a ha => by rw [em a ha, hmd a ha],
      by rw [en _ (by omega) (by omega) (by omega) (by omega) (by omega), d13],
      by rw [en _ (by omega) (by omega) (by omega) (by omega) (by omega), d16],
      by omega, by omega, ⟨qt'', by omega, e14, hS'', fun j hj => by
        rw [hpre' j (by omega), hpre j hj], fun j hj v hv => ?_, fun i h1 h2 => ?_⟩,
      fun r hr => by rw [en r (by omega) (by omega) (by omega) (by omega) (by omega), dn r hr],
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
      by config_simp; exact r10, by config_simp; exact r19⟩, fun _ _ => rfl,
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
    have hk' : k ≤ 15 * (oe u - ob u) + 2 := by
      config_simp at hk; simp only [r02, r07, r13, ← hu_def, xo] at hk; exact hk
    refine ⟨by omega, ⟨hRd, hmd, d13, qt', hqt', d14, hSd, hpre, fun j hj v hv => ?_⟩, dn, drr,
      drm, dout⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact hcld j hj v hv
    · rw [hpre j hq, ← hu_def] at hv
      obtain ⟨i, h1, h2, rfl⟩ := hv
      exact hsc i h1 (by omega)

/-! ### The whole search -/

/-- The degrees of distinct queued vertices sum to at most the total. -/
theorem BfsSt.sum_le {qt : ℕ} {Adj : ℕ → ℕ → Prop} {mem : ℕ → ℕ}
    (h : BfsSt nV s Mb Qb qt Adj mem) {t : ℕ} (ht : t ≤ qt) (f : ℕ → ℕ) :
    ∑ j ∈ range t, f (mem (Qb + j)) ≤ ∑ u ∈ range nV, f u := by
  classical
  rw [← sum_image (f := f) (g := fun j => mem (Qb + j)) (fun j hj j' hj' e =>
    h.qinj j (by have := mem_range.1 hj; omega) j' (by have := mem_range.1 hj'; omega) e)]
  refine sum_le_sum_of_subset fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := mem_image.1 hx
  exact mem_range.2 (h.qlt j (by have := mem_range.1 hj; omega))

/-- At the end of the search the marked vertices are the reached ones. -/
theorem BfsSt.reach_iff {qt : ℕ} {Adj : ℕ → ℕ → Prop} {mem : ℕ → ℕ}
    (h : BfsSt nV s Mb Qb qt Adj mem) (hc : BfsClosed Qb qt qt Adj mem) (v : ℕ) :
    (∃ j < qt, mem (Qb + j) = v) ↔ ReflTransGen Adj s v := by
  constructor
  · rintro ⟨j, hj, rfl⟩; exact h.reach j hj
  · intro hr
    induction hr with
    | refl => exact ⟨0, h.pos, h.q0⟩
    | tail _ hbc ih =>
      obtain ⟨j, hj, rfl⟩ := ih
      exact hc j hj _ hbc

set_option maxHeartbeats 2000000 in
open Classical in
/-- **The marks are the reach bits.** With `r1400 … r1407` = `nV, s, OBb, OEb, OLb, HDb, Mb, Qb`
and the inputs below `Mb` (`BfsIn`), `bfsProg` ends within `35 nV + 17 m + 12` steps with the
word at `Mb + v` equal to `1` if `v` is reached from `s` along `BfsAdj ob oe ol hd` and `0`
otherwise, for every `v < nV`; the natural memory below `Mb` and from `Qb + nV` on, the
natural registers below `1410`, the real registers and memory and the output are kept. -/
theorem bfsProg_exec (hL : BfsLay nV m nA OBb OEb OLb HDb Mb Qb Ib W) (c : Config)
    (hc : WordsBounded W c) (h00 : c.nreg 1400 = nV) (h01 : c.nreg 1401 = s)
    (h02 : c.nreg 1402 = OBb) (h03 : c.nreg 1403 = OEb) (h04 : c.nreg 1404 = OLb)
    (h05 : c.nreg 1405 = HDb) (h06 : c.nreg 1406 = Mb) (h07 : c.nreg 1407 = Qb)
    (hI : BfsIn nV m nA s OBb OEb OLb HDb ob oe ol hd c.nmem) :
    ∃ c' t, Exec P W bfsProg c c' t ∧ t ≤ 35 * nV + 17 * m + 12 ∧
      ((∀ v < nV, c'.nmem (Mb + v) = if ReflTransGen (BfsAdj ob oe ol hd) s v then 1 else 0) ∧
        (∀ a, a < Mb ∨ Qb + nV ≤ a → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 1410 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
        c'.output = c.output) := by
  classical
  have := hL.ob; have := hL.oe; have := hL.ol; have := hL.hd; have := hL.im; have := hL.mq
  have := hL.qw
  have hs := hI.s_lt
  unfold bfsProg bfsClear
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
      (∀ a, a < Mb ∨ Qb + nV ≤ a → d.nmem a = c.nmem a) ∧
      d.nreg 1413 ≤ d.nreg 1414 ∧
      BfsSt nV s Mb Qb (d.nreg 1414) (BfsAdj ob oe ol hd) d.nmem ∧
      BfsClosed Qb (d.nreg 1413) (d.nreg 1414) (BfsAdj ob oe ol hd) d.nmem ∧
      (∀ r, r < 1410 → d.nreg r = c.nreg r) ∧ d.rreg = c.rreg ∧ d.rmem = c.rmem ∧
      d.output = c.output
  refine spec_while I (fun d => 30 * (nV - d.nreg 1413) + 17 * (m - D d)) (fun d h => h.1) ?_
    ?_ ?_
  · intro d ⟨hw, hRd, hmd, hle, hSd, hcld, dn, drr, drm, dout⟩ hlt
    have hId := hI.frame hL fun a ha => hmd a (Or.inl ha)
    obtain ⟨d', k, ex, hk, ⟨hR', hm', e13, qt', hqt', e14, hS', hpre, hcl'⟩, en, err, erm, eo⟩ :=
      bfsVert_exec (P := P) hL d hw hRd hId hSd hcld hlt rfl rfl
    have hqn := hSd.le
    have hsum := hSd.sum_le (t := d.nreg 1413 + 1) (by omega) (fun u => oe u - ob u)
    rw [sum_range_succ] at hsum
    have hD' : D d' = D d + (oe (d.nmem (Qb + d.nreg 1413)) - ob (d.nmem (Qb + d.nreg 1413))) := by
      simp only [D, e13, sum_range_succ]
      congr 1
      · exact sum_congr rfl fun j hj => by rw [hpre j (by have := mem_range.1 hj; omega)]
      · rw [hpre _ hlt]
    have hdeg := hI.deg
    refine ⟨d', k, ex, ⟨ex.wb_right, hR', fun a ha => by rw [hm' a ha, hmd a ha], by omega,
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
    · intro a ha
      config_simp
      simp only [q01, q06, q07, g10, upd_apply, show a ≠ Qb by omega, show a ≠ Mb + s by omega,
        ↓reduceIte]
      exact gm a (by omega)
    · config_simp; omega
    · config_simp
      simp only [q01, q06, q07, g10]
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
    refine ⟨?_, fun v hv => ?_, hmd, dn, drr, drm, dout⟩
    · simp only [D] at hk
      config_simp at hk
      simp only [range_zero, sum_empty] at hk
      omega
    · rw [hSd.mark v hv]
      simp only [hSd.reach_iff hcld v]

/-! ### The reach bits of a piece -/

section Piece

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-- **The search follows the piece**: with the vertices numbered by an injective `ν`, the out-list
of `ν x` listing exactly the numbers `σ d` of the darts `d ∈ S` leaving `x`, and the head of the
arc `σ d` the number of the head of `d`, the vertex `ν y` is reached from `ν x` along `BfsAdj`
exactly when `y` is reached from `x` in the piece graph. -/
theorem bfsAdj_reach_iff {M : CombMap D V F} {S : Finset D} {ℓ : D → ℤ} {nD : ℕ}
    (σ : D ≃ Fin nD) {ν : V → ℕ} (hν : Function.Injective ν) {ob oe ol hd : ℕ → ℕ}
    (hsnd : ∀ x i, ob (ν x) ≤ i → i < oe (ν x) → ∃ d ∈ S, M.tail d = x ∧ ol i = σ d)
    (hcmp : ∀ d ∈ S, ∃ i, ob (ν (M.tail d)) ≤ i ∧ i < oe (ν (M.tail d)) ∧ ol i = σ d)
    (hhd : ∀ d, hd (σ d) = ν (M.head d)) (x y : V) :
    ReflTransGen (BfsAdj ob oe ol hd) (ν x) (ν y) ↔ MSSP.Reach (MSSP.pieceGraph M S ℓ) x y := by
  constructor
  · intro h
    suffices H : ∀ w, ReflTransGen (BfsAdj ob oe ol hd) (ν x) w →
        ∃ z, ν z = w ∧ MSSP.Reach (MSSP.pieceGraph M S ℓ) x z by
      obtain ⟨z, hz, hr⟩ := H _ h
      rw [← hν hz]; exact hr
    intro w hw
    induction hw with
    | refl => exact ⟨x, rfl, MSSP.Reach.refl x⟩
    | tail _ hbc ih =>
      obtain ⟨z, rfl, hr⟩ := ih
      obtain ⟨i, h1, h2, rfl⟩ := hbc
      obtain ⟨d, hd, htl, hol⟩ := hsnd z i h1 h2
      refine ⟨M.head d, by rw [hol, hhd], ?_⟩
      have := MSSP.Reach.arc (G := MSSP.pieceGraph M S ℓ) (a := ⟨d, hd⟩)
        (by show MSSP.Reach _ x (M.tail d); rw [htl]; exact hr)
      exact this
  · rintro ⟨l, hl⟩
    induction hl with
    | nil => exact ReflTransGen.refl
    | @cons a _ _ _ ih =>
      refine ReflTransGen.head ?_ ih
      obtain ⟨i, h1, h2, hol⟩ := hcmp a.1 a.2
      exact ⟨i, h1, h2, by rw [hol, hhd]; rfl⟩

open Classical in
/-- **The reach bits of a piece on the machine**: `bfsProg` from the number `ν x` of a vertex,
on the out-lists of the piece (`bfsAdj_reach_iff`), writes at `Mb + ν y` the bit
`[y reached from x in the piece graph]`. -/
theorem bfsProg_reach {M : CombMap D V F} {S : Finset D} {ℓ : D → ℤ} {nD : ℕ}
    (σ : D ≃ Fin nD) {ν : V → ℕ} (hν : Function.Injective ν) {ob oe ol hd : ℕ → ℕ}
    (hsnd : ∀ x i, ob (ν x) ≤ i → i < oe (ν x) → ∃ d ∈ S, M.tail d = x ∧ ol i = σ d)
    (hcmp : ∀ d ∈ S, ∃ i, ob (ν (M.tail d)) ≤ i ∧ i < oe (ν (M.tail d)) ∧ ol i = σ d)
    (hhd : ∀ d, hd (σ d) = ν (M.head d)) {x : V} {nV m nA OBb OEb OLb HDb Mb Qb Ib : ℕ}
    (hL : BfsLay nV m nA OBb OEb OLb HDb Mb Qb Ib W) (c : Config)
    (hc : WordsBounded W c) (h00 : c.nreg 1400 = nV) (h01 : c.nreg 1401 = ν x)
    (h02 : c.nreg 1402 = OBb) (h03 : c.nreg 1403 = OEb) (h04 : c.nreg 1404 = OLb)
    (h05 : c.nreg 1405 = HDb) (h06 : c.nreg 1406 = Mb) (h07 : c.nreg 1407 = Qb)
    (hI : BfsIn nV m nA (ν x) OBb OEb OLb HDb ob oe ol hd c.nmem) :
    ∃ c' t, Exec P W bfsProg c c' t ∧ t ≤ 35 * nV + 17 * m + 12 ∧
      (∀ y, ν y < nV → c'.nmem (Mb + ν y) =
        if MSSP.Reach (MSSP.pieceGraph M S ℓ) x y then 1 else 0) ∧
      (∀ a, a < Mb ∨ Qb + nV ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1410 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  obtain ⟨c', t, ex, ht, hm, hfr, hn, hr, hrm, ho⟩ :=
    bfsProg_exec (P := P) hL c hc h00 h01 h02 h03 h04 h05 h06 h07 hI
  refine ⟨c', t, ex, ht, fun y hy => ?_, hfr, hn, hr, hrm, ho⟩
  rw [hm _ hy]
  simp only [bfsAdj_reach_iff (ℓ := ℓ) σ hν hsnd hcmp hhd x y]

end Piece

end NegSSSP

end PlanarFlow
