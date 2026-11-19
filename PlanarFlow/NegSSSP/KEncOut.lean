module

public import PlanarFlow.NegSSSP.KEncReach
public import PlanarFlow.NegSSSP.ArcSort

/-!
# The out-lists of the one-face encoding, on the machine

The encoding of a one-face instance (`Klein.KVal`) holds, besides the arrays by darts, the
out-darts of the piece vertex by vertex (`Klein.KOut`): for the node `ιv x` of every vertex,
the words of `OL` from `OB[ιv x]` to `OE[ιv x]` are the numbers `σ d` of the darts `d ∈ S`
leaving `x`, each once. Here a **stable counting sort on natural words only** (no real register
or real memory is touched) writes them from the arrays `NT` (the nodes of the tails) and `IS`
(the membership flags) of the same encoding:

* `osProg`: the counting sort of the indices `i < M` with `K i ≠ 0` by the key `T i < N`
  (`csProg` of `PlanarFlow/NegSSSP/ArcSort.lean` without its real lengths, the item placed
  being the index `i` itself), then the offsets copied into the two arrays `OB`, `OE`.
* `osProg_exec`: within `osCost M N = 29 M + 32 N + 26` steps, `OB[u] = (pre L u).length`,
  `OE[u] = (pre L (u + 1)).length` (`u < N`) and the `e`-th word of `OL` the index of the `e`-th
  arc of `arcList N L`, `L = csList T id K 0 M`; the natural memory changes only in the scratch
  `[Ob, Ob + 2 N + 1)` and in `[OBb, Db + M)`.
* `osProg_out`: **the out-lists of a piece**: with `T (σ d) = ιv (M.tail d)` (`ιv` injective,
  below `N`) and `K (σ d) = [d ∈ S]`, the property `KOut` in memory form (`OutMem`).
* `kout_of_outMem`: `OutMem` at the offsets `β + iOB`, `β + iOE`, `β + iOL` of the encoding
  gives `Klein.KOut` for any input words agreeing with the memory there.
* `osProg_kout`: **the out-lists of the encoding**: `osProg` reading `NT`, `IS` at `β + iNT`,
  `β + iIS` and writing at `β + iOB`, `β + iOE`, `β + iOL`, so that every input agreeing with
  the memory from `β` up to the end of `OL` meets `Klein.KOut`.

Registers: natural `1500 … 1509` (inputs `M`, `N`, `Tb`, —, `Kb`, `Ob`, `Cb`, `OBb`, `OEb`,
`Db`), `1510 … 1519` (scratch).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge.FR

/-! ### The program -/

/-- Clear the counts `Ob[x] := 0`, `x ≤ N`. -/
def osClear : Stmt :=
  .seq (block [.constN 1510 1, .constN 1511 0, .addN 1512 1501 1510, .constN 1513 0])
    (.whileLtN 1511 1512 (block [.addN 1514 1505 1511, .storeN 1514 1513, .addN 1511 1511 1510]))

/-- Count the kept indices per key at `Ob + T i + 1`. -/
def osCountBody : Stmt :=
  .seq (block [.addN 1514 1504 1511, .loadN 1515 1514]) <|
  .seq (.ifLtN 1515 1510 .skip (block [.addN 1514 1502 1511, .loadN 1516 1514,
    .addN 1514 1505 1516, .addN 1514 1514 1510, .loadN 1517 1514, .addN 1517 1517 1510,
    .storeN 1514 1517]))
    (block [.addN 1511 1511 1510])

/-- The prefix sums `Ob[x + 1] += Ob[x]`. -/
def osPrefBody : Stmt := block [.addN 1514 1505 1511, .loadN 1515 1514, .addN 1514 1514 1510,
  .loadN 1516 1514, .addN 1516 1516 1515, .storeN 1514 1516, .addN 1511 1511 1510]

/-- The cursors `Cb[x] := Ob[x]`. -/
def osCopyBody : Stmt := block [.addN 1514 1505 1511, .loadN 1515 1514, .addN 1514 1506 1511,
  .storeN 1514 1515, .addN 1511 1511 1510]

/-- Place the kept index `i` at the cursor of its key. -/
def osPlaceBody : Stmt :=
  .seq (block [.addN 1514 1504 1511, .loadN 1515 1514]) <|
  .seq (.ifLtN 1515 1510 .skip (block [.addN 1514 1502 1511, .loadN 1516 1514,
    .addN 1514 1506 1516, .loadN 1517 1514, .addN 1519 1509 1517, .storeN 1519 1511,
    .addN 1517 1517 1510, .storeN 1514 1517]))
    (block [.addN 1511 1511 1510])

/-- The offsets copied: `OB[u] := Ob[u]`, `OE[u] := Ob[u + 1]`. -/
def osOutBody : Stmt := block [.addN 1514 1505 1511, .loadN 1515 1514, .addN 1516 1507 1511,
  .storeN 1516 1515, .addN 1514 1514 1510, .loadN 1515 1514, .addN 1516 1508 1511,
  .storeN 1516 1515, .addN 1511 1511 1510]

/-- **The counting sort of the out-darts.** -/
def osProg : Stmt :=
  .seq osClear <|
  .seq (.instr (.constN 1511 0)) <| .seq (.whileLtN 1511 1500 osCountBody) <|
  .seq (.instr (.constN 1511 0)) <| .seq (.whileLtN 1511 1501 osPrefBody) <|
  .seq (.instr (.constN 1511 0)) <| .seq (.whileLtN 1511 1501 osCopyBody) <|
  .seq (.instr (.constN 1511 0)) <| .seq (.whileLtN 1511 1500 osPlaceBody) <|
  .seq (.instr (.constN 1511 0)) (.whileLtN 1511 1501 osOutBody)

/-- The data of `osProg`: `M` indices (keys at `Tb`, keep flags at `Kb`), `N` keys; the counts
at `Ob`, the cursors at `Cb`, the sorted indices at `Db`, the offsets at `OBb`, `OEb`. -/
structure OsIn (M N Tb Kb Ob Cb OBb OEb Db : ℕ) (T K : ℕ → ℕ) (c : Config) : Prop where
  r00 : c.nreg 1500 = M
  r01 : c.nreg 1501 = N
  r02 : c.nreg 1502 = Tb
  r04 : c.nreg 1504 = Kb
  r05 : c.nreg 1505 = Ob
  r06 : c.nreg 1506 = Cb
  r07 : c.nreg 1507 = OBb
  r08 : c.nreg 1508 = OEb
  r09 : c.nreg 1509 = Db
  tl : ∀ i < M, c.nmem (Tb + i) = T i
  kp : ∀ i < M, c.nmem (Kb + i) = K i

/-- The layout of `osProg`: the kept keys below `N`; the scratch `[Ob, Ob + 2 N + 1)` (counts,
then cursors) apart from the inputs and the outputs; the outputs `OB`, `OE`, `OL` in a row,
apart from the inputs; the addresses below the word bound. -/
structure OsLay (M N Tb Kb Ob Cb OBb OEb Db W : ℕ) (T K : ℕ → ℕ) : Prop where
  tlt : ∀ i < M, K i ≠ 0 → T i < N
  cb : Cb = Ob + N + 1
  sT : Ob + 2 * N + 1 ≤ Tb ∨ Tb + M ≤ Ob
  sK : Ob + 2 * N + 1 ≤ Kb ∨ Kb + M ≤ Ob
  sO : Ob + 2 * N + 1 ≤ OBb ∨ Db + M ≤ Ob
  bE : OBb + N ≤ OEb
  eD : OEb + N ≤ Db
  dT : Db + M ≤ Tb ∨ Tb + M ≤ OBb
  dK : Db + M ≤ Kb ∨ Kb + M ≤ OBb
  wT : Tb + M ≤ W
  wK : Kb + M ≤ W
  wD : Db + M ≤ W
  wS : Ob + 2 * N + 1 ≤ W
  wM : M + 1 ≤ W
  wN : N + 1 ≤ W

/-! ### The phases -/

variable {P : Input} {W : ℕ} {M N Tb Kb Ob Cb OBb OEb Db : ℕ} {T K : ℕ → ℕ}

lemma OsIn.mono {c : Config} (hI : OsIn M N Tb Kb Ob Cb OBb OEb Db T K c) {c' : Config}
    (hn : ∀ r, r < 1510 → c'.nreg r = c.nreg r)
    (ht : ∀ i < M, c'.nmem (Tb + i) = c.nmem (Tb + i))
    (hk : ∀ i < M, c'.nmem (Kb + i) = c.nmem (Kb + i)) :
    OsIn M N Tb Kb Ob Cb OBb OEb Db T K c' :=
  ⟨(hn 1500 (by omega)).trans hI.r00, (hn 1501 (by omega)).trans hI.r01,
    (hn 1502 (by omega)).trans hI.r02, (hn 1504 (by omega)).trans hI.r04,
    (hn 1505 (by omega)).trans hI.r05, (hn 1506 (by omega)).trans hI.r06,
    (hn 1507 (by omega)).trans hI.r07, (hn 1508 (by omega)).trans hI.r08,
    (hn 1509 (by omega)).trans hI.r09, fun i hi => (ht i hi).trans (hI.tl i hi),
    fun i hi => (hk i hi).trans (hI.kp i hi)⟩

theorem osClear_exec (hL : OsLay M N Tb Kb Ob Cb OBb OEb Db W T K) (c : Config)
    (hc : WordsBounded W c) (hI : OsIn M N Tb Kb Ob Cb OBb OEb Db T K c) :
    ∃ c' k, Exec P W osClear c c' k ∧ k ≤ 5 * N + 11 ∧
      ((∀ x ≤ N, c'.nmem (Ob + x) = 0) ∧
        (∀ a, (a < Ob ∨ Ob + N + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 1510 ∨ 1520 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 1510 = 1 ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wS; have := hL.wN
  unfold osClear
  refine spec_seq ?_
  exec_block
  all_goals try ((try config_simp); (try simp only [hI.r01]); omega)
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x < i, c'.nmem (Ob + x) = 0) ∧ (∀ a, (a < Ob ∨ Ob + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1510 ∨ 1520 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 1510 = 1 ∧
      c'.nreg 1513 = 0 ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 1511) (bR := 1512)
    (body := block [.addN 1514 1505 1511, .storeN 1514 1513, .addN 1511 1511 1510]) J (K := 3)
    (n := N + 1) _ ‹_› (by config_simp) (by config_simp; rw [hI.r01]) ?_
    (fun i c₁ hi hw ha hb ⟨g0, gm, gn, g410, g413, gr, grm, go⟩ => by
      have e405 : c₁.nreg 1505 = Ob := (gn 1505 (by omega)).trans hI.r05
      exec_block
      all_goals try ((try config_simp); (try simp only [e405, ha, g410]); omega)
      dsimp only [J]
      config_simp
      simp only [e405, ha, g410, g413]
      and_intros
      all_goals first
        | trivial
        | omega
        | assumption
        | (intro x hx; simp only [upd_apply]; split_ifs
           · rfl
           · exact g0 x (by omega))
        | (intro a ha'; simp only [upd_apply]
           rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact gm a (by omega))
        | (intro r hr; simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr))) ?_
  · refine ⟨fun x hx => absurd hx (by omega), fun a _ => ?_, fun r hr => ?_, ?_, ?_, rfl, rfl, rfl⟩
    all_goals config_simp
    · simp only [upd_apply]; split_ifs <;> omega
  intro c₂ k₂ hk₂ _ hJ₂
  obtain ⟨_, g0, gm, gn, g410, -, gr, grm, go⟩ := hJ₂
  exact ⟨by omega, fun x hx => g0 x (by omega), gm, gn, g410, gr, grm, go⟩

theorem osCount_exec (hL : OsLay M N Tb Kb Ob Cb OBb OEb Db W T K) (c : Config)
    (hc : WordsBounded W c) (hI : OsIn M N Tb Kb Ob Cb OBb OEb Db T K c)
    (h410 : c.nreg 1510 = 1) (h411 : c.nreg 1511 = 0) (h0 : ∀ x ≤ N, c.nmem (Ob + x) = 0) :
    ∃ c' k, Exec P W (.whileLtN 1511 1500 osCountBody) c c' k ∧ k ≤ 14 * M + 2 ∧
      ((∀ x < N, c'.nmem (Ob + (x + 1)) = (blk (csList T id K (fun _ => 0) M) x).length) ∧
        c'.nmem Ob = 0 ∧ (∀ a, (a < Ob ∨ Ob + N + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 1510 ∨ 1520 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 1510 = 1 ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wS; have := hL.wN; have := hL.wM; have := hL.wK; have := hL.wT
  have := hL.sK; have := hL.sT
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x < N, c'.nmem (Ob + (x + 1)) = (blk (csList T id K (fun _ => 0) i) x).length) ∧
      c'.nmem Ob = 0 ∧ (∀ a, (a < Ob ∨ Ob + N + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1510 ∨ 1520 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 1510 = 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 1511) (bR := 1500) (body := osCountBody) J
    (K := 12) (n := M) c hc h411 hI.r00 ⟨fun x hx => by rw [h0 _ (by omega)]; rfl,
      by simpa using h0 0 (by omega), fun _ _ => rfl, fun _ _ => rfl, h410, rfl, rfl, rfl⟩
    (fun i c₁ hi hw ha hb ⟨gc, g0, gm, gn, g410, gr, grm, go⟩ => by
      have e404 : c₁.nreg 1504 = Kb := (gn 1504 (by omega)).trans hI.r04
      have e402 : c₁.nreg 1502 = Tb := (gn 1502 (by omega)).trans hI.r02
      have e405 : c₁.nreg 1505 = Ob := (gn 1505 (by omega)).trans hI.r05
      have eK : c₁.nmem (Kb + i) = K i := by rw [gm _ (by omega)]; exact hI.kp i hi
      have eT : c₁.nmem (Tb + i) = T i := by rw [gm _ (by omega)]; exact hI.tl i hi
      unfold osCountBody
      refine spec_seq ?_
      exec_block
      all_goals try ((try config_simp); (try simp only [e404, ha]); omega)
      refine spec_seq ?_
      by_cases hk : K i = 0
      · refine spec_ifLtN_true (by config_simp; simp only [e404, ha, eK, hk, g410]; omega) ?_
        refine spec_skip ‹_› ?_
        exec_block
        all_goals try ((try config_simp); (try simp only [ha, g410]); omega)
        dsimp only [J]
        config_simp
        simp only [ha, g410]
        refine ⟨by omega, trivial, hb, fun x hx => ?_, g0, gm, fun r hr => ?_, trivial, gr, grm,
          go⟩
        · rw [gc x hx, length_blk_succ]; simp [hk]
        · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr
      · have htN := hL.tlt i hi hk
        have hcnt := gc (T i) htN
        have hle := length_blk_le (T := T) (H := id) (K := K) (Lz := fun _ => 0) i (T i)
        refine spec_ifLtN_false (by config_simp; simp only [e404, ha, eK, g410]; omega) ?_
        have hcnt' : c₁.nmem (Ob + T i + 1) = (blk (csList T id K (fun _ => 0) i) (T i)).length := by
          rw [Nat.add_assoc]; exact hcnt
        exec_block
        all_goals try ((try config_simp); (try simp only [e404, e402, ha, eK, eT, g410]); omega)
        all_goals try ((try config_simp); (try simp only [e405, e402, ha, eT, hcnt', g410]); omega)
        dsimp only [J]
        config_simp
        simp only [e404, e402, e405, ha, eK, eT, g410]
        refine ⟨by omega, trivial, hb, fun x hx => ?_, ?_, fun a ha' => ?_, fun r hr => ?_, trivial,
          gr, grm, go⟩
        · simp only [upd_apply]
          rw [length_blk_succ]
          by_cases hx' : x = T i
          · subst hx'
            rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), hcnt']
            simp [hk]
          · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), gc x hx]
            simp [Ne.symm hx']
        · simp only [upd_apply]; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), g0]
        · simp only [upd_apply]; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), gm a ha']
        · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr)) ?_
  intro c₂ k₂ hk₂ _ hJ₂
  obtain ⟨_, gc, g0, gm, gn, g410, gr, grm, go⟩ := hJ₂
  exact ⟨by omega, gc, g0, gm, gn, g410, gr, grm, go⟩

theorem osPref_exec (hL : OsLay M N Tb Kb Ob Cb OBb OEb Db W T K) (c : Config)
    (hc : WordsBounded W c) (hI : OsIn M N Tb Kb Ob Cb OBb OEb Db T K c)
    (h410 : c.nreg 1510 = 1) (h411 : c.nreg 1511 = 0) (hc0 : c.nmem Ob = 0)
    (hcnt : ∀ x < N, c.nmem (Ob + (x + 1)) = (blk (csList T id K (fun _ => 0) M) x).length) :
    ∃ c' k, Exec P W (.whileLtN 1511 1501 osPrefBody) c c' k ∧ k ≤ 9 * N + 2 ∧
      ((∀ x ≤ N, c'.nmem (Ob + x) = (pre (csList T id K (fun _ => 0) M) x).length) ∧
        (∀ a, (a < Ob ∨ Ob + N + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 1510 ∨ 1520 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 1510 = 1 ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wS; have := hL.wN; have := hL.wM
  set L := csList T id K (fun _ => 0) M with hLd
  let J : ℕ → Config → Prop := fun j c' =>
    (∀ x ≤ j, c'.nmem (Ob + x) = (pre L x).length) ∧
      (∀ x, j < x → x < N + 1 → c'.nmem (Ob + x) = (blk L (x - 1)).length) ∧
      (∀ a, (a < Ob ∨ Ob + N + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1510 ∨ 1520 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 1510 = 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 1511) (bR := 1501) (body := osPrefBody) J
    (K := 7) (n := N) c hc h411 hI.r01 ⟨fun x hx => by
      rw [show x = 0 by omega, Nat.add_zero, hc0]; simp [pre],
      fun x hx hx' => by
        have := hcnt (x - 1) (by omega); rwa [show x - 1 + 1 = x by omega] at this,
      fun _ _ => rfl, fun _ _ => rfl, h410, rfl, rfl, rfl⟩
    (fun j c₁ hj hw ha hb ⟨gp, gb, gm, gn, g410, gr, grm, go⟩ => by
      have e405 : c₁.nreg 1505 = Ob := (gn 1505 (by omega)).trans hI.r05
      have hpj := gp j le_rfl
      have hbj : c₁.nmem (Ob + j + 1) = (blk L j).length := by
        rw [Nat.add_assoc, gb (j + 1) (by omega) (by omega), Nat.add_sub_cancel]
      have hps := length_pre_succ L j
      have hpM := length_pre_csList_le L hLd (j + 1)
      unfold osPrefBody
      exec_block
      all_goals try ((try config_simp); (try simp only [e405, ha, g410, hpj, hbj]); omega)
      dsimp only [J]
      config_simp
      simp only [e405, ha, g410, hpj, hbj]
      refine ⟨by omega, trivial, hb, fun x hx => ?_, fun x hx hx' => ?_, fun a ha' => ?_,
        fun r hr => ?_, trivial, gr, grm, go⟩
      · simp only [upd_apply]
        by_cases hxj : x = j + 1
        · subst hxj; rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]; omega
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), gp x (by omega)]
      · simp only [upd_apply]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), gb x (by omega) hx']
      · simp only [upd_apply]; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), gm a ha']
      · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr)) ?_
  intro c₂ k₂ hk₂ _ hJ₂
  obtain ⟨_, gp, -, gm, gn, g410, gr, grm, go⟩ := hJ₂
  exact ⟨by omega, gp, gm, gn, g410, gr, grm, go⟩

theorem osCopy_exec (hL : OsLay M N Tb Kb Ob Cb OBb OEb Db W T K) (c : Config)
    (hc : WordsBounded W c) (hI : OsIn M N Tb Kb Ob Cb OBb OEb Db T K c)
    (h410 : c.nreg 1510 = 1) (h411 : c.nreg 1511 = 0) :
    ∃ c' k, Exec P W (.whileLtN 1511 1501 osCopyBody) c c' k ∧ k ≤ 7 * N + 2 ∧
      ((∀ x < N, c'.nmem (Cb + x) = c.nmem (Ob + x)) ∧
        (∀ a, (a < Cb ∨ Cb + N ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 1510 ∨ 1520 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 1510 = 1 ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wS; have := hL.wN; have := hL.cb
  let J : ℕ → Config → Prop := fun j c' =>
    (∀ x < j, c'.nmem (Cb + x) = c.nmem (Ob + x)) ∧
      (∀ a, (a < Cb ∨ Cb + N ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1510 ∨ 1520 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 1510 = 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 1511) (bR := 1501) (body := osCopyBody) J
    (K := 5) (n := N) c hc h411 hI.r01 ⟨fun x hx => absurd hx (by omega), fun _ _ => rfl,
      fun _ _ => rfl, h410, rfl, rfl, rfl⟩
    (fun j c₁ hj hw ha hb ⟨gp, gm, gn, g410, gr, grm, go⟩ => by
      have e405 : c₁.nreg 1505 = Ob := (gn 1505 (by omega)).trans hI.r05
      have e406 : c₁.nreg 1506 = Cb := (gn 1506 (by omega)).trans hI.r06
      have hoj : c₁.nmem (Ob + j) = c.nmem (Ob + j) := gm _ (by omega)
      unfold osCopyBody
      exec_block
      all_goals try ((try config_simp); (try simp only [e405, e406, ha, g410]); omega)
      dsimp only [J]
      config_simp
      simp only [e405, e406, ha, g410, hoj]
      refine ⟨by omega, trivial, hb, fun x hx => ?_, fun a ha' => ?_, fun r hr => ?_, trivial, gr,
        grm, go⟩
      · simp only [upd_apply]
        by_cases hxj : x = j
        · subst hxj; rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), gp x (by omega)]
      · simp only [upd_apply]; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), gm a ha']
      · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr)) ?_
  intro c₂ k₂ hk₂ _ hJ₂
  obtain ⟨_, gp, gm, gn, g410, gr, grm, go⟩ := hJ₂
  exact ⟨by omega, gp, gm, gn, g410, gr, grm, go⟩

theorem osPlace_exec (hL : OsLay M N Tb Kb Ob Cb OBb OEb Db W T K) (c : Config)
    (hc : WordsBounded W c) (hI : OsIn M N Tb Kb Ob Cb OBb OEb Db T K c)
    (h410 : c.nreg 1510 = 1) (h411 : c.nreg 1511 = 0)
    (hcur : ∀ x < N, c.nmem (Cb + x) = (pre (csList T id K (fun _ => 0) M) x).length) :
    ∃ c' k, Exec P W (.whileLtN 1511 1500 osPlaceBody) c c' k ∧ k ≤ 15 * M + 2 ∧
      ((∀ x < N, ∀ j < (blk (csList T id K (fun _ => 0) M) x).length,
          c'.nmem (Db + ((pre (csList T id K (fun _ => 0) M) x).length + j)) =
            ((blk (csList T id K (fun _ => 0) M) x).getD j (0, 0, 0)).2.1) ∧
        (∀ a, (a < Cb ∨ Cb + N ≤ a) → (a < Db ∨ Db + M ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 1510 ∨ 1520 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 1510 = 1 ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wN; have := hL.wM; have := hL.wS; have := hL.wD; have := hL.wT; have := hL.wK
  have := hL.cb; have := hL.sT; have := hL.sK; have := hL.sO; have := hL.dT; have := hL.dK
  have := hL.bE; have := hL.eD
  set L := csList T id K (fun _ => 0) M with hLd
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x < N, c'.nmem (Cb + x) = (pre L x).length +
      (blk (csList T id K (fun _ => 0) i) x).length) ∧
      (∀ x < N, ∀ j < (blk (csList T id K (fun _ => 0) i) x).length,
        c'.nmem (Db + ((pre L x).length + j)) =
          ((blk (csList T id K (fun _ => 0) i) x).getD j (0, 0, 0)).2.1) ∧
      (∀ a, (a < Cb ∨ Cb + N ≤ a) → (a < Db ∨ Db + M ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1510 ∨ 1520 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 1510 = 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 1511) (bR := 1500) (body := osPlaceBody) J
    (K := 13) (n := M) c hc h411 hI.r00 ⟨fun x hx => by rw [hcur x hx]; simp [csList, blk],
      fun x _ j hj => by simp [csList, blk] at hj, fun _ _ _ => rfl, fun _ _ => rfl, h410, rfl,
      rfl, rfl⟩
    (fun i c₁ hi hw ha hb ⟨gA, gB, gm, gn, g410, gr, grm, go⟩ => by
      have e402 : c₁.nreg 1502 = Tb := (gn 1502 (by omega)).trans hI.r02
      have e404 : c₁.nreg 1504 = Kb := (gn 1504 (by omega)).trans hI.r04
      have e406 : c₁.nreg 1506 = Cb := (gn 1506 (by omega)).trans hI.r06
      have e409 : c₁.nreg 1509 = Db := (gn 1509 (by omega)).trans hI.r09
      have eK : c₁.nmem (Kb + i) = K i := by rw [gm _ (by omega) (by omega)]; exact hI.kp i hi
      have eT : c₁.nmem (Tb + i) = T i := by rw [gm _ (by omega) (by omega)]; exact hI.tl i hi
      unfold osPlaceBody
      refine spec_seq ?_
      exec_block
      all_goals try ((try config_simp); (try simp only [e404, ha]); omega)
      refine spec_seq ?_
      by_cases hk : K i = 0
      · refine spec_ifLtN_true (by config_simp; simp only [e404, ha, eK, hk, g410]; omega) ?_
        refine spec_skip ‹_› ?_
        exec_block
        all_goals try ((try config_simp); (try simp only [ha, g410]); omega)
        dsimp only [J]
        config_simp
        simp only [ha, g410]
        have hbl : ∀ x, blk (csList T id K (fun _ => 0) (i + 1)) x =
            blk (csList T id K (fun _ => 0) i) x := fun x => by
          rw [blk_csList_succ]; simp [hk]
        refine ⟨by omega, trivial, hb, fun x hx => ?_, fun x hx j hj => ?_, gm,
          fun r hr => ?_, trivial, gr, grm, go⟩
        · rw [hbl]; exact gA x hx
        · rw [hbl] at hj ⊢; exact gB x hx j hj
        · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr
      · -- the index `i` is kept, with key `t < N`
        have htN := hL.tlt i hi hk
        set t := T i with htd
        have hpos := gA t htN
        have hsucc := length_blk_succ (T := T) (H := id) (K := K) (Lz := fun _ => 0) i t
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hk, rfl⟩)] at hsucc
        have hpre1 := length_blk_csList_le (T := T) (H := id) (K := K) (Lz := fun _ => 0)
          (M := M) (show i + 1 ≤ M by omega) t
        rw [← hLd] at hpre1
        have hps := length_pre_succ L t
        have hmono := length_pre_mono L (show t + 1 ≤ N by omega)
        have hNM := length_pre_csList_le L hLd N
        refine spec_ifLtN_false (by config_simp; simp only [e404, ha, eK, g410]; omega) ?_
        exec_block
        all_goals try ((try config_simp); (try simp only [e402, e404, e406, e409, ha, eT, g410, hpos]); omega)
        dsimp only [J]
        config_simp
        simp only [e402, e404, e406, e409, ha, eT, g410, hpos]
        refine ⟨by omega, trivial, hb, fun x hx => ?_, fun x hx j hj => ?_, fun a h1 h2 => ?_,
          fun r hr => ?_, trivial, gr, grm, go⟩
        · simp only [upd_apply]
          by_cases hxt : x = t
          · subst hxt; rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]; omega
          · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
              ite_eq_right_of_eq_false _ _ (eq_false (by omega)), gA x hx, length_blk_succ]
            rw [← htd]; simp [Ne.symm hxt]
        · rw [blk_csList_succ, ← htd] at hj ⊢
          simp only [upd_apply]
          by_cases hxt : x = t
          · subst hxt
            simp only [ne_eq, hk, not_false_eq_true, true_and, ↓reduceIte, List.length_append,
              List.length_singleton] at hj ⊢
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
            · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
                ite_eq_right_of_eq_false _ _ (eq_false (by omega)), List.getD_append _ _ _ _ hj',
                gB _ hx j hj']
            · subst hj'
              rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
                ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
                List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
              rfl
          · have hne : ¬ (K i ≠ 0 ∧ t = x) := fun h => hxt h.2.symm
            simp only [hne, ↓reduceIte, List.append_nil] at hj ⊢
            have hx1 := length_blk_csList_le (T := T) (H := id) (K := K) (Lz := fun _ => 0)
              (M := M) (show i ≤ M by omega) x
            rw [← hLd] at hx1
            have hpx := length_pre_succ L x
            have hfar : (pre L x).length + j < (pre L t).length +
                (blk (csList T id K (fun _ => 0) i) t).length ∨
                (pre L t).length + (blk (csList T id K (fun _ => 0) i) t).length <
                  (pre L x).length + j := by
              rcases Nat.lt_or_gt_of_ne hxt with h | h
              · have := length_pre_mono L (show x + 1 ≤ t by omega); omega
              · have := length_pre_mono L (show t + 1 ≤ x by omega); omega
            have := length_pre_mono L (show x + 1 ≤ N by omega)
            rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
              ite_eq_right_of_eq_false _ _ (eq_false (by omega)), gB x hx j hj]
        · simp only [upd_apply]
          rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
            ite_eq_right_of_eq_false _ _ (eq_false (by omega)), gm a h1 h2]
        · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr)) ?_
  intro c₂ k₂ hk₂ _ hJ₂
  obtain ⟨_, -, gB, gm, gn, g410, gr, grm, go⟩ := hJ₂
  exact ⟨by omega, gB, gm, gn, g410, gr, grm, go⟩

theorem osOut_exec (hL : OsLay M N Tb Kb Ob Cb OBb OEb Db W T K) (c : Config)
    (hc : WordsBounded W c) (hI : OsIn M N Tb Kb Ob Cb OBb OEb Db T K c)
    (h410 : c.nreg 1510 = 1) (h411 : c.nreg 1511 = 0) :
    ∃ c' k, Exec P W (.whileLtN 1511 1501 osOutBody) c c' k ∧ k ≤ 11 * N + 2 ∧
      ((∀ x < N, c'.nmem (OBb + x) = c.nmem (Ob + x) ∧
          c'.nmem (OEb + x) = c.nmem (Ob + (x + 1))) ∧
        (∀ a, (a < OBb ∨ OEb + N ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 1510 ∨ 1520 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 1510 = 1 ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wS; have := hL.wN; have := hL.sO; have := hL.bE; have := hL.eD; have := hL.wD
  let J : ℕ → Config → Prop := fun j c' =>
    (∀ x < j, c'.nmem (OBb + x) = c.nmem (Ob + x) ∧
        c'.nmem (OEb + x) = c.nmem (Ob + (x + 1))) ∧
      (∀ a, (a < OBb ∨ OBb + j ≤ a) → (a < OEb ∨ OEb + j ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1510 ∨ 1520 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 1510 = 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 1511) (bR := 1501) (body := osOutBody) J
    (K := 9) (n := N) c hc h411 hI.r01 ⟨fun x hx => absurd hx (by omega), fun _ _ _ => rfl,
      fun _ _ => rfl, h410, rfl, rfl, rfl⟩
    (fun j c₁ hj hw ha hb ⟨gp, gm, gn, g410, gr, grm, go⟩ => by
      have e405 : c₁.nreg 1505 = Ob := (gn 1505 (by omega)).trans hI.r05
      have e407 : c₁.nreg 1507 = OBb := (gn 1507 (by omega)).trans hI.r07
      have e408 : c₁.nreg 1508 = OEb := (gn 1508 (by omega)).trans hI.r08
      have ho0 : c₁.nmem (Ob + j) = c.nmem (Ob + j) := gm _ (by omega) (by omega)
      have ho1 : c₁.nmem (Ob + j + 1) = c.nmem (Ob + (j + 1)) := by
        rw [Nat.add_assoc]; exact gm _ (by omega) (by omega)
      unfold osOutBody
      exec_block
      all_goals try ((try config_simp); (try simp only [e405, e407, e408, ha, g410]); omega)
      dsimp only [J]
      config_simp
      simp only [e405, e407, e408, ha, g410]
      refine ⟨by omega, trivial, hb, fun x hx => ?_, fun a h1 h2 => ?_, fun r hr => ?_, trivial,
        gr, grm, go⟩
      · simp only [upd_apply]
        constructor <;> split_ifs <;> first
          | omega
          | (obtain rfl : x = j := by omega
             first | exact ho0 | exact ho1)
          | exact (gp x (by omega)).1
          | exact (gp x (by omega)).2
      · simp only [upd_apply]
        split_ifs <;> first | omega | exact gm a (by omega) (by omega)
      · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr)) ?_
  intro c₂ k₂ hk₂ _ hJ₂
  obtain ⟨_, gp, gm, gn, g410, gr, grm, go⟩ := hJ₂
  exact ⟨by omega, gp, fun a ha => gm a (by omega) (by omega), gn, g410, gr, grm, go⟩

/-! ### The counting sort -/

/-- The cost bound of `osProg`. -/
def osCost (M N : ℕ) : ℕ := 29 * M + 32 * N + 26

/-- **The counting sort of the out-darts on the machine** (natural words only). From `OsIn`
(with `OsLay`), `osProg` writes the offsets `OB[x] = (pre L x).length` and
`OE[x] = (pre L (x + 1)).length` (`x < N`), and the index of the `e`-th arc of `arcList N L` at
`Db + e`, `L = csList T id K 0 M` the kept indices in order, within `osCost M N` steps; the
natural memory changes only in the scratch `[Ob, Ob + 2 N + 1)` and in `[OBb, Db + M)`; the real
registers and memory are not touched. -/
theorem osProg_exec (hL : OsLay M N Tb Kb Ob Cb OBb OEb Db W T K) (c : Config)
    (hc : WordsBounded W c) (hI : OsIn M N Tb Kb Ob Cb OBb OEb Db T K c) :
    ∃ c' k, Exec P W osProg c c' k ∧ k ≤ osCost M N ∧
      (∀ x < N, c'.nmem (OBb + x) = (pre (csList T id K (fun _ => 0) M) x).length ∧
        c'.nmem (OEb + x) = (pre (csList T id K (fun _ => 0) M) (x + 1)).length) ∧
      (∀ e < (pre (csList T id K (fun _ => 0) M) N).length,
        c'.nmem (Db + e) = ((pre (csList T id K (fun _ => 0) M) N).getD e (0, 0, 0)).2.1) ∧
      (∀ a, (a < Ob ∨ Ob + 2 * N + 1 ≤ a) → (a < OBb ∨ Db + M ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1510 ∨ 1520 < r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hL.cb; have := hL.wS; have := hL.wN; have := hL.wM; have := hL.wD
  have := hL.sT; have := hL.sK; have := hL.sO; have := hL.dT; have := hL.dK; have := hL.bE
  have := hL.eD
  unfold osProg
  -- clear
  refine spec_seq ?_
  refine spec_use (osClear_exec (P := P) hL c hc hI) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨z₁, m₁, n₁, r410₁, rr₁, rm₁, o₁⟩
  have hI₁ := hI.mono (fun r hr => n₁ r (by omega)) (fun i hi => m₁ _ (by omega))
    (fun i hi => m₁ _ (by omega))
  -- count
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₁ 1511 0 (by omega)) fun hw₂ => ?_
  refine spec_seq ?_
  refine spec_use (osCount_exec (P := P) hL _ hw₂
    (hI₁.mono (fun r hr => upd_other _ _ _ (by omega)) (fun _ _ => rfl) (fun _ _ => rfl))
    (by config_simp; exact r410₁) (by config_simp) (by config_simp; exact z₁)) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨cnt₃, z₃, m₃, n₃, r410₃, rr₃, rm₃, o₃⟩
  config_simp at m₃
  config_simp at n₃
  config_simp at rr₃
  config_simp at rm₃
  config_simp at o₃
  have hI₃ := hI₁.mono (fun r hr => by rw [n₃ r (by omega)]; exact upd_other _ _ _ (by omega))
    (fun i hi => m₃ _ (by omega)) (fun i hi => m₃ _ (by omega))
  -- prefix sums
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₃ 1511 0 (by omega)) fun hw₄ => ?_
  refine spec_seq ?_
  refine spec_use (osPref_exec (P := P) hL _ hw₄
    (hI₃.mono (fun r hr => upd_other _ _ _ (by omega)) (fun _ _ => rfl) (fun _ _ => rfl))
    (by config_simp; exact r410₃) (by config_simp) (by config_simp; exact z₃)
    (by config_simp; exact cnt₃)) ?_
  intro c₅ k₅ hk₅ hw₅ ⟨pre₅, m₅, n₅, r410₅, rr₅, rm₅, o₅⟩
  config_simp at m₅
  config_simp at n₅
  config_simp at rr₅
  config_simp at rm₅
  config_simp at o₅
  have hI₅ := hI₃.mono (fun r hr => by rw [n₅ r (by omega)]; exact upd_other _ _ _ (by omega))
    (fun i hi => m₅ _ (by omega)) (fun i hi => m₅ _ (by omega))
  -- the cursors
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₅ 1511 0 (by omega)) fun hw₆ => ?_
  refine spec_seq ?_
  refine spec_use (osCopy_exec (P := P) hL _ hw₆
    (hI₅.mono (fun r hr => upd_other _ _ _ (by omega)) (fun _ _ => rfl) (fun _ _ => rfl))
    (by config_simp; exact r410₅) (by config_simp)) ?_
  intro c₇ k₇ hk₇ hw₇ ⟨cur₇, m₇, n₇, r410₇, rr₇, rm₇, o₇⟩
  config_simp at cur₇
  config_simp at m₇
  config_simp at n₇
  config_simp at rr₇
  config_simp at rm₇
  config_simp at o₇
  have hI₇ := hI₅.mono (fun r hr => by rw [n₇ r (by omega)]; exact upd_other _ _ _ (by omega))
    (fun i hi => m₇ _ (by omega)) (fun i hi => m₇ _ (by omega))
  -- place
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₇ 1511 0 (by omega)) fun hw₈ => ?_
  have hcur : ∀ x < N, ({ c₇ with nreg := upd c₇.nreg 1511 0 } : Config).nmem (Cb + x) =
      (pre (csList T id K (fun _ => 0) M) x).length := by
    intro x hx; config_simp; rw [cur₇ x hx, pre₅ x (by omega)]
  refine spec_seq ?_
  refine spec_use (osPlace_exec (P := P) hL _ hw₈
    (hI₇.mono (fun r hr => upd_other _ _ _ (by omega)) (fun _ _ => rfl) (fun _ _ => rfl))
    (by config_simp; exact r410₇) (by config_simp) hcur) ?_
  intro c₉ k₉ hk₉ hw₉ ⟨B₉, m₉, n₉, r410₉, rr₉, rm₉, o₉⟩
  config_simp at m₉
  config_simp at n₉
  config_simp at rr₉
  config_simp at rm₉
  config_simp at o₉
  have hI₉ := hI₇.mono (fun r hr => by rw [n₉ r (by omega)]; exact upd_other _ _ _ (by omega))
    (fun i hi => m₉ _ (by omega) (by omega)) (fun i hi => m₉ _ (by omega) (by omega))
  -- the offsets
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₉ 1511 0 (by omega)) fun hw₁₀ => ?_
  refine spec_use (osOut_exec (P := P) hL _ hw₁₀
    (hI₉.mono (fun r hr => upd_other _ _ _ (by omega)) (fun _ _ => rfl) (fun _ _ => rfl))
    (by config_simp; exact r410₉) (by config_simp)) ?_
  intro c₁₁ k₁₁ hk₁₁ hw₁₁ ⟨O₁₁, m₁₁, n₁₁, r410₁₁, rr₁₁, rm₁₁, o₁₁⟩
  config_simp at O₁₁
  config_simp at m₁₁
  config_simp at n₁₁
  config_simp at rr₁₁
  config_simp at rm₁₁
  config_simp at o₁₁
  have hob : ∀ x ≤ N, c₉.nmem (Ob + x) = (pre (csList T id K (fun _ => 0) M) x).length :=
    fun x hx => by rw [m₉ _ (by omega) (by omega), m₇ _ (by omega), pre₅ x hx]
  refine ⟨?_, fun x hx => ?_, fun e he => ?_, fun a h1 h2 => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · unfold osCost; omega
  · rw [(O₁₁ x hx).1, (O₁₁ x hx).2, hob x (by omega), hob (x + 1) (by omega)]
    exact ⟨rfl, rfl⟩
  · obtain ⟨x, hx, j, hj, rfl, hg⟩ := pre_getElem _ N e he
    have hgd : (pre (csList T id K (fun _ => 0) M) N).getD
        ((pre (csList T id K (fun _ => 0) M) x).length + j) (0, 0, 0) =
        (blk (csList T id K (fun _ => 0) M) x).getD j (0, 0, 0) := by
      rw [List.getD_eq_getElem _ _ he, List.getD_eq_getElem _ _ hj]; exact hg
    have hNM := length_pre_csList_le _ rfl (T := T) (H := id) (K := K) (Lz := fun _ => 0)
      (M := M) N
    rw [hgd, m₁₁ _ (by omega)]
    exact B₉ x hx j hj
  · rw [m₁₁ a (by omega), m₉ a (by omega) (by omega), m₇ a (by omega), m₅ a (by omega),
      m₃ a (by omega), m₁ a (by omega)]
  · rw [n₁₁ r hr, upd_other _ _ _ (by omega), n₉ r hr, upd_other _ _ _ (by omega), n₇ r hr,
      upd_other _ _ _ (by omega), n₅ r hr, upd_other _ _ _ (by omega), n₃ r hr,
      upd_other _ _ _ (by omega), n₁ r hr]
  · rw [rr₁₁, rr₉, rr₇, rr₅, rr₃, rr₁]
  · rw [rm₁₁, rm₉, rm₇, rm₅, rm₃, rm₁]
  · rw [o₁₁, o₉, o₇, o₅, o₃, o₁]

/-! ### The out-lists of a piece -/

lemma blk_map_csList (T K : ℕ → ℕ) (Z : ℕ → ℤ) (u : ℕ) : ∀ M : ℕ,
    (blk (csList T id K Z M) u).map (fun a => a.2.1) =
      (List.range M).filter (fun i => decide (K i ≠ 0 ∧ T i = u))
  | 0 => by simp [csList, blk]
  | M + 1 => by
    rw [blk_csList_succ, List.map_append, blk_map_csList T K Z u M, List.range_succ,
      List.filter_append]
    congr 1
    by_cases h : K M ≠ 0 ∧ T M = u
    · simp only [h, ne_eq, not_false_eq_true, and_self, ↓reduceIte, List.map_cons, id_eq,
        List.map_nil, List.filter_cons, decide_true, List.filter_nil]
    · have h' : ¬ (¬ K M = 0 ∧ T M = u) := h
      simp only [h', ↓reduceIte, List.map_nil, List.filter_cons, decide_false, Bool.false_eq_true,
        List.filter_nil]

lemma pre_getD_blk (L : List (ℕ × ℕ × ℤ)) {u N j : ℕ} (hu : u < N) (hj : j < (blk L u).length) :
    (pre L N).getD ((pre L u).length + j) (0, 0, 0) = (blk L u)[j] := by
  obtain ⟨rest, h⟩ := pre_add L (u + 1) (N - (u + 1))
  rw [show u + 1 + (N - (u + 1)) = N by omega, pre_succ, List.append_assoc] at h
  rw [h, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ hj, List.getD_eq_getElem _ _ hj]

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

/-- **`KOut` in memory form**: for the node `ιv x` of every vertex, the words `mem (OLb + ·)`
from `mem (OBb + ιv x)` to `mem (OEb + ιv x)` are the numbers of the darts of `S` leaving `x`,
each once. -/
def OutMem (M : CombMap D V F) (S : Finset D) {nD : ℕ} (σ : D ≃ Fin nD) (ιv : V → ℕ)
    (mem : ℕ → ℕ) (OBb OEb OLb : ℕ) : Prop :=
  ∀ x : V, ∃ ds : List D, ds.Nodup ∧ (∀ d, d ∈ ds ↔ d ∈ S ∧ M.tail d = x) ∧
    mem (OEb + ιv x) = mem (OBb + ιv x) + ds.length ∧ mem (OEb + ιv x) ≤ nD ∧
    ∀ i (h : i < ds.length), mem (OLb + (mem (OBb + ιv x) + i)) = σ ds[i]

/-- The keys of a piece are below the number of nodes. -/
lemma tlt_of_piece {M : CombMap D V F} {nD N : ℕ} (σ : D ≃ Fin nD) {ιv : V → ℕ}
    (hιv : ∀ x, ιv x < N) {T K : ℕ → ℕ} (hT : ∀ d, T (σ d) = ιv (M.tail d)) :
    ∀ i < nD, K i ≠ 0 → T i < N := fun i hi _ => by
  have := hT (σ.symm ⟨i, hi⟩)
  rw [Equiv.apply_symm_apply] at this
  rw [this]; exact hιv _

/-- **The out-lists of a piece on the machine**: `osProg` on the `nD` darts, the key of the dart
numbered `σ d` the node `ιv (M.tail d)` of its tail (`ιv` injective, below `N`), its keep flag
`[d ∈ S]`, writes the out-lists of the piece (`OutMem`) at `OBb`, `OEb`, `Db`, within
`osCost nD N` steps, natural words only. -/
theorem osProg_out {M : CombMap D V F} {S : Finset D} {nD : ℕ} (σ : D ≃ Fin nD) {ιv : V → ℕ}
    (hinj : Function.Injective ιv) (hιv : ∀ x, ιv x < N) (hT : ∀ d, T (σ d) = ιv (M.tail d))
    (hK : ∀ d, K (σ d) = if d ∈ S then 1 else 0)
    (hL : OsLay nD N Tb Kb Ob Cb OBb OEb Db W T K) (c : Config)
    (hc : WordsBounded W c) (hI : OsIn nD N Tb Kb Ob Cb OBb OEb Db T K c) :
    ∃ c' k, Exec P W osProg c c' k ∧ k ≤ osCost nD N ∧ OutMem M S σ ιv c'.nmem OBb OEb Db ∧
      (∀ a, (a < Ob ∨ Ob + 2 * N + 1 ≤ a) → (a < OBb ∨ Db + nD ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1510 ∨ 1520 < r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', k, ex, hk, hOB, hOL, hm, hn, hr, hrm, ho⟩ := osProg_exec (P := P) hL c hc hI
  refine ⟨c', k, ex, hk, fun x => ?_, hm, hn, hr, hrm, ho⟩
  set L := csList T id K (fun _ => 0) nD with hLd
  have huN : ιv x < N := hιv x
  obtain ⟨hb, he⟩ := hOB (ιv x) huN
  let p : ℕ → Bool := fun i => decide (K i ≠ 0 ∧ T i = ιv x)
  let fl := (List.finRange nD).filter (fun j : Fin nD => p j)
  have hfr : (List.finRange nD).map Fin.val = List.range nD :=
    List.ext_getElem (by simp) (fun i h1 h2 => by simp)
  have hmapv : fl.map Fin.val = (blk L (ιv x)).map (fun a => a.2.1) := by
    rw [blk_map_csList, ← hfr, List.filter_map]; rfl
  have hlen : fl.length = (blk L (ιv x)).length := by
    have := congrArg List.length hmapv; simpa using this
  have hmemp : ∀ d, σ d ∈ fl ↔ d ∈ S ∧ M.tail d = x := fun d => by
    simp only [fl, p, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, hT d,
      hK d]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by by_contra h; simp [h] at h1, hinj h2⟩
    · rintro ⟨h1, rfl⟩
      exact ⟨by simp [h1], rfl⟩
  refine ⟨fl.map σ.symm, ((List.nodup_finRange nD).filter _).map σ.symm.injective,
    fun d => ?_, ?_, ?_, fun i hi => ?_⟩
  · rw [List.mem_map]
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [← hmemp, Equiv.apply_symm_apply]; exact hj
    · intro h
      exact ⟨σ d, (hmemp d).2 h, σ.symm_apply_apply d⟩
  · rw [he, hb, List.length_map, hlen, length_pre_succ]
  · rw [he]; exact (length_pre_le _ _).trans (length_csList_le nD)
  · rw [List.getElem_map, Equiv.apply_symm_apply, hb]
    have hi' : i < (blk L (ιv x)).length := by rw [← hlen]; simpa using hi
    have hlt : (pre L (ιv x)).length + i < (pre L N).length := by
      have := length_pre_mono L (show ιv x + 1 ≤ N by omega)
      rw [length_pre_succ] at this; omega
    rw [hOL _ hlt, pre_getD_blk L huN hi']
    have h := List.getElem_of_eq hmapv (i := i) (by simpa using hi)
    simp only [List.getElem_map] at h
    exact h.symm

/-- **`OutMem` at the offsets of the encoding is `KOut`**: if the input words of `P` up to the end
of `OL` are the memory words from `β`, the out-lists written at `β + iOB`, `β + iOE`, `β + iOL`
(nodes below `n`) give `Klein.KOut` for `P`. -/
theorem kout_of_outMem {M : CombMap D V F} {S : Finset D} {nD : ℕ} {σ : D ≃ Fin nD}
    {ιv : V → ℕ} {n k β : ℕ} {mem : ℕ → ℕ} {P : Input} (hιv : ∀ x, ιv x < n)
    (hP : ∀ i < Klein.iOL nD n k + nD, P.data.getD i 0 = mem (β + i))
    (hO : OutMem M S σ ιv mem (β + Klein.iOB nD n k) (β + Klein.iOE nD n k)
      (β + Klein.iOL nD n k)) :
    Klein.KOut M S σ ιv n k P := by
  intro x
  obtain ⟨ds, hnd, hmem, hl, hle, hds⟩ := hO x
  have hx := hιv x
  have eB : P.data.getD (Klein.iOB nD n k + ιv x) 0 = mem (β + Klein.iOB nD n k + ιv x) := by
    rw [hP _ (by unfold Klein.iOB Klein.iOL; omega), Nat.add_assoc]
  have eE : P.data.getD (Klein.iOE nD n k + ιv x) 0 = mem (β + Klein.iOE nD n k + ιv x) := by
    rw [hP _ (by unfold Klein.iOE Klein.iOL; omega), Nat.add_assoc]
  refine ⟨ds, hnd, hmem, by rw [eB, eE]; exact hl, by rw [eE]; exact hle, fun i hi => ?_⟩
  rw [eB, hP _ (by unfold Klein.iOL; omega), ← Nat.add_assoc]
  exact hds i hi

/-- **The out-lists of the one-face encoding on the machine**: with the arrays `NT` (the nodes
of the tails, `ιv` injective below `n`) and `IS` (the flags of `S`) of the encoding at
`β + iNT`, `β + iIS` (by the numbers `σ d` of the darts), and `2 n + 1` words of scratch at
`Ob` off the encoding, `osProg` writes `OB`, `OE`, `OL` at `β + iOB`, `β + iOE`, `β + iOL`
within `osCost nD n` steps, so that **every input agreeing with the memory from `β` up to the
end of `OL` meets `Klein.KOut`**; natural words only. -/
theorem osProg_kout {M : CombMap D V F} {S : Finset D} {nD : ℕ} (σ : D ≃ Fin nD) {ιv : V → ℕ}
    {n k β Ob : ℕ} (hinj : Function.Injective ιv) (hιv : ∀ x, ιv x < n)
    (hS : Ob + 2 * n + 1 ≤ β ∨ β + Klein.iOL nD n k + nD ≤ Ob)
    (hW : Ob + 2 * n + 1 ≤ W ∧ β + Klein.iOL nD n k + nD ≤ W ∧ nD + 1 ≤ W ∧ n + 1 ≤ W)
    (c : Config) (hc : WordsBounded W c)
    (hNT : ∀ d, c.nmem (β + Klein.iNT nD + σ d) = ιv (M.tail d))
    (hIS : ∀ d, c.nmem (β + Klein.iIS nD + σ d) = if d ∈ S then 1 else 0)
    (h00 : c.nreg 1500 = nD) (h01 : c.nreg 1501 = n) (h02 : c.nreg 1502 = β + Klein.iNT nD)
    (h04 : c.nreg 1504 = β + Klein.iIS nD) (h05 : c.nreg 1505 = Ob)
    (h06 : c.nreg 1506 = Ob + n + 1) (h07 : c.nreg 1507 = β + Klein.iOB nD n k)
    (h08 : c.nreg 1508 = β + Klein.iOE nD n k) (h09 : c.nreg 1509 = β + Klein.iOL nD n k) :
    ∃ c' t, Exec P W osProg c c' t ∧ t ≤ osCost nD n ∧
      (∀ Pk : Input, (∀ i < Klein.iOL nD n k + nD, Pk.data.getD i 0 = c'.nmem (β + i)) →
        Klein.KOut M S σ ιv n k Pk) ∧
      (∀ a, (a < Ob ∨ Ob + 2 * n + 1 ≤ a) →
        (a < β + Klein.iOB nD n k ∨ β + Klein.iOL nD n k + nD ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1510 ∨ 1520 < r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨w1, w2, w3, w4⟩ := hW
  have hT : ∀ d, (fun j => c.nmem (β + Klein.iNT nD + j)) (σ d) = ιv (M.tail d) := hNT
  have hK : ∀ d, (fun j => c.nmem (β + Klein.iIS nD + j)) (σ d) = if d ∈ S then 1 else 0 := hIS
  have hL : OsLay nD n (β + Klein.iNT nD) (β + Klein.iIS nD) Ob (Ob + n + 1)
      (β + Klein.iOB nD n k) (β + Klein.iOE nD n k) (β + Klein.iOL nD n k) W
      (fun j => c.nmem (β + Klein.iNT nD + j)) (fun j => c.nmem (β + Klein.iIS nD + j)) := by
    refine ⟨tlt_of_piece σ hιv hT, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (simp only [Klein.iOB, Klein.iOE, Klein.iOL, Klein.iNT, Klein.iIS] at hS w2 ⊢; omega)
  have hI : OsIn nD n (β + Klein.iNT nD) (β + Klein.iIS nD) Ob (Ob + n + 1)
      (β + Klein.iOB nD n k) (β + Klein.iOE nD n k) (β + Klein.iOL nD n k)
      (fun j => c.nmem (β + Klein.iNT nD + j)) (fun j => c.nmem (β + Klein.iIS nD + j)) c :=
    ⟨h00, h01, h02, h04, h05, h06, h07, h08, h09, fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨c', t, ex, ht, hO, hm, hn, hr, hrm, ho⟩ :=
    osProg_out (P := P) σ hinj hιv hT hK hL c hc hI
  refine ⟨c', t, ex, ht, fun Pk hPk => kout_of_outMem hιv hPk hO, fun a h1 h2 => hm a h1 h2,
    hn, hr, hrm, ho⟩

end NegSSSP
