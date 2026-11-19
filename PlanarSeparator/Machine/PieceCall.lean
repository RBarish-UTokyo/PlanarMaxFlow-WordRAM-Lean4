module

public import PlanarSeparator.Machine.PieceCallD

/-!
# The program of a piece: `ltComp` on the machine

**`PlanarSeparator.Piece.pieceCall`** computes the separation `ltComp R (ord N) C w` of a piece
`C` (given as the sorted list `lv C` of its vertices) of a graph `G` on `Fin N` held in global
arrays (`Pre`): for a piece of at most one vertex every mark is `0`; otherwise the labels and
two rank passes, the layout, the dart pass, the separator program as a subroutine
(`PlanarSeparator.ltSubR_exec`) and the write-back of its words to the marks
`mark[lv C j] = (ltOut (ltIn R (ord N) C w)).getD j 0`, then the cleanup (labels, ranks, the
cells `[0, β + len)`, the registers `< 1000`), so that the machine is in its initial state up to
the marks of the vertices of `C`.

* **`pieceCall_exec`**: the run, within
  `2200 #C + (6 Δ + 3400) ∑_{v ∈ C} deg v + 12 ∑_{v ∈ C} w v + 5300` steps.
* **`pieceCall_ltComp`**: the marks are `0`, `1`, `2` exactly on the three parts of
  `ltComp R (ord N) C w`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
  {R : Kasteleyn.RotationSystem G} {w : Fin N → ℕ} {C : Finset (Fin N)} {Z W : ℕ}

/-! ### The cleanup -/

/-- **The cleanup**: the labels, the ranks, the cells `[0, β + len)`, the registers `< 1000`. -/
def cleanup : Stmt :=
  .seq (block [.copyN 1042 1017, .constN 1065 0, .constN 1039 0])
    (.seq mapLoop (.seq rkClr (.seq (block [.constN 1030 0, .addN 1031 1062 1063])
      (.seq (clrLoop 1030 1031 1039 1001) (zeroRegs 1000)))))

variable (C) in
/-- **The state at the end**: the registers `< 1000` zero, the kept registers, the marks
`code j` at `lv C j`, every other cell as at the start. -/
structure Done (W : ℕ) (code : ℕ → ℕ) (c d : Config) : Prop where
  wb : WordsBounded W d
  zreg : ∀ r < 1000, d.nreg r = 0
  regs : ∀ r, Kept r → d.nreg r = c.nreg r
  mark : ∀ j < #C, d.nmem (c.nreg 1019 + lv C j) = code j
  frame : ∀ a, (∀ j < #C, a ≠ c.nreg 1019 + lv C j) → d.nmem a = c.nmem a
  out : d.output = c.output
  rr : d.rreg = c.rreg
  rm : d.rmem = c.rmem

set_option maxHeartbeats 1000000 in
theorem cleanup_exec {P : Input} {c d : Config} (hp : Pre G R w C Z W c)
    (hq : Post G R w C Z W c d) :
    ∃ d' t, Exec P W cleanup d d' t ∧
      t ≤ 4 * psum (gofs G) (lv C) #C + 30 * #C +
        4 * (bB #C (mI G C) (∑ v ∈ C, w v) + lenL #C (mI G C)) + 1020 ∧
      Done C W (fun j => (ltOut (ltIn R (ord N) C w)).getD j 0) c d' := by
  have hk : (clist (ord N) C).length = #C := length_clist_ord C
  set k := #C with hkdef
  set m := mI G C with hmdef
  set sw := ∑ v ∈ C, w v with hswdef
  set β := bB k m sw with hβdef
  set p := pP k m sw with hpdef
  set len := lenL k m with hlendef
  set aOfs := c.nreg 1010
  set aL := c.nreg 1015
  set aLab := c.nreg 1017
  set aRk := c.nreg 1018
  set aMk := c.nreg 1019
  have lZ := hp.lZ; have l0 := hp.l0; have l1 := hp.l1; have l2 := hp.l2; have l3 := hp.l3
  have l4 := hp.l4; have l5 := hp.l5; have l6 := hp.l6; have l7 := hp.l7; have l8 := hp.l8
  have hbig : 2 * β ≤ Z := hp.big
  have hβ : β = p + kK k m + 1 := rfl
  have hlen : len = 2 * k + 3 + 3 * m := rfl
  have hKK : kK k m = 320 * m + 191 * k + 403 := rfl
  have hp0 : 2 * k + 3 + 3 * m + 2 ≤ p := by rw [hpdef]; unfold pP; omega
  have hkN : k ≤ N := by have := card_le_univ C; simpa using this
  have hlvN : ∀ j < k, lv C j < N := fun j hj => lv_lt C (by omega)
  have hlinc : ∀ i j, i < j → j < k → lv C i < lv C j := fun i j h hj => lv_inc C i j h (by omega)
  have hQ : ∀ r, Kept r → d.nreg r = c.nreg r := hq.regs
  -- the first block
  obtain ⟨d₁, t₁, e₁, hw₁, g42, g65, g39, gr₁, gm₁, ht₁⟩ : ∃ d₁ t₁, Exec P W
      (block [.copyN 1042 1017, .constN 1065 0, .constN 1039 0]) d d₁ t₁ ∧ WordsBounded W d₁ ∧
      d₁.nreg 1042 = aLab ∧ d₁.nreg 1065 = 0 ∧ d₁.nreg 1039 = 0 ∧
      (∀ r, r ≠ 1042 → r ≠ 1065 → r ≠ 1039 → d₁.nreg r = d.nreg r) ∧ d₁.nmem = d.nmem ∧
      t₁ = 3 := by
    have hw := hq.wb
    have a17 : d.nreg 1017 = aLab := hQ 1017 (by unfold Kept; omega)
    exec_block
    · omega
    · omega
    · refine ⟨‹WordsBounded _ _›, ?_⟩
      config_simp
      rw [a17]
      refine ⟨rfl, fun r h1 h2 h3 => ?_⟩
      simp only [upd_apply]; split_ifs <;> first | omega | rfl
  have R1 : ∀ r, Kept r → d₁.nreg r = c.nreg r := fun r hr => by
    rw [gr₁ r (by unfold Kept at hr; omega) (by unfold Kept at hr; omega)
      (by unfold Kept at hr; omega), hQ r hr]
  have hdL : ∀ j < k, d.nmem (aL + j) = lv C j := fun j hj => by
    rw [hq.rest _ (by omega) (by omega) (by omega) (fun i hi => by have := hlvN i hi; omega)]
    exact hp.L j hj
  -- the labels
  obtain ⟨d₂, t₂, e₂, ht₂, hlab₂, hfr₂⟩ := mapLoop_exec (P := P) hw₁ (k := k) (ℓ := 0) (pp := p)
    (base := aLab) (lv C) (R1 1001 (Or.inl rfl) ▸ hp.one)
    (by rw [R1 1016 (by unfold Kept; omega)]; exact hp.kk) g65
    (by rw [gr₁ 1064 (by omega) (by omega) (by omega)]; exact hq.r64) g42
    (fun j hj => by rw [R1 1015 (by unfold Kept; omega), gm₁]; exact hdL j hj)
    (fun i hi j hj h => lv_inj C (by omega) (by omega) h)
    (fun i hi j hj => by rw [R1 1015 (by unfold Kept; omega)]; have := hlvN i hi; omega)
    (fun i hi j hj => by simp at hj)
    (by omega) (by rw [R1 1015 (by unfold Kept; omega)]; omega)
    (fun j hj => by have := hlvN j hj; omega) (by omega)
  have R2 : ∀ r, Kept r → d₂.nreg r = c.nreg r := fun r hr => by
    rw [nreg_of_scr e₂ (by decide) (by unfold Kept at hr; omega), R1 r hr]
  have M2 : ∀ a, (∀ j < k, a ≠ aLab + lv C j) → d₂.nmem a = d.nmem a := fun a ha => by
    rw [hfr₂ a ha, gm₁]
  -- the ranks
  have hN := nwfG G R
  obtain ⟨d₃, t₃, e₃, ht₃, hrk₃, hfr₃⟩ := rkClr_exec (P := P) e₂.wb_right (N := N) (M := nD G)
    (k := k) (lv C) (gofs G) (R2 1001 (Or.inl rfl) ▸ hp.one)
    (by rw [Exec.nreg_of_wr e₂ (r := 1039) (by decide)]; exact g39)
    (by rw [R2 1016 (by unfold Kept; omega)]; exact hp.kk)
    (fun j hj => by
      rw [R2 1015 (by unfold Kept; omega), M2 _ (fun i hi => by have := hlvN i hi; omega)]
      exact hdL j hj) hlvN hlinc
    (fun v hv => by
      rw [R2 1010 (by unfold Kept; omega), M2 _ (fun i hi => by have := hlvN i hi; omega),
        hq.rest _ (by omega) (by omega) (by omega) (fun i hi => by have := hlvN i hi; omega)]
      exact hp.ofs v hv) (gofs_mono G) (gofs_le G N)
    (by rw [R2 1015 (by unfold Kept; omega), R2 1018 (by unfold Kept; omega)]; omega)
    (by rw [R2 1010 (by unfold Kept; omega), R2 1018 (by unfold Kept; omega)]; omega)
    (by rw [R2 1018 (by unfold Kept; omega)]; omega)
  rw [R2 1018 (by unfold Kept; omega)] at hrk₃ hfr₃
  have R3 : ∀ r, Kept r → d₃.nreg r = c.nreg r := fun r hr => by
    rw [nreg_of_scr e₃ (by decide) (by unfold Kept at hr; omega), R2 r hr]
  have M3 : ∀ a, (a < aRk ∨ aRk + nD G ≤ a) → d₃.nmem a = d₂.nmem a := fun a ha =>
    hfr₃ a (fun j hj g h1 h2 => by have := gofs_le G (lv C j + 1); omega)
  -- the cells `[0, β + len)`
  obtain ⟨d₄, t₄, e₄, hw₄, g30, g31, gr₄, gm₄, ht₄⟩ : ∃ d₄ t₄, Exec P W
      (block [.constN 1030 0, .addN 1031 1062 1063]) d₃ d₄ t₄ ∧ WordsBounded W d₄ ∧
      d₄.nreg 1030 = 0 ∧ d₄.nreg 1031 = β + len ∧
      (∀ r, r ≠ 1030 → r ≠ 1031 → d₄.nreg r = d₃.nreg r) ∧ d₄.nmem = d₃.nmem ∧ t₄ = 2 := by
    have hw := e₃.wb_right
    have a62 : d₃.nreg 1062 = β := by
      rw [Exec.nreg_of_wr e₃ (r := 1062) (by decide), Exec.nreg_of_wr e₂ (r := 1062) (by decide),
        gr₁ 1062 (by omega) (by omega) (by omega)]; exact hq.r62
    have a63 : d₃.nreg 1063 = len := by
      rw [Exec.nreg_of_wr e₃ (r := 1063) (by decide), Exec.nreg_of_wr e₂ (r := 1063) (by decide),
        gr₁ 1063 (by omega) (by omega) (by omega)]; exact hq.r63
    exec_block
    · omega
    · config_simp; rw [a62, a63]; omega
    · refine ⟨‹WordsBounded _ _›, ?_⟩
      config_simp
      rw [a62, a63]
      refine ⟨rfl, fun r h1 h2 => ?_⟩
      simp only [upd_apply]; split_ifs <;> first | omega | rfl
  obtain ⟨d₅, t₅, e₅, ht₅, hz₅, hfr₅⟩ := clrLoop_exec (P := P) hw₄ (ri := 1030) (rb := 1031)
    (rz := 1039) (one := 1001) (by omega) (by omega) (by omega)
    (by rw [gr₄ 1001 (by omega) (by omega), R3 1001 (Or.inl rfl)]; exact hp.one)
    (by rw [gr₄ 1039 (by omega) (by omega), Exec.nreg_of_wr e₃ (r := 1039) (by decide),
      Exec.nreg_of_wr e₂ (r := 1039) (by decide)]; exact g39) g30 g31 (by omega) (by omega)
  have M5 : ∀ a, β + len ≤ a → d₅.nmem a = d₃.nmem a := fun a ha => by
    rw [hfr₅ a (by omega), gm₄]
  have e₆ := Exec.zeroRegs (P := P) 1000 e₅.wb_right
  have hclean : Exec P W cleanup d _ (t₁ + (t₂ + (t₃ + (t₄ + (t₅ + 1000))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆))))
  -- the final memory
  have F : ∀ a, β + len ≤ a → (a < aLab ∨ aLab + N ≤ a) → (a < aRk ∨ aRk + nD G ≤ a) →
      d₅.nmem a = d.nmem a := fun a h1 h2 h3 => by
    rw [M5 a h1, M3 a h3, M2 a (fun j hj => by have := hlvN j hj; omega)]
  have hβ' : bB #C (mI G C) (∑ v ∈ C, w v) = β := rfl
  have hlen' : lenL #C (mI G C) = len := rfl
  refine ⟨_, _, hclean, by omega, ⟨e₆.wb_right, fun r hr => ?_, fun r hr => ?_,
    fun j hj => ?_, fun a ha => ?_, ?_, ?_, ?_⟩⟩
  · show (if r < 1000 then 0 else _) = 0
    simp [hr]
  · show (if r < 1000 then 0 else d₅.nreg r) = _
    have : ¬ r < 1000 := by unfold Kept at hr; omega
    simp only [this, ↓reduceIte]
    rw [nreg_of_scr e₅ (by decide) (by unfold Kept at hr; omega),
      gr₄ r (by unfold Kept at hr; omega) (by unfold Kept at hr; omega), R3 r hr]
  · show d₅.nmem _ = _
    have := hlvN j hj
    rw [F _ (by omega) (by omega) (by omega)]
    exact hq.mark j hj
  · show d₅.nmem a = _
    by_cases ha1 : a < β + len
    · rw [hz₅ a (Nat.zero_le _) ha1, hp.zero a (by omega)]
    by_cases ha2 : a < Z
    · rw [F a (by omega) (by omega) (by omega), hq.hi a (by omega) ha2, hp.zero a ha2]
    by_cases ha3 : aLab ≤ a ∧ a < aLab + N
    · by_cases hx : ∃ j < k, a = aLab + lv C j
      · obtain ⟨j, hj, rfl⟩ := hx
        rw [M5 _ (by omega), M3 _ (by omega), hlab₂ j hj, hp.lab _ (hlvN j hj)]
        simp
      · push Not at hx
        rw [M5 a (by omega), M3 a (by omega), M2 a hx, show a = aLab + (a - aLab) by omega,
          hq.lab _ (by omega), hp.lab _ (by omega)]
        exact labV_zero C (fun j hj h => hx j (by omega) (by omega))
    by_cases ha4 : aRk ≤ a ∧ a < aRk + nD G
    · by_cases hx : ∃ j < k, gofs G (lv C j) ≤ a - aRk ∧ a - aRk < gofs G (lv C j + 1)
      · obtain ⟨j, hj, h1, h2⟩ := hx
        rw [M5 _ (by omega), show a = aRk + (a - aRk) by omega, hrk₃ j hj _ h1 h2,
          hp.rk _ (by omega)]
      · push Not at hx
        rw [M5 _ (by omega), hfr₃ a (fun j hj g h1 h2 he => by have := hx j hj (by omega); omega),
          M2 a (fun j hj => by have := hlvN j hj; omega),
          show a = aRk + (a - aRk) by omega, hq.rk _ (by omega), hp.rk _ (by omega)]
        obtain ⟨dd, hdd⟩ := exists_dart_of_lt G (show a - aRk < nD G by omega)
        rw [← hdd, rkA_dartNum]
        split_ifs with hin
        · exfalso
          obtain ⟨j, hj, -, hb1, hb2⟩ := block_of_mem G C dd hin.1
          have := hx j (by omega) (by rw [hdd] at hb1; omega)
          rw [hdd] at hb2; omega
        · rfl
    rw [F a (by omega) (by omega) (by omega)]
    exact hq.rest a (by omega) (by omega) (by omega) ha
  · show d₅.output = _
    rw [Exec.output_of_ou e₅ (by decide), Exec.output_of_ou e₄ (by decide),
      Exec.output_of_ou e₃ (by decide), Exec.output_of_ou e₂ (by decide),
      Exec.output_of_ou e₁ (by decide)]; exact hq.out
  · show d₅.rreg = _
    rw [(Exec.real_of_noReal e₅ (by decide)).1, (Exec.real_of_noReal e₄ (by decide)).1,
      (Exec.real_of_noReal e₃ (by decide)).1, (Exec.real_of_noReal e₂ (by decide)).1,
      (Exec.real_of_noReal e₁ (by decide)).1]; exact hq.rr
  · show d₅.rmem = _
    rw [(Exec.real_of_noReal e₅ (by decide)).2, (Exec.real_of_noReal e₄ (by decide)).2,
      (Exec.real_of_noReal e₃ (by decide)).2, (Exec.real_of_noReal e₂ (by decide)).2,
      (Exec.real_of_noReal e₁ (by decide)).2]; exact hq.rm

/-! ### The program of a piece -/

variable (R w C) in
/-- **The mark of the `j`-th vertex of `C`**: `0` for a piece of at most one vertex, otherwise
the `j`-th word printed by the separator program on `ltIn R (ord N) C w` (as `List.getD`). -/
noncomputable def pieceCode (j : ℕ) : ℕ :=
  if #C ≤ 1 then 0 else (ltOut (ltIn R (ord N) C w)).getD j 0

/-- A piece of at most one vertex: every mark `0`. -/
def small : Stmt := .seq (block [.copyN 1042 1019, .constN 1065 0, .constN 1064 0]) mapLoop

/-- A piece of at least two vertices. -/
def bigCase : Stmt := .seq front1 (.seq front2 (.seq back cleanup))

/-- **The program of a piece.** -/
def pieceCall : Stmt := .ifLtN 1001 1016 bigCase small

theorem small_exec {P : Input} {c : Config} (hp : Pre G R w C Z W c) :
    ∃ d t, Exec P W small c d t ∧ t ≤ 15 * #C + 6 ∧ Done C W (fun _ => 0) c d := by
  have hk : (clist (ord N) C).length = #C := length_clist_ord C
  set k := #C with hkdef
  have lZ := hp.lZ; have l0 := hp.l0; have l1 := hp.l1; have l2 := hp.l2; have l3 := hp.l3
  have l4 := hp.l4; have l5 := hp.l5; have l6 := hp.l6; have l7 := hp.l7; have l8 := hp.l8
  have hbig := hp.big
  unfold bB pP kK at hbig
  have hkN : k ≤ N := by have := card_le_univ C; simpa using this
  have hlvN : ∀ j < k, lv C j < N := fun j hj => lv_lt C (by omega)
  obtain ⟨d₁, t₁, e₁, hw₁, g42, g65, g64, gr₁, gm₁, ht₁⟩ : ∃ d₁ t₁, Exec P W
      (block [.copyN 1042 1019, .constN 1065 0, .constN 1064 0]) c d₁ t₁ ∧ WordsBounded W d₁ ∧
      d₁.nreg 1042 = c.nreg 1019 ∧ d₁.nreg 1065 = 0 ∧ d₁.nreg 1064 = 0 ∧
      (∀ r, r < 1030 → d₁.nreg r = c.nreg r) ∧ d₁.nmem = c.nmem ∧ t₁ = 3 := by
    have hw := hp.wb
    exec_block
    · omega
    · omega
    · refine ⟨‹WordsBounded _ _›, ?_⟩
      config_simp
      intro r hr
      simp only [upd_apply]; split_ifs <;> first | omega | rfl
  obtain ⟨d₂, t₂, e₂, ht₂, hmk₂, hfr₂⟩ := mapLoop_exec (P := P) hw₁ (k := k) (ℓ := 0) (pp := 0)
    (base := c.nreg 1019) (lv C) (by rw [gr₁ 1001 (by omega)]; exact hp.one)
    (by rw [gr₁ 1016 (by omega)]; exact hp.kk) g65 g64 g42
    (fun j hj => by rw [gr₁ 1015 (by omega), gm₁]; exact hp.L j hj)
    (fun i hi j hj h => lv_inj C (by omega) (by omega) h)
    (fun i hi j hj => by rw [gr₁ 1015 (by omega)]; have := hlvN i hi; omega)
    (fun i hi j hj => by simp at hj)
    (by omega) (by rw [gr₁ 1015 (by omega)]; omega)
    (fun j hj => by have := hlvN j hj; omega) (by omega)
  have hs : Exec P W small c d₂ (t₁ + t₂) := .seq e₁ e₂
  refine ⟨d₂, _, hs, by omega, ⟨e₂.wb_right, fun r hr => ?_, fun r hr => ?_, fun j hj => ?_,
    fun a ha => ?_, ?_, ?_, ?_⟩⟩
  · rw [nreg_of_scr e₂ (by decide) (by omega), gr₁ r (by omega)]; exact hp.zreg r hr
  · rw [nreg_of_scr e₂ (by decide) (by unfold Kept at hr; omega), gr₁ r (by unfold Kept at hr; omega)]
  · rw [hmk₂ j hj]; simp
  · rw [hfr₂ a ha, gm₁]
  · exact Exec.output_of_ou hs (by decide)
  · exact (Exec.real_of_noReal hs (by decide)).1
  · exact (Exec.real_of_noReal hs (by decide)).2

theorem mI_le_psum : mI G C ≤ psum (gofs G) (lv C) #C := by
  have hq : ∀ d : G.Dart, d.fst ∈ C →
      ((fun g => 0 < labV C (tlG G (rvG G g))) (dartNum G d) ↔ d.snd ∈ C) :=
    fun d h => labV_hq G C d h
  have := cntB_lv_card G C (fun g => 0 < labV C (tlG G (rvG G g))) hq
  rw [length_clist_ord] at this
  rw [mI, ← this]
  exact cntB_le_psum _ _ _ _

theorem gofs_succ (v : Fin N) : gofs G ((v : ℕ) + 1) = gofs G v + G.degree v := by
  unfold gofs
  rw [← G.dart_fst_fiber_card_eq_degree, ← card_union_of_disjoint]
  · congr 1; ext d; simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · intro h
      rcases Nat.lt_or_ge (d.fst : ℕ) v with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Fin.ext (by omega))
    · rintro (h | h)
      · omega
      · rw [h]; omega
  · rw [disjoint_filter]; rintro d _ h rfl; omega

/-- **The darts of the vertices of the piece** are counted by the degrees. -/
theorem psum_lv : psum (gofs G) (lv C) #C = ∑ v ∈ C, G.degree v := by
  unfold psum
  rw [← length_clist_ord C]
  conv_rhs => rw [← map_cemb mem_ord C]
  rw [sum_map, ← Fin.sum_univ_eq_sum_range (fun j => gofs G (lv C j + 1) - gofs G (lv C j))]
  refine sum_congr rfl fun i _ => ?_
  rw [lv_eq C i.2, gofs_succ]
  simp only [Fin.eta]
  omega

/-- **The program of a piece on the machine**: from the state `Pre` (the global arrays of a
plane rotation system `R` of `G` of maximum degree at most `Δ`, the sorted list of a piece `C`
connected inside itself), `pieceCall` runs to the state `Done` with the marks `pieceCode`
(and the rest of the machine as before), within
`2200 #C + (6 Δ + 3400) ∑_{v ∈ C} deg v + 12 ∑_{v ∈ C} w v + 5300` steps. -/
theorem pieceCall_exec {P : Input} {c : Config} (hp : Pre G R w C Z W c) (hR : R.IsPlane)
    (hC : InConn G C) {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) :
    ∃ d t, Exec P W pieceCall c d t ∧
      t ≤ 2200 * #C + (6 * Δ + 3400) * ∑ v ∈ C, G.degree v + 12 * ∑ v ∈ C, w v + 5300 ∧
      Done C W (pieceCode R w C) c d := by
  rw [← psum_lv]
  have hmp := mI_le_psum (G := G) (C := C)
  by_cases h2 : 2 ≤ #C
  · obtain ⟨d₁, t₁, e₁, ht₁, hs₁⟩ := front1_exec (P := P) hp
    obtain ⟨d₂, t₂, e₂, ht₂, hs₂⟩ := front2_exec (P := P) hp hs₁ hΔ
    obtain ⟨d₃, t₃, e₃, ht₃, hs₃⟩ := back_exec (P := P) hp hs₂ hR hC h2
    obtain ⟨d₄, t₄, e₄, ht₄, hs₄⟩ := cleanup_exec (P := P) hp hs₃
    have hc : c.nreg 1001 < c.nreg 1016 := by rw [hp.one, hp.kk]; omega
    refine ⟨d₄, _, .ifLtN_true hc (.seq e₁ (.seq e₂ (.seq e₃ e₄))), ?_, ?_⟩
    · have : (6 * Δ + 3400) * psum (gofs G) (lv C) #C =
          (6 * Δ + 36) * psum (gofs G) (lv C) #C + 3364 * psum (gofs G) (lv C) #C := by ring
      simp only [kK, bB, pP, lenL] at ht₃ ht₄
      omega
    · have hf : pieceCode R w C = fun j => (ltOut (ltIn R (ord N) C w)).getD j 0 := by
        funext j; simp only [pieceCode, show ¬ #C ≤ 1 by omega, ↓reduceIte]
      rw [hf]; exact hs₄
  · obtain ⟨d, t, e, ht, hs⟩ := small_exec (P := P) hp
    have hc : ¬ c.nreg 1001 < c.nreg 1016 := by rw [hp.one, hp.kk]; omega
    refine ⟨d, _, .ifLtN_false hc e, by omega, ?_⟩
    have hf : pieceCode R w C = fun _ => 0 := by
      funext j; simp only [pieceCode, show #C ≤ 1 by omega, ↓reduceIte]
    rw [hf]; exact hs

theorem mem_map_filter_cemb (C : Finset (Fin N)) (q : ℕ → Prop) [DecidablePred q] {j : ℕ}
    (hj : j < (clist (ord N) C).length) :
    cemb (ord N) C ⟨j, hj⟩ ∈
        (univ.filter fun i : Fin (clist (ord N) C).length => q i).map (cemb (ord N) C) ↔ q j := by
  rw [mem_map]
  constructor
  · rintro ⟨i, hi, he⟩
    have := (cemb (ord N) C).injective he
    subst this
    simpa using hi
  · intro h
    exact ⟨⟨j, hj⟩, by simpa using h, rfl⟩

/-- **The marks are the separation `ltComp`**: at the end of `pieceCall`, the mark of a vertex
`v ∈ C` is `0`, `1` or `2` exactly when `v` is in the separator, the first or the second part
of `ltComp R (ord N) C w`. -/
theorem pieceCall_ltComp {c d : Config} (hd : Done C W (pieceCode R w C) c d) {v : Fin N}
    (hv : v ∈ C) :
    (d.nmem (c.nreg 1019 + v) = 0 ↔ v ∈ (ltComp R (ord N) C w).1) ∧
      (d.nmem (c.nreg 1019 + v) = 1 ↔ v ∈ (ltComp R (ord N) C w).2.1) ∧
      (d.nmem (c.nreg 1019 + v) = 2 ↔ v ∈ (ltComp R (ord N) C w).2.2) := by
  have hk : (clist (ord N) C).length = #C := length_clist_ord C
  obtain ⟨j, hj, hjv⟩ := (mem_iff_lv C v).1 hv
  have hv' : cemb (ord N) C ⟨j, hj⟩ = v := Fin.ext (by rw [← lv_eq C hj]; exact hjv)
  rw [← hjv, hd.mark j (by omega)]
  unfold pieceCode ltComp
  by_cases h1 : #C ≤ 1
  · simp only [h1, ↓reduceIte, show (clist (ord N) C).length ≤ 1 by omega]
    simp [hv]
  · simp only [h1, ↓reduceIte, show ¬ (clist (ord N) C).length ≤ 1 by omega]
    rw [← hv', mem_map_filter_cemb C (fun n => (ltOut (ltIn R (ord N) C w)).getD n 0 = 0) hj,
      mem_map_filter_cemb C (fun n => (ltOut (ltIn R (ord N) C w)).getD n 0 = 1) hj,
      mem_map_filter_cemb C (fun n => (ltOut (ltIn R (ord N) C w)).getD n 0 = 2) hj]
    exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

end Piece

end PlanarSeparator
