module

public import PlanarFlow.Monge.FRLoop

/-!
# FR-Dijkstra on the machine: the initialization

* `setup_exec`: the constant registers (`PlanarFlow.Monge.FR.Glob`), within `12` steps;
* `initLoop_exec`: every vertex unsettled and absent, the leaves of the heap of the vertices,
  within `10 N + 2` steps;
* `initWin_exec`: the winners of the internal nodes of the heap of the vertices, bottom-up
  (`hpFix`), within `25 N + 2` steps; the heap is then correct (`PlanarFlow.Monge.FR.WinOK`)
  whatever the keys, since every vertex is absent;
* `gxSetup_exec`: the registers `GX` of the structures of the half blocks, with
  `Lv = ⌊log₂ b⌋ + 1` and `2 ^ TB` computed by two loops.
* `tInit_exec`: an empty triplet structure (or the empty heap of the half blocks): no present
  leaf, both tournaments correct.
* `bInit_exec`: one half block: its registers, an empty triplet structure with the flag `0`, its
  range-minimum structure (when it has a source), and its parameters in the record of its leaf;
  `bLevels_exec`: all the half blocks, level by level.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace FR

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Heap

/-! ### The constants, the vertices and their heap -/

/-- The input registers. -/
structure Inp (P : Prm) (c : Config) : Prop where
  r100 : c.nreg 100 = P.N
  r101 : c.nreg 101 = P.b
  r102 : c.nreg 102 = P.Db
  r103 : c.nreg 103 = P.pb
  r104 : c.nreg 104 = P.ob
  r105 : c.nreg 105 = P.lb
  r106 : c.nreg 106 = P.r
  r107 : c.nreg 107 = P.sb
  r108 : c.nreg 108 = P.db
  r109 : c.nreg 109 = P.wb

variable {P : Prm} {I : Input}

/-- **The constant registers.** -/
theorem setup_exec (hL : Lay P) (c : Config) (hc : WordsBounded P.W c) (hin : Inp P c) :
    ∃ c' k', Exec I P.W setup c c' k' ∧ k' ≤ 12 ∧ Glob P c' ∧
      (∀ r, r < 100 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hw := lay_w hL
  unfold setup
  exec_block
  all_goals first | omega | (config_simp; rw [hin.r100]; omega) | skip
  · config_simp; rw [hin.r100, hin.r109]; omega
  · config_simp; rw [hin.r101]; omega
  · config_simp; rw [hin.r109, hin.r100]; omega
  refine ⟨by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun r hr => by config_simp; upd_tac, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  · exact hin.r100
  · exact hin.r101
  · exact hin.r102
  · exact hin.r103
  · exact hin.r104
  · exact hin.r105
  · exact hin.r106
  · exact hin.r107
  · exact hin.r108
  · exact hin.r109
  · rw [hin.r100, hin.r109]; unfold Prm.hb; ring
  · rw [hin.r101]
  · rw [hin.r109, hin.r100]
  · rw [hin.r101]

/-- The state of the loop over the vertices of the initialization. -/
structure IIn (P : Prm) (c₀ c : Config) : Prop where
  wb : WordsBounded P.W c
  glob : Glob P c
  le : c.nreg 192 ≤ P.N
  keep : ∀ r, r ≠ 191 → r ≠ 192 → c.nreg r = c₀.nreg r
  rr : c.rreg = c₀.rreg
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output
  done : ∀ y < c.nreg 192, sfV P c.nmem y = 0 ∧ prV P c.nmem y = 0 ∧ wnV P c.nmem (P.N + y) = y
  nm : ∀ a < P.sb, c.nmem a = c₀.nmem a

theorem initBody_exec (hL : Lay P) {c₀ : Config} (c : Config) (hI : IIn P c₀ c)
    (hlt : c.nreg 192 < c.nreg 100) :
    ∃ c' k', Exec I P.W initBody c c' k' ∧ IIn P c₀ c' ∧
      (P.N - c'.nreg 192) * 10 + k' + 2 ≤ (P.N - c.nreg 192) * 10 := by
  obtain ⟨hc, hG, hle, hK, hR, hM, hO, hdone, hN⟩ := hI
  have hw := lay_w hL
  have := hL.m5; have := hL.m6
  rw [hG.r100] at hlt
  generalize hj : c.nreg 192 = j at hlt hle hdone
  unfold initBody
  exec_block
  · rw [hG.r107, hj]; omega
  · config_simp; rw [hG.r109, hj]; omega
  · config_simp; rw [hG.r114, hG.r100]; omega
  · config_simp; rw [hG.r114, hG.r100, hj]; omega
  · config_simp; rw [hj, hG.r110]; omega
  refine ⟨⟨‹_›, hG.of fun r h1 h2 => by config_simp; upd_tac,
    by config_simp; rw [hj, hG.r110]; omega,
    fun r h1 h2 => by
      config_simp; rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact hK r h1 h2,
    by config_simp; exact hR, by config_simp; exact hM, by config_simp; exact hO, ?_, ?_⟩, ?_⟩
  · config_simp
    rw [hG.r107, hG.r109, hG.r114, hG.r100, hj, hG.r117, hG.r110]
    intro y hy
    unfold sfV prV wnV
    simp only [upd_apply]
    rcases Nat.lt_or_ge y j with h | h
    · obtain ⟨a1, a2, a3⟩ := hdone y h
      unfold sfV at a1; unfold prV at a2; unfold wnV at a3
      refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega
    · obtain rfl : y = j := by omega
      refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega
  · config_simp
    rw [hG.r107, hG.r109, hG.r114, hG.r100, hj, hG.r117]
    intro a ha
    simp only [upd_apply]
    split_ifs <;> first | omega | exact hN a ha
  · config_simp; rw [hj, hG.r110]
    have : P.N - j = (P.N - (j + 1)) + 1 := by omega
    rw [this, Nat.add_mul, Nat.one_mul]

/-- **The loop over the vertices**: every vertex unsettled and absent, the leaves of the
tournament tree. -/
theorem initLoop_exec (hL : Lay P) (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c)
    (h192 : c.nreg 192 = 0) :
    ∃ c' k', Exec I P.W (.whileLtN 192 100 initBody) c c' k' ∧ k' ≤ P.N * 10 + 2 ∧
      Glob P c' ∧ (∀ r, r ≠ 191 → r ≠ 192 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧
      (∀ y < P.N, sfV P c'.nmem y = 0 ∧ prV P c'.nmem y = 0 ∧ wnV P c'.nmem (P.N + y) = y) ∧
      (∀ a < P.sb, c'.nmem a = c.nmem a) := by
  refine spec_while (IIn P c) (fun c' => (P.N - c'.nreg 192) * 10) (fun _ h => h.wb)
    (fun c' hI hlt => initBody_exec hL c' hI hlt)
    ⟨hc, hG, by rw [h192]; omega, fun _ _ _ => rfl, rfl, rfl, rfl, fun y hy => by omega,
      fun _ _ => rfl⟩ ?_
  intro c' k' hI hn hk
  rw [h192] at hk
  have : c'.nreg 192 = P.N := by have := hI.le; rw [hI.glob.r100] at hn; omega
  refine ⟨by omega, hI.glob, hI.keep, hI.rr, hI.rm, hI.out, fun y hy => hI.done y (by omega),
    hI.nm⟩

/-- The state of the bottom-up computation of the winners: the internal nodes from `r170` on
are correct. -/
structure IW (P : Prm) (c₀ c : Config) : Prop where
  wb : WordsBounded P.W c
  glob : Glob P c
  lo : 1 ≤ c.nreg 170
  hi : c.nreg 170 ≤ P.N
  keep : ∀ r, (r < 170 ∨ 175 ≤ r) → c.nreg r = c₀.nreg r
  keepR : ∀ r, (r < 170 ∨ 172 ≤ r) → c.rreg r = c₀.rreg r
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output
  nm : ∀ a, (a < P.wb + P.N + 1 ∨ P.wb + 2 * P.N ≤ a) → c.nmem a = c₀.nmem a
  inner : ∀ i, c.nreg 170 ≤ i → i < P.N → wnV P c.nmem i < P.N ∧ Anc i (P.N + wnV P c.nmem i) ∧
    wnV P c.nmem i = better (prV P c₀.nmem) (keyV P c₀.rmem) (wnV P c.nmem (2 * i))
      (wnV P c.nmem (2 * i + 1))

lemma IW.child {c₀ c : Config} (h : IW P c₀ c) (hleaf : ∀ y < P.N, wnV P c₀.nmem (P.N + y) = y)
    {ch : ℕ} (h1 : c.nreg 170 ≤ ch) (h2 : ch < 2 * P.N) :
    wnV P c.nmem ch < P.N ∧ Anc ch (P.N + wnV P c.nmem ch) := by
  rcases Nat.lt_or_ge ch P.N with hc | hc
  · exact ⟨(h.inner ch h1 hc).1, (h.inner ch h1 hc).2.1⟩
  · have e : wnV P c.nmem ch = ch - P.N := by
      have := hleaf (ch - P.N) (by omega)
      unfold wnV at this ⊢; rw [h.nm _ (Or.inr (by omega))]
      rw [show P.N + (ch - P.N) = ch by omega] at this; exact this
    rw [e, show P.N + (ch - P.N) = ch by omega]
    exact ⟨by omega, ⟨0, by simp⟩⟩

theorem initWinBody_exec (hL : Lay P) {c₀ : Config}
    (hleaf : ∀ y < P.N, wnV P c₀.nmem (P.N + y) = y) (hpr : ∀ y < P.N, prV P c₀.nmem y ≤ 1)
    (c : Config) (hI : IW P c₀ c) (hlt : c.nreg 110 < c.nreg 170) :
    ∃ c' k', Exec I P.W initWinBody c c' k' ∧ IW P c₀ c' ∧
      (c'.nreg 170 - 1) * 25 + k' + 2 ≤ (c.nreg 170 - 1) * 25 := by
  have hc := hI.wb
  have hG := hI.glob
  have hw := lay_w hL
  rw [hG.r110] at hlt
  generalize hJ : c.nreg 170 = J at hlt
  have hJN := hI.hi; rw [hJ] at hJN
  unfold initWinBody
  refine spec_seq ?_
  refine spec_instr (Exec.subN hc 170 170 110) fun hw₁ => ?_
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁ at hw₁ ⊢
  have f170 : c₁.nreg 170 = J - 1 := by rw [← hc₁]; config_simp; rw [hJ, hG.r110]
  have fK : ∀ r, r ≠ 170 → c₁.nreg r = c.nreg r := fun r h => by rw [← hc₁]; config_simp; upd_tac
  have fN : c₁.nmem = c.nmem := by rw [← hc₁]
  have fM : c₁.rmem = c.rmem := by rw [← hc₁]
  have fR : c₁.rreg = c.rreg := by rw [← hc₁]
  have fO : c₁.output = c.output := by rw [← hc₁]
  have hG₁ : Glob P c₁ := hG.of fun r h1 h2 => fK r (by omega)
  have hch : ∀ ch, J ≤ ch → ch < 2 * P.N → wnV P c.nmem ch < P.N ∧ Anc ch (P.N + wnV P c.nmem ch) :=
    fun ch h1 h2 => hI.child hleaf (by rw [hJ]; exact h1) h2
  have hpr' : ∀ y < P.N, prV P c.nmem y ≤ 1 := fun y hy => by
    unfold prV; rw [hI.nm _ (Or.inl (by omega))]; exact hpr y hy
  refine spec_use (hpFix_exec (I := I) hL c₁ hw₁ hG₁ (by rw [f170]; omega) (by rw [f170]; omega)
    (by rw [f170, fN]; exact (hch _ (by omega) (by omega)).1)
    (by rw [f170, fN]; exact (hch _ (by omega) (by omega)).1) (by rw [fN]; exact hpr')) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hN₂, hM₂, hK₂, hR₂, hO₂⟩
  rw [f170, fN, fM] at hN₂
  have hwn : ∀ i, wnV P c₂.nmem i = if i = J - 1 then better (prV P c.nmem) (keyV P c.rmem)
      (wnV P c.nmem (2 * (J - 1))) (wnV P c.nmem (2 * (J - 1) + 1)) else wnV P c.nmem i := by
    intro i; unfold wnV; rw [hN₂]; simp only [upd_apply]; split_ifs <;> first | rfl | omega
  refine ⟨⟨hw₂, hG₁.of fun r h1 h2 => hK₂ r (by omega), by rw [hK₂ 170 (by omega), f170]; omega,
    by rw [hK₂ 170 (by omega), f170]; omega,
    fun r hr => by rw [hK₂ r (by omega), fK r (by omega)]; exact hI.keep r hr,
    fun r hr => by rw [hR₂ r (by omega), fR]; exact hI.keepR r hr, by rw [hM₂, fM]; exact hI.rm,
    by rw [hO₂, fO]; exact hI.out,
    fun a ha => by rw [hN₂, upd_other _ _ _ (by omega)]; exact hI.nm a ha, ?_⟩, ?_⟩
  · rw [hK₂ 170 (by omega), f170]
    intro i hi1 hi2
    rcases Nat.eq_or_lt_of_le hi1 with e | e
    · subst e
      have e0 : wnV P c₂.nmem (2 * (J - 1)) = wnV P c.nmem (2 * (J - 1)) := by
        rw [hwn]; simp only [show 2 * (J - 1) ≠ J - 1 by omega, ↓reduceIte]
      have e1 : wnV P c₂.nmem (2 * (J - 1) + 1) = wnV P c.nmem (2 * (J - 1) + 1) := by
        rw [hwn]; simp only [show 2 * (J - 1) + 1 ≠ J - 1 by omega, ↓reduceIte]
      have e2 : wnV P c₂.nmem (J - 1) = better (prV P c.nmem) (keyV P c.rmem)
          (wnV P c.nmem (2 * (J - 1))) (wnV P c.nmem (2 * (J - 1) + 1)) := by
        rw [hwn]; simp only [↓reduceIte]
      obtain ⟨a0, a1⟩ := hch (2 * (J - 1)) (by omega) (by omega)
      obtain ⟨b0, b1⟩ := hch (2 * (J - 1) + 1) (by omega) (by omega)
      rw [e0, e1, e2]
      refine ⟨?_, ?_, better_congr (by unfold prV; rw [hI.nm _ (Or.inl (by omega))])
        (by unfold prV; rw [hI.nm _ (Or.inl (by omega))]) (by unfold keyV; rw [hI.rm])
        (by unfold keyV; rw [hI.rm])⟩
      · rcases better_mem (pr := prV P c.nmem) (key := keyV P c.rmem) (wnV P c.nmem (2 * (J - 1)))
          (wnV P c.nmem (2 * (J - 1) + 1)) with e' | e' <;> rw [e'] <;> assumption
      · rcases better_mem (pr := prV P c.nmem) (key := keyV P c.rmem) (wnV P c.nmem (2 * (J - 1)))
          (wnV P c.nmem (2 * (J - 1) + 1)) with e' | e' <;> rw [e']
        · exact anc_of_child (Or.inl a1)
        · exact anc_of_child (Or.inr b1)
    · rw [hwn, hwn (2 * i), hwn (2 * i + 1)]
      simp only [show i ≠ J - 1 by omega, show 2 * i ≠ J - 1 by omega,
        show 2 * i + 1 ≠ J - 1 by omega, ↓reduceIte]
      exact hI.inner i (by rw [hJ]; omega) hi2
  · rw [hK₂ 170 (by omega), f170]
    have : J - 1 = (J - 1 - 1) + 1 := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
    omega

/-- **The winners of the internal nodes**, bottom-up: the tournament tree is correct. -/
theorem initWin_exec (hL : Lay P) (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c)
    (h170 : c.nreg 170 = P.N) (hleaf : ∀ y < P.N, wnV P c.nmem (P.N + y) = y)
    (hpr : ∀ y < P.N, prV P c.nmem y ≤ 1) :
    ∃ c' k', Exec I P.W (.whileLtN 110 170 initWinBody) c c' k' ∧ k' ≤ P.N * 25 + 2 ∧
      Glob P c' ∧ (∀ r, (r < 170 ∨ 175 ≤ r) → c'.nreg r = c.nreg r) ∧
      (∀ r, (r < 170 ∨ 172 ≤ r) → c'.rreg r = c.rreg r) ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧
      (∀ a, (a < P.wb + P.N + 1 ∨ P.wb + 2 * P.N ≤ a) → c'.nmem a = c.nmem a) ∧
      WinOK P.N (prV P c'.nmem) (keyV P c'.rmem) (wnV P c'.nmem) 0 := by
  have hw := lay_w hL
  refine spec_while (IW P c) (fun c' => (c'.nreg 170 - 1) * 25) (fun _ h => h.wb)
    (fun c' hI hlt => initWinBody_exec hL hleaf hpr c' hI hlt)
    ⟨hc, hG, by omega, by omega, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, fun _ _ => rfl,
      fun i hi1 hi2 => by omega⟩ ?_
  intro c' k' hI hn hk
  rw [h170] at hk
  have h1 : c'.nreg 170 = 1 := by have := hI.lo; rw [hI.glob.r110] at hn; omega
  refine ⟨by
      have : (P.N - 1) * 25 ≤ P.N * 25 := Nat.mul_le_mul_right _ (by omega)
      omega, hI.glob, hI.keep, hI.keepR, hI.rm, hI.out, hI.nm, ⟨fun y hy => ?_,
    fun i h1' h2 => hI.child hleaf (by omega) h2, fun i h1' h2 _ => ?_⟩⟩
  · have := hleaf y hy; unfold wnV at this ⊢; rw [hI.nm _ (Or.inr (by omega))]; exact this
  · rw [(hI.inner i (by omega) h2).2.2]
    obtain ⟨a0, -⟩ := hI.child hleaf (ch := 2 * i) (by omega) (by omega)
    obtain ⟨b0, -⟩ := hI.child hleaf (ch := 2 * i + 1) (by omega) (by omega)
    exact (better_congr (by unfold prV; rw [hI.nm _ (Or.inl (by omega))])
      (by unfold prV; rw [hI.nm _ (Or.inl (by omega))]) (by unfold keyV; rw [hI.rm])
      (by unfold keyV; rw [hI.rm])).symm

/-! ### The constants of the structures of the half blocks -/

/-- `Lv = ⌊log₂ b⌋ + 1` in `r195`, by halving `b`. -/
def lvLoop : Stmt :=
  .seq (block [.constN 195 0, .copyN 196 101])
    (.whileLtN 117 196 (block [.divN 196 196 111, .addN 195 195 110]))

/-- `2 ^ TB` in `r198`, the least power of two above `b Lv`, by doubling. -/
def tbLoop : Stmt :=
  .seq (block [.mulN 197 101 195, .addN 197 197 110, .constN 198 1])
    (.whileLtN 198 197 (.instr (.mulN 198 198 111)))

/-- The registers `r240 … r247`. -/
def gxSet : Stmt :=
  block [.constN 199 16, .mulN 199 199 101, .mulN 199 199 195, .addN 240 112 199,
    .addN 241 240 199, .addN 241 241 199, .constN 199 8, .mulN 242 198 199, .addN 242 242 241,
    .copyN 243 198, .constN 199 32, .mulN 244 101 199, .constN 199 4, .mulN 245 195 199,
    .constN 199 16, .mulN 246 198 199, .addN 246 246 241, .constN 199 8, .mulN 247 101 199,
    .mulN 247 247 195]

/-- **The constants of the structures of the half blocks.** -/
def gxSetup : Stmt := .seq lvLoop (.seq tbLoop gxSet)

/-- `Lv` and `2 ^ TB` below the word bound. -/
lemma lay_gx (hL : Lay P) : P.Lv ≤ P.b ∧ 2 ^ P.TB ≤ 2 * (P.b * P.Lv) ∧
    P.rb + 8 * P.b * P.Lv * P.Lv + 4 * P.b + 16 ≤ P.W := by
  refine ⟨?_, two_pow_TB_le hL, hL.wx⟩
  unfold Prm.Lv
  have := Nat.log_lt_self 2 (show P.b ≠ 0 by have := hL.b_pos; omega)
  omega

theorem lvLoop_exec (hL : Lay P) (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c) :
    ∃ c' k', Exec I P.W lvLoop c c' k' ∧ k' ≤ 4 * P.Lv + 4 ∧
      (c'.nreg 195 = P.Lv ∧ (∀ r, r ≠ 195 → r ≠ 196 → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have hb := hL.b_pos
  have hw := lay_w hL
  obtain ⟨hLv, -, -⟩ := lay_gx hL
  unfold lvLoop
  refine spec_seq ?_
  exec_block
  · omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have fK : ∀ r, r ≠ 195 → r ≠ 196 → c₁.nreg r = c.nreg r := fun r h1 h2 => by
    rw [← hc₁]; config_simp; upd_tac
  obtain ⟨j', c', k', e, ⟨hw', h196, h195, hj, hK, hR, hN, hM, hO⟩, hn, hk⟩ :=
    Exec.whileLtN_ghost (P := I) (W := P.W) (a := 117) (b := 196)
    (body := block [.divN 196 196 111, .addN 195 195 110])
    (fun j c' => WordsBounded P.W c' ∧ c'.nreg 196 = P.b / 2 ^ j ∧ c'.nreg 195 = j ∧
      j ≤ P.Lv ∧ (∀ r, r ≠ 195 → r ≠ 196 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output)
    (fun j _ => 4 * (P.Lv - j)) (fun _ _ h => h.1)
    (fun j c₂ ⟨hw₂, h196, h195, hj, hK, hR, hN, hM, hO⟩ hlt => by
      have g117 : c₂.nreg 117 = 0 := (hK 117 (by omega) (by omega)).trans hG.r117
      have g111 : c₂.nreg 111 = 2 := (hK 111 (by omega) (by omega)).trans hG.r111
      have g110 : c₂.nreg 110 = 1 := (hK 110 (by omega) (by omega)).trans hG.r110
      rw [g117, h196] at hlt
      have hpj : 2 ^ j ≤ P.b := by
        by_contra h; rw [Nat.div_eq_of_lt (by omega)] at hlt; omega
      have hjl : j + 1 ≤ P.Lv := by
        unfold Prm.Lv; have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpj; omega
      refine ⟨j + 1, ?_⟩
      exec_block
      · config_simp; rw [h195, g110]; omega
      refine ⟨⟨‹_›, ?_, ?_, hjl, fun r h1 h2 => ?_, hR, hN, hM, hO⟩, by omega⟩
      · config_simp; rw [h196, g111, pow_succ, Nat.div_div_eq_div_mul]
      · config_simp; rw [h195, g110]
      · config_simp; rw [upd_other _ _ _ h1, upd_other _ _ _ h2]; exact hK r h1 h2)
    (x := 0) ⟨hw₁, by rw [← hc₁]; config_simp; rw [hG.r101]; simp,
      by rw [← hc₁]; config_simp, Nat.zero_le _, fK, by rw [← hc₁], by rw [← hc₁], by rw [← hc₁],
      by rw [← hc₁]⟩
  refine ⟨c', k', e, by omega, ?_, hK, hR, hN, hM, hO⟩
  have g117 : c'.nreg 117 = 0 := (hK 117 (by omega) (by omega)).trans hG.r117
  rw [g117, h196] at hn
  have hlt : P.b < 2 ^ j' := by
    by_contra h; exact hn (Nat.div_pos (by omega) (Nat.two_pow_pos _))
  have := Nat.log_lt_of_lt_pow (b := 2) (by omega) hlt
  unfold Prm.Lv at hj ⊢; omega

theorem tbLoop_exec (hL : Lay P) (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c)
    (h195 : c.nreg 195 = P.Lv) :
    ∃ c' k', Exec I P.W tbLoop c c' k' ∧ k' ≤ 3 * P.TB + 5 ∧
      (c'.nreg 198 = 2 ^ P.TB ∧ (∀ r, r ≠ 197 → r ≠ 198 → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have hb := hL.b_pos
  have hw := lay_w hL
  obtain ⟨hLv, hTB, hwx⟩ := lay_gx hL
  have hbL : 1 ≤ P.b * P.Lv := Nat.one_le_iff_ne_zero.2 (by unfold Prm.Lv; positivity)
  have hbw := bh_le_W hL
  have hbLW : P.b * P.Lv + 1 ≤ P.W := by
    have : P.b * P.Lv ≤ P.b * P.b := Nat.mul_le_mul_left _ hLv
    have := hL.m1; have := hL.m2; have := hL.m3; have := hL.m4; have := hL.m5; have := hL.m6
    nlinarith
  unfold tbLoop
  refine spec_seq ?_
  exec_block
  · rw [hG.r101, h195]; omega
  · config_simp; rw [hG.r101, h195, hG.r110]; omega
  · omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have fK : ∀ r, r ≠ 197 → r ≠ 198 → c₁.nreg r = c.nreg r := fun r h1 h2 => by
    rw [← hc₁]; config_simp; upd_tac
  have f197 : c₁.nreg 197 = P.b * P.Lv + 1 := by
    rw [← hc₁]; config_simp; rw [hG.r101, h195, hG.r110]
  obtain ⟨j', c', k', e, ⟨hw', h198, hj, hK, h197, hR, hN, hM, hO⟩, hn, hk⟩ :=
    Exec.whileLtN_ghost (P := I) (W := P.W) (a := 198) (b := 197)
    (body := .instr (.mulN 198 198 111))
    (fun j c' => WordsBounded P.W c' ∧ c'.nreg 198 = 2 ^ j ∧ j ≤ P.TB ∧
      (∀ r, r ≠ 197 → r ≠ 198 → c'.nreg r = c.nreg r) ∧ c'.nreg 197 = P.b * P.Lv + 1 ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output)
    (fun j _ => 3 * (P.TB - j)) (fun _ _ h => h.1)
    (fun j c₂ ⟨hw₂, h198, hj, hK, h197, hR, hN, hM, hO⟩ hlt => by
      have g111 : c₂.nreg 111 = 2 := (hK 111 (by omega) (by omega)).trans hG.r111
      rw [h198, h197] at hlt
      have hjl : j + 1 ≤ P.TB := by
        unfold Prm.TB; have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) (show 2 ^ j ≤ P.b * P.Lv
          by omega); omega
      have hp : 2 ^ (j + 1) ≤ 2 ^ P.TB := Nat.pow_le_pow_right (by norm_num) hjl
      refine ⟨j + 1, ?_⟩
      refine spec_instr (Exec.mulN hw₂ 198 198 111 (by
          rw [h198, g111, ← pow_succ]; have := Nat.le_self_pow (n := P.TB) (by omega) 2; omega))
        fun hw₃ => ⟨⟨hw₃, ?_, hjl, fun r h1 h2 => ?_, ?_, hR, hN, hM, hO⟩, by omega⟩
      · config_simp; rw [h198, g111, pow_succ]
      · config_simp; rw [upd_other _ _ _ h2]; exact hK r h1 h2
      · config_simp; exact h197)
    (x := 0) ⟨hw₁, by rw [← hc₁]; config_simp; rfl, Nat.zero_le _, fK, f197, by rw [← hc₁],
      by rw [← hc₁], by rw [← hc₁], by rw [← hc₁]⟩
  refine ⟨c', k', e, by omega, ?_, hK, hR, hN, hM, hO⟩
  rw [h198, h197] at hn
  have := Nat.log_lt_of_lt_pow (b := 2) (by omega) (show P.b * P.Lv < 2 ^ j' by omega)
  unfold Prm.TB at hj ⊢
  rw [show j' = Nat.log 2 (P.b * P.Lv) + 1 by omega] at h198
  exact h198

/-- **The constants of the structures of the half blocks** (`GX`). -/
theorem gxSetup_exec (hL : Lay P) (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c) :
    ∃ c' k', Exec I P.W gxSetup c c' k' ∧ k' ≤ 4 * P.Lv + 3 * P.TB + 29 ∧
      (GX P c' ∧ (∀ r, (r < 195 ∨ (200 ≤ r ∧ r < 240) ∨ 248 ≤ r) → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have hb := hL.b_pos
  have hw := lay_w hL
  have hbw := bh_le_W hL
  obtain ⟨hLv, hTB, hwx⟩ := lay_gx hL
  unfold gxSetup
  refine spec_seq ?_
  refine spec_use (lvLoop_exec (I := I) hL c hc hG) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨h195, hK₁, hR₁, hN₁, hM₁, hO₁⟩
  have hG₁ : Glob P c₁ := hG.of fun r h1 h2 => hK₁ r (by omega) (by omega)
  refine spec_seq ?_
  refine spec_use (tbLoop_exec (I := I) hL c₁ hw₁ hG₁ h195) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨h198, hK₂, hR₂, hN₂, hM₂, hO₂⟩
  have hG₂ : Glob P c₂ := hG₁.of fun r h1 h2 => hK₂ r (by omega) (by omega)
  have g195 : c₂.nreg 195 = P.Lv := (hK₂ 195 (by omega) (by omega)).trans h195
  have q1 : 32 * P.b * P.Lv = 16 * P.b * P.Lv + 16 * P.b * P.Lv := by ring
  have q2 : P.b * 8 * P.Lv + P.b * 8 * P.Lv = 16 * P.b * P.Lv := by ring
  have q3 : 16 * P.b ≤ 16 * P.b * P.Lv := Nat.le_mul_of_pos_right _ (by unfold Prm.Lv; omega)
  have hbw' : P.hb + 16 * P.b * P.Lv + 32 * P.b * P.Lv + 16 * 2 ^ P.TB ≤ P.W := by
    have := bh_le_W hL; unfold Prm.bh Prm.tb at this; omega
  have hbb : 32 * P.b ≤ 32 * P.b * P.Lv := Nat.le_mul_of_pos_right _ (by unfold Prm.Lv; omega)
  clear hwx hTB
  exec_block
  · omega
  · config_simp; rw [hG₂.r101]; omega
  · config_simp; rw [hG₂.r101, g195]; omega
  · config_simp; rw [hG₂.r101, g195, hG₂.r112]; omega
  · config_simp; rw [hG₂.r101, g195, hG₂.r112]; omega
  · config_simp; rw [hG₂.r101, g195, hG₂.r112]; omega
  · omega
  · config_simp; rw [h198]; omega
  · config_simp; rw [h198, hG₂.r101, g195, hG₂.r112]; omega
  · omega
  · config_simp; rw [hG₂.r101]; omega
  · omega
  · config_simp; rw [g195]; omega
  · omega
  · config_simp; rw [h198]; omega
  · config_simp; rw [h198, hG₂.r101, g195, hG₂.r112]; omega
  · omega
  · config_simp; rw [hG₂.r101]; omega
  · config_simp; rw [hG₂.r101, g195]; omega
  generalize hc₃ : (Config.mk _ _ _ _ _ _ : Config) = c₃
  have hw₃ : WordsBounded P.W c₃ := hc₃ ▸ ‹_›
  have fK : ∀ r, (r < 195 ∨ (200 ≤ r ∧ r < 240) ∨ 248 ≤ r) → c₃.nreg r = c.nreg r := by
    intro r hr
    have a1 : r ≠ 199 := by omega
    have a2 : r ≠ 240 := by omega
    have a3 : r ≠ 241 := by omega
    have a4 : r ≠ 242 := by omega
    have a5 : r ≠ 243 := by omega
    have a6 : r ≠ 244 := by omega
    have a7 : r ≠ 245 := by omega
    have a8 : r ≠ 246 := by omega
    have a9 : r ≠ 247 := by omega
    rw [← hc₃]
    simp only [upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3,
      upd_other _ _ _ a4, upd_other _ _ _ a5, upd_other _ _ _ a6, upd_other _ _ _ a7,
      upd_other _ _ _ a8, upd_other _ _ _ a9]
    rw [hK₂ r (by omega) (by omega)]; exact hK₁ r (by omega) (by omega)
  refine ⟨by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fK, by rw [← hc₃]; config_simp; rw [hR₂, hR₁],
    by rw [← hc₃]; config_simp; rw [hN₂, hN₁], by rw [← hc₃]; config_simp; rw [hM₂, hM₁],
    by rw [← hc₃]; config_simp; rw [hO₂, hO₁]⟩
  · rw [← hc₃]; config_simp; rw [hG₂.r101, g195, hG₂.r112]; unfold Prm.tb; ring
  · rw [← hc₃]; config_simp; rw [hG₂.r101, g195, hG₂.r112]; unfold Prm.bh Prm.tb; ring
  · rw [← hc₃]; config_simp; rw [h198, hG₂.r101, g195, hG₂.r112]; unfold Prm.bh Prm.tb; ring
  · rw [← hc₃]; config_simp; exact h198
  · rw [← hc₃]; config_simp; rw [hG₂.r101]; ring
  · rw [← hc₃]; config_simp; rw [g195]; ring
  · rw [← hc₃]; config_simp; rw [h198, hG₂.r101, g195, hG₂.r112]; unfold Prm.rb Prm.bh Prm.tb; ring
  · rw [← hc₃]; config_simp; rw [hG₂.r101, g195]; ring

/-! ### An empty triplet structure -/

/-- One leaf `r198` of an empty structure (`Q = r208`, tournaments at `r209`, `s = r199`):
absent, its own winner in both tournaments. -/
def tLeafBody : Stmt :=
  block [.mulN 197 198 118, .addN 197 197 208, .storeN 197 117, .addN 197 199 198,
    .mulN 197 197 111, .addN 197 197 209, .storeN 197 198, .addN 197 197 110, .storeN 197 198,
    .addN 198 198 110]

/-- One internal node of the bottom-up computation of the tournaments. -/
def tInitBody : Stmt := .seq (.instr (.subN 210 210 110)) tFix

/-- **An empty triplet structure** of `s = r199` leaves at `Q = r208`. -/
def tInit : Stmt :=
  .seq (.seq (.instr (.constN 198 0)) (.whileLtN 198 199 tLeafBody)) <|
  .seq (.instr (.copyN 210 199)) (.whileLtN 110 210 tInitBody)

/-- The state of the loop over the leaves. -/
structure ITL (P : Prm) (Q s : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded P.W c
  glob : Glob P c
  tctx : TCtx Q s c
  r199 : c.nreg 199 = s
  le : c.nreg 198 ≤ s
  keepN : ∀ r, r ≠ 197 → r ≠ 198 → c.nreg r = c₀.nreg r
  rr : c.rreg = c₀.rreg
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output
  nm : ∀ a, (a < Q ∨ Q + 12 * s ≤ a) → c.nmem a = c₀.nmem a
  done : ∀ x < c.nreg 198, tPr Q c.nmem x = 0 ∧ tWn Q s c.nmem (s + x) = x ∧
    tWl Q s c.nmem (s + x) = x

theorem tLeafBody_exec {Q s : ℕ} {c₀ : Config} (hQ : Q + 16 * s ≤ P.W) (c : Config)
    (hI : ITL P Q s c₀ c) (hlt : c.nreg 198 < c.nreg 199) :
    ∃ c' k', Exec I P.W tLeafBody c c' k' ∧ ITL P Q s c₀ c' ∧
      (s - c'.nreg 198) * 12 + k' + 2 ≤ (s - c.nreg 198) * 12 := by
  obtain ⟨hc, hG, hT, h199, hle, hK, hR, hM, hO, hN, hdone⟩ := hI
  rw [h199] at hlt
  generalize hj : c.nreg 198 = j at hlt hle hdone
  have g208 := hT.r208; have g209 := hT.r209
  unfold tLeafBody
  exec_block
  · rw [hj, hG.r118]; omega
  · config_simp; rw [hj, hG.r118, g208]; omega
  · config_simp; rw [hj, h199]; omega
  · config_simp; rw [hj, h199, hG.r111]; omega
  · config_simp; rw [hj, h199, hG.r111, g209]; omega
  · config_simp; rw [hj, h199, hG.r111, g209, hG.r110]; omega
  · config_simp; rw [hj, hG.r110]; omega
  have e1 : j * 8 + Q = Q + 8 * j := by ring
  have e2 : (s + j) * 2 + (Q + 8 * s) = Q + 8 * s + 2 * (s + j) := by ring
  refine ⟨⟨‹_›, hG.of fun r h1 h2 => by config_simp; upd_tac,
    hT.of fun r h1 h2 => by config_simp; upd_tac, by config_simp; exact h199,
    by config_simp; rw [hj, hG.r110]; omega,
    fun r h1 h2 => by config_simp; rw [upd_other _ _ _ h2, upd_other _ _ _ h1]; exact hK r h1 h2,
    by config_simp; exact hR, by config_simp; exact hM, by config_simp; exact hO, ?_, ?_⟩, ?_⟩
  · config_simp
    rw [hj, hG.r118, g208, h199, hG.r111, g209, hG.r110, hG.r117, e1, e2]
    intro a ha
    simp only [upd_apply]
    split_ifs <;> first | omega | exact hN a ha
  · config_simp
    rw [hj, hG.r118, g208, h199, hG.r111, g209, hG.r110, hG.r117, e1, e2]
    intro y hy
    unfold tPr tWn tWl
    simp only [upd_apply]
    rcases Nat.lt_or_ge y j with h | h
    · obtain ⟨a1, a2, a3⟩ := hdone y h
      unfold tPr at a1; unfold tWn at a2; unfold tWl at a3
      refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega
    · obtain rfl : y = j := by omega
      refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega
  · config_simp; rw [hj, hG.r110]
    have : s - j = (s - (j + 1)) + 1 := by omega
    rw [this, Nat.add_mul, Nat.one_mul]

/-- The state of the bottom-up computation of the tournaments: the internal nodes from `r210`
on are correct. -/
structure ITI (P : Prm) (Q s : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded P.W c
  glob : Glob P c
  tctx : TCtx Q s c
  lo : 1 ≤ c.nreg 210
  hi : c.nreg 210 ≤ s
  keepN : ∀ r, (r < 210 ∨ 220 ≤ r) → c.nreg r = c₀.nreg r
  keepR : ∀ r, r ≠ 210 → r ≠ 211 → c.rreg r = c₀.rreg r
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output
  nm : ∀ a, (a < Q + 8 * s + 2 ∨ Q + 10 * s ≤ a) → c.nmem a = c₀.nmem a
  inner : ∀ i, c.nreg 210 ≤ i → i < s →
    (tWn Q s c.nmem i < s ∧ Anc i (s + tWn Q s c.nmem i) ∧
      tWn Q s c.nmem i = better (tPr Q c₀.nmem) (tKey Q c₀.rmem) (tWn Q s c.nmem (2 * i))
        (tWn Q s c.nmem (2 * i + 1))) ∧
    (tWl Q s c.nmem i < s ∧ Anc i (s + tWl Q s c.nmem i) ∧
      tWl Q s c.nmem i = better (tPr Q c₀.nmem) (fun x => (x : ℝ)) (tWl Q s c.nmem (2 * i))
        (tWl Q s c.nmem (2 * i + 1)))

lemma ITI.child {Q s : ℕ} {c₀ c : Config} (h : ITI P Q s c₀ c)
    (hleaf : ∀ x < s, tWn Q s c₀.nmem (s + x) = x ∧ tWl Q s c₀.nmem (s + x) = x)
    {ch : ℕ} (h1 : c.nreg 210 ≤ ch) (h2 : ch < 2 * s) :
    (tWn Q s c.nmem ch < s ∧ Anc ch (s + tWn Q s c.nmem ch)) ∧
      (tWl Q s c.nmem ch < s ∧ Anc ch (s + tWl Q s c.nmem ch)) := by
  rcases Nat.lt_or_ge ch s with hc | hc
  · obtain ⟨⟨a1, a2, -⟩, ⟨b1, b2, -⟩⟩ := h.inner ch h1 hc
    exact ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
  · have e1 : tWn Q s c.nmem ch = ch - s := by
      have := (hleaf (ch - s) (by omega)).1
      unfold tWn at this ⊢; rw [h.nm _ (Or.inr (by omega))]
      rw [show s + (ch - s) = ch by omega] at this; exact this
    have e2 : tWl Q s c.nmem ch = ch - s := by
      have := (hleaf (ch - s) (by omega)).2
      unfold tWl at this ⊢; rw [h.nm _ (Or.inr (by omega))]
      rw [show s + (ch - s) = ch by omega] at this; exact this
    rw [e1, e2, show s + (ch - s) = ch by omega]
    exact ⟨⟨by omega, ⟨0, by simp⟩⟩, ⟨by omega, ⟨0, by simp⟩⟩⟩

theorem tInitBody_exec {Q s : ℕ} {c₀ : Config} (hQ : Q + 16 * s ≤ P.W)
    (hleaf : ∀ x < s, tWn Q s c₀.nmem (s + x) = x ∧ tWl Q s c₀.nmem (s + x) = x)
    (hpr : ∀ x < s, tPr Q c₀.nmem x ≤ 1) (c : Config) (hI : ITI P Q s c₀ c)
    (hlt : c.nreg 110 < c.nreg 210) :
    ∃ c' k', Exec I P.W tInitBody c c' k' ∧ ITI P Q s c₀ c' ∧
      (c'.nreg 210 - 1) * 50 + k' + 2 ≤ (c.nreg 210 - 1) * 50 := by
  have hc := hI.wb
  have hG := hI.glob
  rw [hG.r110] at hlt
  generalize hJ : c.nreg 210 = J at hlt
  have hJs := hI.hi; rw [hJ] at hJs
  unfold tInitBody
  refine spec_seq ?_
  refine spec_instr (Exec.subN hc 210 210 110) fun hw₁ => ?_
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁ at hw₁ ⊢
  have f210 : c₁.nreg 210 = J - 1 := by rw [← hc₁]; config_simp; rw [hJ, hG.r110]
  have fK : ∀ r, r ≠ 210 → c₁.nreg r = c.nreg r := fun r h => by
    rw [← hc₁]; config_simp; upd_tac
  have fN : c₁.nmem = c.nmem := by rw [← hc₁]
  have fM : c₁.rmem = c.rmem := by rw [← hc₁]
  have fR : c₁.rreg = c.rreg := by rw [← hc₁]
  have fO : c₁.output = c.output := by rw [← hc₁]
  have hG₁ : Glob P c₁ := hG.of fun r h1 h2 => fK r (by omega)
  have hT₁ : TCtx Q s c₁ := hI.tctx.of fun r h1 h2 => fK r (by omega)
  have hch : ∀ ch, J ≤ ch → ch < 2 * s →
      (tWn Q s c.nmem ch < s ∧ Anc ch (s + tWn Q s c.nmem ch)) ∧
      (tWl Q s c.nmem ch < s ∧ Anc ch (s + tWl Q s c.nmem ch)) :=
    fun ch h1 h2 => hI.child hleaf (by rw [hJ]; exact h1) h2
  have hprc : ∀ x < s, tPr Q c.nmem x = tPr Q c₀.nmem x := fun x hx =>
    hI.nm _ (Or.inl (by omega))
  have hpr' : ∀ x < s, tPr Q c.nmem x ≤ 1 := fun x hx => by rw [hprc x hx]; exact hpr x hx
  refine spec_seq ?_
  refine spec_use (twWin_exec (I := I) c₁ hw₁ hG₁ hT₁ hQ (by rw [f210]; omega)
    (by rw [f210]; omega) (by rw [f210, fN]; exact (hch _ (by omega) (by omega)).1.1)
    (by rw [f210, fN]; exact (hch _ (by omega) (by omega)).1.1) (by rw [fN]; exact hpr')) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hN₂, hM₂, hK₂, hR₂, hO₂⟩
  rw [f210, fN, fM] at hN₂
  have hG₂ : Glob P c₂ := hG₁.of fun r h1 h2 => hK₂ r (by omega)
  have hT₂ : TCtx Q s c₂ := hT₁.of fun r h1 h2 => hK₂ r (by omega)
  have e210 : c₂.nreg 210 = J - 1 := (hK₂ 210 (by omega)).trans f210
  have hpr₂ : ∀ x < s, tPr Q c₂.nmem x ≤ 1 := fun x hx => by
    rw [tPr_congr (nm := c.nmem) (fun a ha => by rw [hN₂, upd_other _ _ _ (by omega)]) hx]
    exact hpr' x hx
  have hwl₂ : tWl Q s c₂.nmem = tWl Q s c.nmem := by rw [hN₂, tWl_upd_even]
  refine spec_use (twLm_exec (I := I) c₂ hw₂ hG₂ hT₂ hQ (by rw [e210]; omega) (by omega)
    (by rw [e210, hwl₂]; exact (hch _ (by omega) (by omega)).2.1)
    (by rw [e210, hwl₂]; exact (hch _ (by omega) (by omega)).2.1) hpr₂) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hN₃, hM₃, hK₃, hR₃, hO₃⟩
  rw [e210, hwl₂] at hN₃
  have hkey : tKey Q c.rmem = tKey Q c₀.rmem := by funext x; unfold tKey; rw [hI.rm]
  have hpr3 : ∀ x < s, tPr Q c₂.nmem x = tPr Q c₀.nmem x := fun x hx => by
    rw [tPr_congr (nm := c.nmem) (fun a ha => by rw [hN₂, upd_other _ _ _ (by omega)]) hx]
    exact hprc x hx
  -- the new tournaments
  have hwn : ∀ i, tWn Q s c₃.nmem i = if i = J - 1 then better (tPr Q c.nmem) (tKey Q c.rmem)
      (tWn Q s c.nmem (2 * (J - 1))) (tWn Q s c.nmem (2 * (J - 1) + 1))
      else tWn Q s c.nmem i := by
    intro i; unfold tWn; rw [hN₃, upd_other _ _ _ (by omega), hN₂]
    simp only [upd_apply]; split_ifs <;> first | rfl | omega
  have hwl : ∀ i, tWl Q s c₃.nmem i = if i = J - 1 then better (tPr Q c₂.nmem)
      (fun x => (x : ℝ)) (tWl Q s c.nmem (2 * (J - 1))) (tWl Q s c.nmem (2 * (J - 1) + 1))
      else tWl Q s c.nmem i := by
    intro i; unfold tWl; rw [hN₃]
    simp only [upd_apply]
    split_ifs <;> first | rfl | omega | (rw [hN₂, upd_other _ _ _ (by omega)])
  refine ⟨⟨hw₃, hG₂.of fun r h1 h2 => hK₃ r (by omega), hT₂.of fun r h1 h2 => hK₃ r (by omega),
    by rw [hK₃ 210 (by omega), e210]; omega, by rw [hK₃ 210 (by omega), e210]; omega,
    fun r hr => by rw [hK₃ r (by omega), hK₂ r (by omega), fK r (by omega)]; exact hI.keepN r hr,
    fun r h1 h2 => by rw [hR₃, hR₂ r h1 h2, fR]; exact hI.keepR r h1 h2,
    by rw [hM₃, hM₂, fM, hI.rm], by rw [hO₃, hO₂, fO, hI.out],
    fun a ha => by
      rw [hN₃, upd_other _ _ _ (by omega), hN₂, upd_other _ _ _ (by omega)]; exact hI.nm a ha,
    ?_⟩, ?_⟩
  · rw [hK₃ 210 (by omega), e210]
    intro i hi1 hi2
    rcases Nat.eq_or_lt_of_le hi1 with e | e
    · subst e
      obtain ⟨⟨a0, a1⟩, ⟨b0, b1⟩⟩ := hch (2 * (J - 1)) (by omega) (by omega)
      obtain ⟨⟨c0, c1⟩, ⟨d0, d1⟩⟩ := hch (2 * (J - 1) + 1) (by omega) (by omega)
      rw [hwn, hwn (2 * (J - 1)), hwn (2 * (J - 1) + 1), hwl, hwl (2 * (J - 1)),
        hwl (2 * (J - 1) + 1)]
      simp only [show 2 * (J - 1) ≠ J - 1 by omega, show 2 * (J - 1) + 1 ≠ J - 1 by omega,
        ↓reduceIte]
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
      · rcases better_mem (pr := tPr Q c.nmem) (key := tKey Q c.rmem)
          (tWn Q s c.nmem (2 * (J - 1))) (tWn Q s c.nmem (2 * (J - 1) + 1)) with e' | e' <;>
          rw [e'] <;> assumption
      · rcases better_mem (pr := tPr Q c.nmem) (key := tKey Q c.rmem)
          (tWn Q s c.nmem (2 * (J - 1))) (tWn Q s c.nmem (2 * (J - 1) + 1)) with e' | e' <;>
          rw [e']
        · exact anc_of_child (Or.inl a1)
        · exact anc_of_child (Or.inr c1)
      · rw [hkey]; exact better_congr (hprc _ a0) (hprc _ c0) rfl rfl
      · rcases better_mem (pr := tPr Q c₂.nmem) (key := fun x => (x : ℝ))
          (tWl Q s c.nmem (2 * (J - 1))) (tWl Q s c.nmem (2 * (J - 1) + 1)) with e' | e' <;>
          rw [e'] <;> assumption
      · rcases better_mem (pr := tPr Q c₂.nmem) (key := fun x => (x : ℝ))
          (tWl Q s c.nmem (2 * (J - 1))) (tWl Q s c.nmem (2 * (J - 1) + 1)) with e' | e' <;>
          rw [e']
        · exact anc_of_child (Or.inl b1)
        · exact anc_of_child (Or.inr d1)
      · exact better_congr (hpr3 _ b0) (hpr3 _ d0) rfl rfl
    · rw [hwn, hwn (2 * i), hwn (2 * i + 1), hwl, hwl (2 * i), hwl (2 * i + 1)]
      simp only [show i ≠ J - 1 by omega, show 2 * i ≠ J - 1 by omega,
        show 2 * i + 1 ≠ J - 1 by omega, ↓reduceIte]
      exact hI.inner i (by rw [hJ]; omega) hi2
  · rw [hK₃ 210 (by omega), e210]
    have : J - 1 = (J - 1 - 1) + 1 := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
    omega

/-- **An empty triplet structure**: no present leaf, and both tournaments correct; only its
`12 s` cells are written. -/
theorem tInit_exec {Q s : ℕ} (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c)
    (hT : TCtx Q s c) (h199 : c.nreg 199 = s) (hs : 1 ≤ s) (hQ : Q + 16 * s ≤ P.W) :
    ∃ c' k', Exec I P.W tInit c c' k' ∧ k' ≤ 62 * s + 8 ∧
      ((∀ x < s, tPr Q c'.nmem x = 0) ∧
        WinOK s (tPr Q c'.nmem) (tKey Q c'.rmem) (tWn Q s c'.nmem) 0 ∧
        WinOK s (tPr Q c'.nmem) (fun x => (x : ℝ)) (tWl Q s c'.nmem) 0 ∧
        (∀ a, (a < Q ∨ Q + 12 * s ≤ a) → c'.nmem a = c.nmem a) ∧ c'.rmem = c.rmem ∧
        (∀ r, (r < 197 ∨ (199 ≤ r ∧ r < 210) ∨ 220 ≤ r) → c'.nreg r = c.nreg r) ∧
        (∀ r, r ≠ 210 → r ≠ 211 → c'.rreg r = c.rreg r) ∧ c'.output = c.output) := by
  unfold tInit
  refine spec_seq ?_
  refine spec_seq ?_
  refine spec_instr (Exec.constN hc 198 0 (by omega)) fun hw₁ => ?_
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁ at hw₁ ⊢
  have hI₁ : ITL P Q s c c₁ := ⟨hw₁, hG.of fun r h1 h2 => by rw [← hc₁]; config_simp; upd_tac,
    hT.of fun r h1 h2 => by rw [← hc₁]; config_simp; upd_tac,
    by rw [← hc₁]; config_simp; exact h199, by rw [← hc₁]; config_simp; omega,
    fun r h1 h2 => by rw [← hc₁]; config_simp; upd_tac, by rw [← hc₁], by rw [← hc₁],
    by rw [← hc₁], fun a _ => by rw [← hc₁],
    fun x hx => by rw [← hc₁] at hx; config_simp at hx; omega⟩
  refine spec_while (ITL P Q s c) (fun c' => (s - c'.nreg 198) * 12) (fun _ h => h.wb)
    (fun c' hI hlt => tLeafBody_exec hQ c' hI hlt) hI₁ ?_
  intro c₂ k₂ hI₂ hn₂ hk₂
  have h198 : c₂.nreg 198 = s := by have := hI₂.le; rw [hI₂.r199] at hn₂; omega
  have h1₁ : c₁.nreg 198 = 0 := by rw [← hc₁]; config_simp
  rw [h1₁] at hk₂
  have hdone := hI₂.done; rw [h198] at hdone
  refine spec_seq ?_
  refine spec_instr (Exec.copyN hI₂.wb 210 199) fun hw₃ => ?_
  generalize hc₃ : (Config.mk _ _ _ _ _ _ : Config) = c₃ at hw₃ ⊢
  have hG₃ : Glob P c₃ := hI₂.glob.of fun r h1 h2 => by rw [← hc₃]; config_simp; upd_tac
  have hT₃ : TCtx Q s c₃ := hI₂.tctx.of fun r h1 h2 => by rw [← hc₃]; config_simp; upd_tac
  have e3N : c₃.nmem = c₂.nmem := by rw [← hc₃]
  have hleaf : ∀ x < s, tWn Q s c₃.nmem (s + x) = x ∧ tWl Q s c₃.nmem (s + x) = x :=
    fun x hx => by rw [e3N]; exact ⟨(hdone x hx).2.1, (hdone x hx).2.2⟩
  have hpr : ∀ x < s, tPr Q c₃.nmem x ≤ 1 := fun x hx => by rw [e3N, (hdone x hx).1]; omega
  have hI₃ : ITI P Q s c₃ c₃ := ⟨hw₃, hG₃, hT₃, by rw [← hc₃]; config_simp; rw [hI₂.r199]; omega,
    by rw [← hc₃]; config_simp; rw [hI₂.r199], fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl,
    fun _ _ => rfl, fun i h1 h2 => by
      rw [← hc₃] at h1; config_simp at h1; rw [hI₂.r199] at h1; omega⟩
  refine spec_while (ITI P Q s c₃) (fun c' => (c'.nreg 210 - 1) * 50) (fun _ h => h.wb)
    (fun c' hI hlt => tInitBody_exec hQ hleaf hpr c' hI hlt) hI₃ ?_
  intro c₄ k₄ hI₄ hn₄ hk₄
  have h210 : c₄.nreg 210 = 1 := by have := hI₄.lo; rw [hI₄.glob.r110] at hn₄; omega
  have h3 : c₃.nreg 210 = s := by rw [← hc₃]; config_simp; rw [hI₂.r199]
  rw [h3] at hk₄
  have hpr4 : ∀ x < s, tPr Q c₄.nmem x = tPr Q c₃.nmem x := fun x hx =>
    hI₄.nm _ (Or.inl (by omega))
  refine ⟨?_, fun x hx => by rw [hpr4 x hx, e3N]; exact (hdone x hx).1, ⟨fun x hx => ?_,
    fun i h1 h2 => (hI₄.child hleaf (by omega) h2).1, fun i h1 h2 _ => ?_⟩,
    ⟨fun x hx => ?_, fun i h1 h2 => (hI₄.child hleaf (by omega) h2).2, fun i h1 h2 _ => ?_⟩,
    fun a ha => ?_, by rw [hI₄.rm, ← hc₃]; config_simp; rw [hI₂.rm], fun r hr => ?_,
    fun r h1 h2 => ?_, by rw [hI₄.out, ← hc₃]; config_simp; rw [hI₂.out]⟩
  · have : (s - 1) * 50 ≤ s * 50 := Nat.mul_le_mul_right _ (by omega)
    have : (s - 0) * 12 = s * 12 := by rw [Nat.sub_zero]
    omega
  · have := (hleaf x hx).1; unfold tWn at this ⊢; rw [hI₄.nm _ (Or.inr (by omega))]; exact this
  · rw [(hI₄.inner i (by omega) h2).1.2.2]
    obtain ⟨⟨a0, -⟩, -⟩ := hI₄.child hleaf (ch := 2 * i) (by omega) (by omega)
    obtain ⟨⟨b0, -⟩, -⟩ := hI₄.child hleaf (ch := 2 * i + 1) (by omega) (by omega)
    exact (better_congr (hpr4 _ a0) (hpr4 _ b0) (by unfold tKey; rw [hI₄.rm])
      (by unfold tKey; rw [hI₄.rm])).symm
  · have := (hleaf x hx).2; unfold tWl at this ⊢; rw [hI₄.nm _ (Or.inr (by omega))]; exact this
  · rw [(hI₄.inner i (by omega) h2).2.2.2]
    obtain ⟨-, ⟨a0, -⟩⟩ := hI₄.child hleaf (ch := 2 * i) (by omega) (by omega)
    obtain ⟨-, ⟨b0, -⟩⟩ := hI₄.child hleaf (ch := 2 * i + 1) (by omega) (by omega)
    exact (better_congr (hpr4 _ a0) (hpr4 _ b0) rfl rfl).symm
  · rw [hI₄.nm a (by omega), e3N]; exact hI₂.nm a ha
  · rw [hI₄.keepN r (by omega), ← hc₃]; config_simp
    rw [upd_other _ _ _ (by omega), hI₂.keepN r (by omega) (by omega)]
  · rw [hI₄.keepR r h1 h2, ← hc₃]; config_simp; rw [hI₂.rr]

/-! ### One half block -/

/-- The parameters `r300 … r306` of the range-minimum structure of the current half block. -/
def rmPar : Stmt :=
  block [.copyN 300 120, .copyN 301 121, .copyN 302 124, .mulN 303 123 101, .addN 303 303 102,
    .addN 303 303 122, .copyN 304 101, .addN 305 103 122, .subN 306 125 110]

/-- **Initialize the half block `r183` of the level `r182`**: its context, an empty triplet
structure with the flag `0`, its range-minimum structure (when it has a source), and the
parameters in the record of its leaf. -/
def bInit : Stmt :=
  .seq (ctxW 245) <|
  .seq tctx <|
  .seq (.instr (.copyN 199 121)) <|
  .seq tInit <|
  .seq (block [.mulN 197 121 116, .addN 197 197 209, .storeN 197 117]) <|
  .seq (.ifLtN 117 124 (.seq rmqLg (.seq rmPar RM.rmBuild)) .skip) <|
  block [.addN 197 285 183, .mulN 197 197 118, .addN 197 197 241, .addN 197 197 110,
    .storeN 197 182, .addN 197 197 110, .storeN 197 181, .addN 197 197 110, .storeN 197 284,
    .addN 197 197 110, .storeN 197 183, .addN 197 197 110, .storeN 197 285]

/-- **An initialized half block**: no start, both tournaments correct, the flag `0`, the
range-minimum structure built (when it has a source), and the parameters in its leaf. -/
structure InitB (P : Prm) (nm : ℕ → ℕ) (rm : ℕ → ℝ) (t k : ℕ) : Prop where
  pr : ∀ x < 2 ^ t, tPr (tbQ P t k) nm x = 0
  win : WinOK (2 ^ t) (tPr (tbQ P t k) nm) (tKey (tbQ P t k) rm) (tWn (tbQ P t k) (2 ^ t) nm) 0
  wl : WinOK (2 ^ t) (tPr (tbQ P t k) nm) (fun x => (x : ℝ)) (tWl (tbQ P t k) (2 ^ t) nm) 0
  flag : tFlag (tbQ P t k) t nm = 0
  ready : 0 < hbNc P.b (2 ^ t) k → QReady P (rbB P t k) (2 ^ t) k nm
  leaf : LeafP P nm t k

/-- The cost of the initialization of a half block of `2 ^ t` rows. -/
def bInitC (t : ℕ) : ℕ := 83 * 2 ^ t * (2 * t + 2) + 62 * 2 ^ t + 4 * t + 90

set_option maxHeartbeats 1000000 in
/-- **The initialization of a half block.** -/
theorem bInit_exec (hL : Lay P) (hDc : Crossing P.b P.D) {t k : ℕ} (ht : 2 ^ t < P.b)
    (hk : k * 2 ^ t < P.b) (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c) (hX : GX P c)
    (hDa : Data P c) (h182 : c.nreg 182 = 2 ^ t) (h183 : c.nreg 183 = k)
    (h181 : c.nreg 181 = P.rb + 8 * P.b * P.Lv * t) (h284 : c.nreg 284 = P.tb + 32 * P.b * t)
    (h285 : c.nreg 285 = t * P.b) :
    ∃ c' k', Exec I P.W bInit c c' k' ∧ k' ≤ bInitC t ∧
      (InitB P c'.nmem c'.rmem t k ∧
        (∀ a, (a < tbQ P t k ∨ tbQ P t k + 16 * 2 ^ t ≤ a) →
          (a < rbB P t k ∨ rbB P t k + 4 * (t + 1) * 2 ^ t ≤ a) →
          (∀ j, 1 ≤ j → j < 6 → a ≠ P.bh + 8 * bid P t k + j) → c'.nmem a = c.nmem a) ∧
        c'.rmem = c.rmem ∧
        (∀ r, (r < 120 ∨ (126 ≤ r ∧ r < 189) ∨ (190 ≤ r ∧ r < 197) ∨ (220 ≤ r ∧ r < 300)) →
          c'.nreg r = c.nreg r) ∧
        (∀ r < 200, c'.rreg r = c.rreg r) ∧ c'.output = c.output) := by
  have hs1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hw := lay_w hL
  have hbw := bh_le_W hL
  have hQb := tbQ_le_bh ht hk
  have hQt : P.tb ≤ tbQ P t k := tb_le_tbQ
  have hrb := rbB_le_W hL ht hk
  have hrb0 : P.rb ≤ rbB P t k := rb_le_rbB
  have hbr : P.bh + 16 * 2 ^ P.TB = P.rb := rfl
  have hxl := bid_lt ht hk
  have := hL.m5; have := hL.m6; have htb := tb_ge P
  unfold bInit
  refine spec_seq ?_
  refine spec_use (ctxW_exec (I := I) (s := 2 ^ t) (k := k) (LB := P.rb + 8 * P.b * P.Lv * t)
    (m := 4 * P.Lv) hL c hc hG h182 h183 h181 hX.r245 (by omega) (by omega) hk hs1 ht.le
    (by unfold rbB at hrb; omega)) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨hH₁, h189, hK₁, hR₁, hN₁, hM₁, hO₁⟩
  have hG₁ : Glob P c₁ := hG.of fun r h1 h2 => hK₁ r (by omega) (by omega)
  refine spec_seq ?_
  refine spec_use (tctx_exec (I := I) (TB := P.tb + 32 * P.b * t) c₁ hw₁ hG₁ hH₁
    (by rw [hK₁ 284 (by omega) (by omega)]; exact h284) (by unfold tbQ at hQb; omega)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hT₂, hF₂, hN₂, hM₂⟩
  have hT₂' : TCtx (tbQ P t k) (2 ^ t) c₂ := by unfold tbQ; exact hT₂
  have k2 : ∀ r, r ≠ 208 → r ≠ 209 → c₂.nreg r = c₁.nreg r := fun r h1 h2 => hF₂.n r (by omega)
  have hG₂ : Glob P c₂ := hG₁.of fun r h1 h2 => k2 r (by omega) (by omega)
  have hH₂ : HCtx P (rbB P t k) (2 ^ t) k c₂ := hH₁.of fun r h1 h2 => k2 r (by omega) (by omega)
  refine spec_seq ?_
  refine spec_instr (Exec.copyN hw₂ 199 121) fun hw₃ => ?_
  generalize hc₃ : (Config.mk _ _ _ _ _ _ : Config) = c₃ at hw₃ ⊢
  have k3 : ∀ r, r ≠ 199 → c₃.nreg r = c₂.nreg r := fun r h => by rw [← hc₃]; config_simp; upd_tac
  have hG₃ : Glob P c₃ := hG₂.of fun r h1 h2 => k3 r (by omega)
  have hT₃ : TCtx (tbQ P t k) (2 ^ t) c₃ := hT₂'.of fun r h1 h2 => k3 r (by omega)
  refine spec_seq ?_
  refine spec_use (tInit_exec (I := I) c₃ hw₃ hG₃ hT₃
    (by rw [← hc₃]; config_simp; exact hH₂.r121) hs1 (by omega)) ?_
  intro c₄ k₄ hk₄ hw₄ ⟨hpr₄, hW₄, hWl₄, hn₄, hrm₄, hK₄, hR₄, hO₄⟩
  have k4 : ∀ r, (r < 197 ∨ (199 ≤ r ∧ r < 210) ∨ 220 ≤ r) → r ≠ 199 → r ≠ 208 → r ≠ 209 →
      (r < 120 ∨ 126 ≤ r) → r ≠ 189 → c₄.nreg r = c.nreg r := fun r h1 h2 h3 h4 h5 h6 => by
    rw [hK₄ r h1, k3 r h2, k2 r h3 h4]; exact hK₁ r h5 h6
  have hG₄ : Glob P c₄ := hG.of fun r h1 h2 => k4 r (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  have hH₄ : HCtx P (rbB P t k) (2 ^ t) k c₄ := hH₂.of fun r h1 h2 => by
    rw [hK₄ r (by omega), k3 r (by omega)]
  have hT₄ : TCtx (tbQ P t k) (2 ^ t) c₄ := hT₃.of fun r h1 h2 => hK₄ r (by omega)
  -- the flag
  refine spec_seq ?_
  exec_block
  · rw [hH₄.r121, hG₄.r116]; omega
  · config_simp; rw [hH₄.r121, hG₄.r116, hT₄.r209]; omega
  generalize hc₅ : (Config.mk _ _ _ _ _ _ : Config) = c₅
  have hw₅ : WordsBounded P.W c₅ := hc₅ ▸ ‹_›
  have f5N : ∀ a, c₅.nmem a = if a = tbQ P t k + 12 * 2 ^ t then 0 else c₄.nmem a := by
    intro a; rw [← hc₅]; config_simp; rw [hH₄.r121, hG₄.r116, hT₄.r209, hG₄.r117]
    simp only [upd_apply]; split_ifs <;> first | rfl | omega
  have k5 : ∀ r, r ≠ 197 → c₅.nreg r = c₄.nreg r := fun r h => by rw [← hc₅]; config_simp; upd_tac
  have e5M : c₅.rmem = c₄.rmem := by rw [← hc₅]
  have e5R : c₅.rreg = c₄.rreg := by rw [← hc₅]
  have e5O : c₅.output = c₄.output := by rw [← hc₅]
  have hG₅ : Glob P c₅ := hG₄.of fun r h1 h2 => k5 r (by omega)
  have hX₅ : GX P c₅ := hX.of fun r h1 h2 => by
    rw [k5 r (by omega)]; exact k4 r (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
  have hH₅ : HCtx P (rbB P t k) (2 ^ t) k c₅ := hH₄.of fun r h1 h2 => k5 r (by omega)
  have hDa₅ : Data P c₅ := hDa.of hL (fun a ha => by
      rw [f5N, iteF (by omega), hn₄ a (Or.inl (by omega)), ← hc₃]; config_simp
      rw [hN₂, hN₁]) (fun a ha => by rw [e5M, hrm₄, ← hc₃]; config_simp; rw [hM₂, hM₁])
  -- the structure of the half block before the range minima
  have hpr₅ : ∀ x < 2 ^ t, tPr (tbQ P t k) c₅.nmem x = 0 := fun x hx => by
    unfold tPr; rw [f5N, iteF (by omega)]; exact hpr₄ x hx
  have hq5 : ∀ a, tbQ P t k ≤ a → a < tbQ P t k + 12 * 2 ^ t → c₅.nmem a = c₄.nmem a :=
    fun a h1 h2 => by rw [f5N, iteF (by omega)]
  have hflag5 : tFlag (tbQ P t k) t c₅.nmem = 0 := by unfold tFlag; rw [f5N, iteT rfl]
  -- the range-minimum structure
  refine spec_seq ?_
  obtain ⟨c₆, k₆, e₆, hk₆, hK₆, hN₆, hM₆, hR₆, hO₆, hQ₆⟩ : ∃ c₆ k₆, Exec I P.W
      (.ifLtN 117 124 (.seq rmqLg (.seq rmPar RM.rmBuild)) .skip) c₅ c₆ k₆ ∧
      k₆ ≤ 83 * 2 ^ t * (2 * t + 2) + 4 * t + 26 ∧ (∀ r < 300, c₆.nreg r = c₅.nreg r) ∧
      (∀ a, (a < rbB P t k ∨ rbB P t k + 4 * (t + 1) * 2 ^ t ≤ a) → c₆.nmem a = c₅.nmem a) ∧
      c₆.rmem = c₅.rmem ∧ (∀ r < 300, c₆.rreg r = c₅.rreg r) ∧ c₆.output = c₅.output ∧
      (0 < hbNc P.b (2 ^ t) k → QReady P (rbB P t k) (2 ^ t) k c₆.nmem) := by
    by_cases hnc : 0 < hbNc P.b (2 ^ t) k
    · refine spec_ifLtN_true (by rw [hG₅.r117, hH₅.r124]; exact hnc) ?_
      have hlay := rmLay_rbB hL ht hk hnc
      have pT := rmp_T (P := P) (B := rbB P t k) (k := k) (rfl : 2 ^ t = 2 ^ t)
      have ps := rmp_s (P := P) (B := rbB P t k) (k := k) (rfl : 2 ^ t = 2 ^ t)
      have hTs : t ≤ P.W := by have := Nat.lt_two_pow_self (n := t); omega
      refine spec_seq ?_
      refine spec_use (rmqLg_exec (I := I) (T := t) c₅ hw₅ hG₅ hH₅.r121 hTs) ?_
      intro c₇ k₇ hk₇ hw₇ ⟨h307, hK₇, hR₇, hN₇, hM₇, hO₇⟩
      have g : ∀ r, r ≠ 307 → r ≠ 371 → c₇.nreg r = c₅.nreg r := hK₇
      have hsσ : sib k * 2 ^ t < P.b := by unfold hbNc at hnc; omega
      have hsb' : sib k * 2 ^ t * P.b + P.b ≤ P.b * P.b := by
        have := Nat.mul_le_mul_right P.b (show sib k * 2 ^ t + 1 ≤ P.b by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; linarith
      have := hL.m1; have := hL.m2; have := hL.m3; have := hL.m4
      have hDb : P.Db + P.b * P.b ≤ P.W := by omega
      have g101 : c₇.nreg 101 = P.b := (g 101 (by omega) (by omega)).trans hG₅.r101
      have g102 : c₇.nreg 102 = P.Db := (g 102 (by omega) (by omega)).trans hG₅.r102
      have g103 : c₇.nreg 103 = P.pb := (g 103 (by omega) (by omega)).trans hG₅.r103
      have g110 : c₇.nreg 110 = 1 := (g 110 (by omega) (by omega)).trans hG₅.r110
      have g120 : c₇.nreg 120 = rbB P t k := (g 120 (by omega) (by omega)).trans hH₅.r120
      have g121 : c₇.nreg 121 = 2 ^ t := (g 121 (by omega) (by omega)).trans hH₅.r121
      have g122 : c₇.nreg 122 = k * 2 ^ t := (g 122 (by omega) (by omega)).trans hH₅.r122
      have g123 : c₇.nreg 123 = sib k * 2 ^ t := (g 123 (by omega) (by omega)).trans hH₅.r123
      have g124 : c₇.nreg 124 = hbNc P.b (2 ^ t) k := (g 124 (by omega) (by omega)).trans hH₅.r124
      have g125 : c₇.nreg 125 = hbNr P.b (2 ^ t) k := (g 125 (by omega) (by omega)).trans hH₅.r125
      unfold rmPar
      refine spec_seq ?_
      exec_block
      · config_simp; rw [g123, g101]; omega
      · config_simp; rw [g123, g101, g102]; omega
      · config_simp; rw [g123, g101, g102, g122]; omega
      · config_simp; rw [g103, g122]; omega
      generalize hc₈ : (Config.mk _ _ _ _ _ _ : Config) = c₈
      have hw₈ : WordsBounded P.W c₈ := hc₈ ▸ ‹_›
      have hP : RM.RPar (rmp P (rbB P t k) (2 ^ t) k) c₈ := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [← hc₈] <;> config_simp
        · exact g120
        · rw [g121, ps]
        · exact g124
        · rw [g123, g101, g102, g122]; dsimp only [rmp]; ring
        · exact g101
        · rw [g103, g122]; rfl
        · rw [g125, g110]; rfl
        · rw [h307, pT]
      have e8M : c₈.rmem = c₅.rmem := by rw [← hc₈]; config_simp; exact hM₇
      have hF : ∀ ρ < 2 ^ t, ∀ σ < hbNc P.b (2 ^ t) k,
          RM.rmF c₈.rmem (rmp P (rbB P t k) (2 ^ t) k) ρ σ = hbF P.b P.D P.p (2 ^ t) k ρ σ :=
        fun ρ hρ σ hσ => by
          rw [e8M]
          exact rmF_rmp (fun i j hi hj => hDa₅.dmem i j hi hj)
            (fun x hx => hDa₅.pmem x (by have := hL.bN; omega)) hk hρ hσ
      have hA : AntiM (rmp P (rbB P t k) (2 ^ t) k).s (rmp P (rbB P t k) (2 ^ t) k).nc
          (RM.rmF c₈.rmem (rmp P (rbB P t k) (2 ^ t) k)) := by
        have h := antiM_hbF hDc P.p hk
        intro ρ ρ' σ σ' h1 h2 h3 h4
        rw [ps] at h2
        have h4' : σ' < hbNc P.b (2 ^ t) k := h4
        rw [hF ρ (by omega) σ' h4', hF ρ' h2 σ (by omega), hF ρ (by omega) σ (by omega),
          hF ρ' h2 σ' h4']
        exact h ρ ρ' σ σ' h1 h2 h3 h4'
      refine spec_use (RM.rmBuild_exec (I := I) hlay c₈ hw₈ hP hA) ?_
      intro c₉ k₉ hk₉ hw₉ ⟨hB₉, hn₉, hK₉, hR₉, hM₉, hO₉⟩
      have hlg : lg (hbNc P.b (2 ^ t) k) ≤ t + 1 := lg_le_of_le_pow hbNc_le
      have hbc := RM.rmBuildCost_le (rmp P (rbB P t k) (2 ^ t) k)
      rw [ps, pT] at hbc
      have hbc' : 83 * 2 ^ t * (t + lg (hbNc P.b (2 ^ t) k) + 1) ≤ 83 * 2 ^ t * (2 * t + 2) :=
        Nat.mul_le_mul_left _ (by omega)
      refine ⟨?_, fun r hr => ?_, fun a ha => ?_, by rw [hM₉, e8M], fun r hr => ?_, ?_, ?_⟩
      · have : (rmp P (rbB P t k) (2 ^ t) k).nc = hbNc P.b (2 ^ t) k := rfl
        rw [this] at hbc
        omega
      · rw [hK₉ r (by omega), ← hc₈]; config_simp; simp only [upd_apply]
        split_ifs <;> first | omega | exact g r (by omega) (by omega)
      · rw [hn₉ a (by rw [pT, ps]; dsimp only [rmp]; omega), ← hc₈]; config_simp; rw [hN₇]
      · by_cases h301 : 301 ≤ r
        · rw [hR₉ r (by omega), ← hc₈]; config_simp; rw [hR₇]
        · rw [hR₉ r (by omega), ← hc₈]; config_simp; rw [hR₇]
      · rw [hO₉, ← hc₈]; config_simp; rw [hO₇]
      · intro _
        refine ⟨hlay, built_congr_F hB₉ fun ρ hρ σ hσ => hF ρ (by rw [ps] at hρ; exact hρ) σ hσ⟩
    · refine spec_ifLtN_false (by rw [hG₅.r117, hH₅.r124]; exact hnc) ?_
      exact spec_skip hw₅ ⟨by omega, fun _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, rfl,
        fun h => absurd h hnc⟩
  refine ⟨c₆, k₆, e₆, ?_⟩
  have hw₆ := e₆.wb_right
  have hG₆ : Glob P c₆ := hG₅.of fun r h1 h2 => hK₆ r (by omega)
  have hX₆ : GX P c₆ := hX₅.of fun r h1 h2 => hK₆ r (by omega)
  have l : ∀ r, (r = 285 ∨ r = 183 ∨ r = 182 ∨ r = 181 ∨ r = 284) → c₆.nreg r = c.nreg r :=
    fun r hr => by
      rw [hK₆ r (by omega), k5 r (by omega)]
      exact k4 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hxl8 : (t * P.b + k) * 8 + P.bh + 6 ≤ P.W := by
    have := hxl; unfold bid at this; omega
  -- the parameters in the leaf
  exec_block
  · rw [l 285 (by omega), l 183 (by omega), h285, h183]; omega
  · config_simp; rw [l 285 (by omega), l 183 (by omega), h285, h183, hG₆.r118]; omega
  · config_simp; rw [l 285 (by omega), l 183 (by omega), h285, h183, hG₆.r118, hX₆.r241]
    omega
  · config_simp; rw [l 285 (by omega), l 183 (by omega), h285, h183, hG₆.r118, hX₆.r241,
      hG₆.r110]; omega
  · config_simp; rw [l 285 (by omega), l 183 (by omega), h285, h183, hG₆.r118, hX₆.r241,
      hG₆.r110]; omega
  · config_simp; rw [l 285 (by omega), l 183 (by omega), h285, h183, hG₆.r118, hX₆.r241,
      hG₆.r110]; omega
  · config_simp; rw [l 285 (by omega), l 183 (by omega), h285, h183, hG₆.r118, hX₆.r241,
      hG₆.r110]; omega
  · config_simp; rw [l 285 (by omega), l 183 (by omega), h285, h183, hG₆.r118, hX₆.r241,
      hG₆.r110]; omega
  generalize hc₇ : (Config.mk _ _ _ _ _ _ : Config) = c₇
  have hL8 : (c₆.nreg 285 + c₆.nreg 183) * c₆.nreg 118 + c₆.nreg 241 = P.bh + 8 * bid P t k := by
    rw [l 285 (by omega), l 183 (by omega), h285, h183, hG₆.r118, hX₆.r241]; unfold bid; ring
  have f7N : ∀ a, c₇.nmem a =
      if a = P.bh + 8 * bid P t k + 5 then t * P.b
      else if a = P.bh + 8 * bid P t k + 4 then k
      else if a = P.bh + 8 * bid P t k + 3 then P.tb + 32 * P.b * t
      else if a = P.bh + 8 * bid P t k + 2 then P.rb + 8 * P.b * P.Lv * t
      else if a = P.bh + 8 * bid P t k + 1 then 2 ^ t else c₆.nmem a := by
    intro a; rw [← hc₇]; config_simp
    rw [hL8, hG₆.r110, l 285 (by omega), l 183 (by omega), l 182 (by omega), l 181 (by omega),
      l 284 (by omega), h285, h183, h182, h181, h284]
    simp only [upd_apply]
  have e7 : ∀ a, a < P.bh → c₇.nmem a = c₆.nmem a := fun a ha => by
    rw [f7N]; split_ifs <;> first | rfl | omega
  have e7r : ∀ a, P.rb ≤ a → c₇.nmem a = c₆.nmem a := fun a ha => by
    rw [f7N]; split_ifs <;> first | rfl | omega
  have e7M : c₇.rmem = c₆.rmem := by rw [← hc₇]
  have hRB : rbB P t k + 4 * (t + 1) * 2 ^ t ≥ rbB P t k := Nat.le_add_right _ _
  -- the triplet structure: equal to the one after `tInit`, except its flag
  have hq7 : ∀ a, tbQ P t k ≤ a → a < tbQ P t k + 12 * 2 ^ t → c₇.nmem a = c₄.nmem a :=
    fun a h1 h2 => by
      rw [e7 a (by omega), hN₆ a (Or.inl (by omega)), hq5 a h1 h2]
  have hrm7 : c₇.rmem = c₄.rmem := by rw [e7M, hM₆, e5M]
  have pr7 : ∀ x < 2 ^ t, tPr (tbQ P t k) c₇.nmem x = tPr (tbQ P t k) c₄.nmem x := fun x hx =>
    hq7 _ (by omega) (by omega)
  have wn7 : ∀ i, 1 ≤ i → i < 2 * 2 ^ t →
      tWn (tbQ P t k) (2 ^ t) c₇.nmem i = tWn (tbQ P t k) (2 ^ t) c₄.nmem i := fun i h1 h2 =>
    hq7 _ (by omega) (by omega)
  have wl7 : ∀ i, 1 ≤ i → i < 2 * 2 ^ t →
      tWl (tbQ P t k) (2 ^ t) c₇.nmem i = tWl (tbQ P t k) (2 ^ t) c₄.nmem i := fun i h1 h2 =>
    hq7 _ (by omega) (by omega)
  refine ⟨?_, ⟨fun x hx => by rw [pr7 x hx]; exact hpr₄ x hx,
    ((hW₄.congr_wn wn7).congr (fun x hx => pr7 x hx) (fun x hx => by unfold tKey; rw [hrm7])),
    ((hWl₄.congr_wn wl7).congr (fun x hx => pr7 x hx) (fun _ _ => rfl)), ?_,
    fun hnc => (hQ₆ hnc).congr fun a ha => e7r a (le_trans hrb0 ha), ?_⟩,
    fun a h1 h2 h3 => ?_, ?_, fun r hr => ?_, fun r hr => ?_, ?_⟩
  · unfold bInitC; omega
  · unfold tFlag; rw [e7 _ (by omega), hN₆ _ (Or.inl (by omega))]; exact hflag5
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [f7N] <;> simp
  · rw [f7N]
    simp only [show a ≠ P.bh + 8 * bid P t k + 5 from h3 5 (by omega) (by omega),
      show a ≠ P.bh + 8 * bid P t k + 4 from h3 4 (by omega) (by omega),
      show a ≠ P.bh + 8 * bid P t k + 3 from h3 3 (by omega) (by omega),
      show a ≠ P.bh + 8 * bid P t k + 2 from h3 2 (by omega) (by omega),
      show a ≠ P.bh + 8 * bid P t k + 1 from h3 1 (by omega) (by omega), ↓reduceIte]
    rw [hN₆ a h2, f5N, iteF (by omega), hn₄ a (by omega), ← hc₃]; config_simp; rw [hN₂, hN₁]
  · rw [e7M, hM₆, e5M, hrm₄, ← hc₃]; config_simp; rw [hM₂, hM₁]
  · rw [← hc₇]; config_simp; rw [upd_other _ _ _ (by omega), hK₆ r (by omega), k5 r (by omega)]
    exact k4 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · rw [← hc₇]; config_simp
    rw [hR₆ r (by omega), e5R, hR₄ r (by omega) (by omega), ← hc₃]; config_simp
    rw [hF₂.r r (fun h => h), hR₁]
  · rw [← hc₇]; config_simp; rw [hO₆, e5O, hO₄, ← hc₃]; config_simp; rw [hF₂.o, hO₁]

/-! ### All the half blocks -/

/-- The range-minimum structures of two half blocks are disjoint. -/
lemma rbB_disj {t k t' k' : ℕ} (ht : 2 ^ t < P.b) (hk : k * 2 ^ t < P.b) (ht' : 2 ^ t' < P.b)
    (hk' : k' * 2 ^ t' < P.b) (hne : ¬ (t = t' ∧ k = k')) :
    rbB P t k + 4 * (t + 1) * 2 ^ t ≤ rbB P t' k' ∨
      rbB P t' k' + 4 * (t' + 1) * 2 ^ t' ≤ rbB P t k := by
  have h1 := lt_Lv' ht
  have h1' := lt_Lv' ht'
  have hin : ∀ {t k : ℕ}, 2 ^ t < P.b → k * 2 ^ t < P.b →
      4 * P.Lv * (k * 2 ^ t) + 4 * (t + 1) * 2 ^ t ≤ 8 * P.b * P.Lv := by
    intro t k ht hk
    have := lt_Lv' ht
    have a : 4 * (t + 1) * 2 ^ t ≤ 4 * P.Lv * 2 ^ t := by
      have := Nat.mul_le_mul_right (2 ^ t) this; nlinarith
    have b : 4 * P.Lv * (k * 2 ^ t) + 4 * P.Lv * 2 ^ t ≤ 8 * P.b * P.Lv := by
      have := Nat.mul_le_mul_left (4 * P.Lv) (show k * 2 ^ t + 2 ^ t ≤ 2 * P.b by omega)
      nlinarith
    omega
  have i1 := hin ht hk
  have i2 := hin ht' hk'
  unfold rbB
  rcases Nat.lt_trichotomy t t' with h | rfl | h
  · left
    have : 8 * P.b * P.Lv * t + 8 * P.b * P.Lv ≤ 8 * P.b * P.Lv * t' := by
      have := Nat.mul_le_mul_left (8 * P.b * P.Lv) (show t + 1 ≤ t' by omega)
      rw [Nat.mul_add, Nat.mul_one] at this; exact this
    omega
  · have hkk : k ≠ k' := fun h => hne ⟨rfl, h⟩
    have hs : 4 * (t + 1) * 2 ^ t ≤ 4 * P.Lv * 2 ^ t := by
      have := Nat.mul_le_mul_right (2 ^ t) h1; nlinarith
    rcases Nat.lt_or_gt_of_ne hkk with h | h
    · left
      have : 4 * P.Lv * (k * 2 ^ t) + 4 * P.Lv * 2 ^ t ≤ 4 * P.Lv * (k' * 2 ^ t) := by
        have := Nat.mul_le_mul_left (4 * P.Lv)
          (Nat.mul_le_mul_right (2 ^ t) (show k + 1 ≤ k' by omega))
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_add] at this; exact this
      omega
    · right
      have : 4 * P.Lv * (k' * 2 ^ t) + 4 * P.Lv * 2 ^ t ≤ 4 * P.Lv * (k * 2 ^ t) := by
        have := Nat.mul_le_mul_left (4 * P.Lv)
          (Nat.mul_le_mul_right (2 ^ t) (show k' + 1 ≤ k by omega))
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_add] at this; exact this
      omega
  · right
    have : 8 * P.b * P.Lv * t' + 8 * P.b * P.Lv ≤ 8 * P.b * P.Lv * t := by
      have := Nat.mul_le_mul_left (8 * P.b * P.Lv) (show t' + 1 ≤ t by omega)
      rw [Nat.mul_add, Nat.mul_one] at this; exact this
    omega

/-- An initialized half block depends only on its cells. -/
lemma InitB.congr {nm nm' : ℕ → ℕ} {rm rm' : ℕ → ℝ} {t k : ℕ} (h : InitB P nm rm t k)
    (hq : ∀ a, tbQ P t k ≤ a → a < tbQ P t k + 16 * 2 ^ t → nm' a = nm a)
    (hqr : ∀ a, tbQ P t k ≤ a → a < tbQ P t k + 8 * 2 ^ t → rm' a = rm a)
    (hr : ∀ a, rbB P t k ≤ a → a < rbB P t k + 4 * (t + 1) * 2 ^ t → nm' a = nm a)
    (hl : ∀ j, 1 ≤ j → j < 6 → nm' (P.bh + 8 * bid P t k + j) = nm (P.bh + 8 * bid P t k + j)) :
    InitB P nm' rm' t k := by
  have hs1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have p : ∀ x < 2 ^ t, tPr (tbQ P t k) nm' x = tPr (tbQ P t k) nm x := fun x hx =>
    hq _ (by omega) (by omega)
  have wn : ∀ i, 1 ≤ i → i < 2 * 2 ^ t →
      tWn (tbQ P t k) (2 ^ t) nm' i = tWn (tbQ P t k) (2 ^ t) nm i := fun i h1 h2 =>
    hq _ (by omega) (by omega)
  have wl : ∀ i, 1 ≤ i → i < 2 * 2 ^ t →
      tWl (tbQ P t k) (2 ^ t) nm' i = tWl (tbQ P t k) (2 ^ t) nm i := fun i h1 h2 =>
    hq _ (by omega) (by omega)
  have ky : ∀ x < 2 ^ t, tKey (tbQ P t k) rm' x = tKey (tbQ P t k) rm x := fun x hx =>
    hqr _ (by omega) (by omega)
  obtain ⟨l1, l2, l3, l4, l5⟩ := h.leaf
  refine ⟨fun x hx => by rw [p x hx]; exact h.pr x hx,
    (h.win.congr_wn wn).congr (fun x hx => p x hx) (fun x hx => ky x hx),
    (h.wl.congr_wn wl).congr (fun x hx => p x hx) (fun _ _ => rfl),
    by unfold tFlag; rw [hq _ (by omega) (by omega)]; exact h.flag,
    fun hnc => (h.ready hnc).congr_reg fun a h1 h2 => hr a h1 (by
      rw [rmp_T (rfl : 2 ^ t = 2 ^ t), rmp_s (rfl : 2 ^ t = 2 ^ t)] at h2; exact h2),
    ⟨by rw [hl 1 (by omega) (by omega)]; exact l1, by rw [hl 2 (by omega) (by omega)]; exact l2,
      by rw [hl 3 (by omega) (by omega)]; exact l3, by rw [hl 4 (by omega) (by omega)]; exact l4,
      by rw [hl 5 (by omega) (by omega)]; exact l5⟩⟩

/-- The empty heap of the half blocks. -/
structure BHE (P : Prm) (nm : ℕ → ℕ) (rm : ℕ → ℝ) : Prop where
  pr : ∀ y < 2 ^ P.TB, tPr P.bh nm y = 0
  win : WinOK (2 ^ P.TB) (tPr P.bh nm) (tKey P.bh rm) (tWn P.bh (2 ^ P.TB) nm) 0
  wl : WinOK (2 ^ P.TB) (tPr P.bh nm) (fun x => (x : ℝ)) (tWl P.bh (2 ^ P.TB) nm) 0

/-- The empty heap of the half blocks depends only on its present flags and tournaments. -/
lemma BHE.congr {nm nm' : ℕ → ℕ} {rm rm' : ℕ → ℝ} (h : BHE P nm rm)
    (hn : ∀ y < 2 ^ P.TB, nm' (P.bh + 8 * y) = nm (P.bh + 8 * y))
    (ht : ∀ a, P.bh + 8 * 2 ^ P.TB ≤ a → a < P.bh + 12 * 2 ^ P.TB → nm' a = nm a)
    (hr : ∀ y < 2 ^ P.TB, rm' (P.bh + 8 * y) = rm (P.bh + 8 * y)) : BHE P nm' rm' := by
  have p : ∀ y < 2 ^ P.TB, tPr P.bh nm' y = tPr P.bh nm y := hn
  have wn : ∀ i, 1 ≤ i → i < 2 * 2 ^ P.TB →
      tWn P.bh (2 ^ P.TB) nm' i = tWn P.bh (2 ^ P.TB) nm i := fun i h1 h2 => ht _ (by omega)
        (by omega)
  have wl : ∀ i, 1 ≤ i → i < 2 * 2 ^ P.TB →
      tWl P.bh (2 ^ P.TB) nm' i = tWl P.bh (2 ^ P.TB) nm i := fun i h1 h2 => ht _ (by omega)
        (by omega)
  exact ⟨fun y hy => by rw [p y hy]; exact h.pr y hy,
    (h.win.congr_wn wn).congr (fun y hy => p y hy) (fun y hy => hr y hy),
    (h.wl.congr_wn wl).congr (fun y hy => p y hy) (fun _ _ => rfl)⟩

/-- The half blocks of a level. -/
def bLevel : Stmt :=
  .seq (block [.constN 183 0, .constN 192 0]) <|
  .seq (.whileLtN 192 101 (.seq bInit (block [.addN 183 183 110, .mulN 192 183 182]))) <|
  block [.addN 182 182 182, .addN 181 181 247, .addN 284 284 244, .addN 285 285 101]

/-- **All the half blocks.** -/
def bLevels : Stmt :=
  .seq (block [.copyN 182 110, .copyN 181 246, .copyN 284 240, .constN 285 0])
    (.whileLtN 182 101 bLevel)

/-- The state of the initialization of the half blocks, before the half block `k` of the level
`t₀`. -/
structure IBk (P : Prm) (c₀ : Config) (t₀ : ℕ) (k : ℕ) (c : Config) : Prop where
  wb : WordsBounded P.W c
  glob : Glob P c
  gx : GX P c
  data : Data P c
  r182 : c.nreg 182 = 2 ^ t₀
  r181 : c.nreg 181 = P.rb + 8 * P.b * P.Lv * t₀
  r284 : c.nreg 284 = P.tb + 32 * P.b * t₀
  r285 : c.nreg 285 = t₀ * P.b
  r183 : c.nreg 183 = k
  r192 : c.nreg 192 = k * 2 ^ t₀
  keepN : ∀ r < 100, c.nreg r = c₀.nreg r
  keepR : ∀ r < 100, c.rreg r = c₀.rreg r
  out : c.output = c₀.output
  done : ∀ t k', 2 ^ t < P.b → k' * 2 ^ t < P.b → (t < t₀ ∨ (t = t₀ ∧ k' < k)) →
    InitB P c.nmem c.rmem t k'
  lowN : ∀ a < P.tb, c.nmem a = c₀.nmem a
  rmE : c.rmem = c₀.rmem
  bhe : BHE P c.nmem c.rmem

/-- The memory written by the initialization of a half block keeps the other ones, the
vertices and the empty heap of the half blocks. -/
lemma bInit_frame {nm nm' : ℕ → ℕ} {rm : ℕ → ℝ} {t k : ℕ} (ht : 2 ^ t < P.b)
    (hk : k * 2 ^ t < P.b)
    (hn : ∀ a, (a < tbQ P t k ∨ tbQ P t k + 16 * 2 ^ t ≤ a) →
      (a < rbB P t k ∨ rbB P t k + 4 * (t + 1) * 2 ^ t ≤ a) →
      (∀ j, 1 ≤ j → j < 6 → a ≠ P.bh + 8 * bid P t k + j) → nm' a = nm a) :
    (∀ t' k', 2 ^ t' < P.b → k' * 2 ^ t' < P.b → ¬ (t' = t ∧ k' = k) → InitB P nm rm t' k' →
      InitB P nm' rm t' k') ∧ (∀ a < P.tb, nm' a = nm a) ∧ (BHE P nm rm → BHE P nm' rm) := by
  have hQb := tbQ_le_bh ht hk
  have hQt : P.tb ≤ tbQ P t k := tb_le_tbQ
  have hrb0 : P.rb ≤ rbB P t k := rb_le_rbB
  have hbr : P.bh + 16 * 2 ^ P.TB = P.rb := rfl
  have hxl := bid_lt ht hk
  have hkb : k < P.b := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ Nat.one_le_two_pow) hk
  refine ⟨fun t' k' ht' hk' hne hI => ?_, fun a ha => hn a (Or.inl (by omega))
    (Or.inl (by omega)) (fun j _ _ => by omega), fun hB => hB.congr (fun y hy => ?_)
    (fun a h1 h2 => hn a (Or.inr (by omega)) (Or.inl (by omega)) (fun j _ _ => by omega))
    (fun _ _ => rfl)⟩
  · have hQb' := tbQ_le_bh ht' hk'
    have hQt' : P.tb ≤ tbQ P t' k' := tb_le_tbQ
    have hrb0' : P.rb ≤ rbB P t' k' := rb_le_rbB
    have hxl' := bid_lt ht' hk'
    have hkb' : k' < P.b := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ Nat.one_le_two_pow) hk'
    have hbne : bid P t' k' ≠ bid P t k := fun h => hne (bid_inj hkb' hkb h)
    have hd1 := tbQ_disj ht hk ht' hk' (fun ⟨e1, e2⟩ => hne ⟨e1.symm, e2.symm⟩)
    have hd2 := rbB_disj ht hk ht' hk' (fun ⟨e1, e2⟩ => hne ⟨e1.symm, e2.symm⟩)
    refine hI.congr (fun a h1 h2 => hn a (by omega) (Or.inl (by omega)) (fun j _ _ => by omega))
      (fun _ _ _ => rfl) (fun a h1 h2 => hn a (Or.inr (by omega)) (by omega)
        (fun j _ _ => by omega)) (fun j hj1 hj2 => hn _ (Or.inr (by omega)) (Or.inl (by omega))
        fun j' _ _ => fun h => hbne (by omega))
  · exact hn _ (Or.inr (by omega)) (Or.inl (by omega)) fun j _ _ => by omega

/-- **One half block of the initialization.** -/
theorem bkBody_exec (hL : Lay P) (hDc : Crossing P.b P.D) {c₀ : Config} {t₀ k : ℕ}
    (ht : 2 ^ t₀ < P.b) (c : Config) (hI : IBk P c₀ t₀ k c) (hlt : c.nreg 192 < c.nreg 101) :
    ∃ c' k', Exec I P.W (.seq bInit (block [.addN 183 183 110, .mulN 192 183 182])) c c' k' ∧
      IBk P c₀ t₀ (k + 1) c' ∧
      (P.b / 2 ^ t₀ + 1 - (k + 1)) * (bInitC t₀ + 4) + k' + 2 ≤
        (P.b / 2 ^ t₀ + 1 - k) * (bInitC t₀ + 4) := by
  obtain ⟨hc, hG, hX, hDa, h182, h181, h284, h285, h183, h192, hkN, hkR, hO, hdone, hlow, hrmE,
    hbhe⟩ := hI
  rw [h192, hG.r101] at hlt
  have hk : k * 2 ^ t₀ < P.b := hlt
  have hkd : k ≤ P.b / 2 ^ t₀ := (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2 hk.le
  have hw := lay_w hL
  refine spec_seq ?_
  refine spec_use (bInit_exec (I := I) hL hDc ht hk c hc hG hX hDa h182 h183 h181 h284 h285) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨hB₁, hn₁, hrm₁, hK₁, hR₁, hO₁⟩
  obtain ⟨hfr, hlo, hbh⟩ := bInit_frame (rm := c.rmem) ht hk hn₁
  have hG₁ : Glob P c₁ := hG.of fun r h1 h2 => hK₁ r (by omega)
  have g183 : c₁.nreg 183 = k := (hK₁ 183 (by omega)).trans h183
  have g182 : c₁.nreg 182 = 2 ^ t₀ := (hK₁ 182 (by omega)).trans h182
  have hsbt : P.sb ≤ P.tb := by have := tb_ge P; have := hL.m5; have := hL.m6; omega
  have := Nat.div_le_self P.b (2 ^ t₀)
  exec_block
  · rw [g183, hG₁.r110]; omega
  · config_simp; rw [g183, hG₁.r110, g182]
    have := Nat.mul_le_mul_right (2 ^ t₀) (show k + 1 ≤ P.b / 2 ^ t₀ + 1 by omega)
    have := Nat.div_mul_le_self P.b (2 ^ t₀)
    rw [Nat.add_mul, Nat.one_mul] at *; omega
  generalize hc₂ : (Config.mk _ _ _ _ _ _ : Config) = c₂
  have hw₂ : WordsBounded P.W c₂ := hc₂ ▸ ‹_›
  have fK : ∀ r, (r < 120 ∨ (126 ≤ r ∧ r < 183) ∨ (184 ≤ r ∧ r < 189) ∨ (220 ≤ r ∧ r < 300)) →
      r ≠ 183 → r ≠ 192 → c₂.nreg r = c.nreg r := fun r h0 h1 h2 => by
    rw [← hc₂]; config_simp; rw [upd_other _ _ _ h2, upd_other _ _ _ h1, hK₁ r (by omega)]
  have e2N : c₂.nmem = c₁.nmem := by rw [← hc₂]
  have e2M : c₂.rmem = c₁.rmem := by rw [← hc₂]
  have e2R : c₂.rreg = c₁.rreg := by rw [← hc₂]
  have e2O : c₂.output = c₁.output := by rw [← hc₂]
  refine ⟨⟨hw₂, hG.of fun r h1 h2 => fK r (by omega) (by omega) (by omega),
    hX.of fun r h1 h2 => fK r (by omega) (by omega) (by omega),
    hDa.of hL (fun a ha => by rw [e2N]; exact hlo a (by omega)) (fun a _ => by rw [e2M, hrm₁]),
    by rw [fK 182 (by omega) (by omega) (by omega)]; exact h182,
    by rw [fK 181 (by omega) (by omega) (by omega)]; exact h181,
    by rw [fK 284 (by omega) (by omega) (by omega)]; exact h284,
    by rw [fK 285 (by omega) (by omega) (by omega)]; exact h285,
    by rw [← hc₂]; config_simp; rw [g183, hG₁.r110],
    by rw [← hc₂]; config_simp; rw [g183, hG₁.r110, g182],
    fun r hr => by rw [fK r (by omega) (by omega) (by omega)]; exact hkN r hr,
    fun r hr => by rw [e2R, hR₁ r (by omega)]; exact hkR r hr,
    by rw [e2O, hO₁, hO], fun t k' ht' hk' h => ?_,
    fun a ha => by rw [e2N, hlo a ha]; exact hlow a ha, by rw [e2M, hrm₁, hrmE],
    by rw [e2N, e2M, hrm₁]; exact hbh hbhe⟩, ?_⟩
  · rw [e2N, e2M]
    by_cases hb : t = t₀ ∧ k' = k
    · obtain ⟨rfl, rfl⟩ := hb; exact hB₁
    · rw [hrm₁]
      refine hfr t k' ht' hk' hb (hdone t k' ht' hk' ?_)
      rcases h with h | ⟨rfl, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨rfl, by omega⟩
  · have : P.b / 2 ^ t₀ + 1 - k = (P.b / 2 ^ t₀ + 1 - (k + 1)) + 1 := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
    omega

/-- The cost of the initialization of a level. -/
def levC (P : Prm) (t : ℕ) : ℕ := (P.b / 2 ^ t + 1) * (bInitC t + 4) + 12

/-- The state of the initialization of the half blocks, before the level `t₀`. -/
structure IBl (P : Prm) (c₀ : Config) (t₀ : ℕ) (c : Config) : Prop where
  wb : WordsBounded P.W c
  glob : Glob P c
  gx : GX P c
  data : Data P c
  r182 : c.nreg 182 = 2 ^ t₀
  r181 : c.nreg 181 = P.rb + 8 * P.b * P.Lv * t₀
  r284 : c.nreg 284 = P.tb + 32 * P.b * t₀
  r285 : c.nreg 285 = t₀ * P.b
  tle : t₀ ≤ P.Lv
  keepN : ∀ r < 100, c.nreg r = c₀.nreg r
  keepR : ∀ r < 100, c.rreg r = c₀.rreg r
  out : c.output = c₀.output
  done : ∀ t k', 2 ^ t < P.b → k' * 2 ^ t < P.b → t < t₀ → InitB P c.nmem c.rmem t k'
  lowN : ∀ a < P.tb, c.nmem a = c₀.nmem a
  rmE : c.rmem = c₀.rmem
  bhe : BHE P c.nmem c.rmem

/-- **One level of the initialization.** -/
theorem bLevel_exec (hL : Lay P) (hDc : Crossing P.b P.D) {c₀ : Config} {t₀ : ℕ} (c : Config)
    (hI : IBl P c₀ t₀ c) (hlt : c.nreg 182 < c.nreg 101) :
    ∃ c' k', Exec I P.W bLevel c c' k' ∧ IBl P c₀ (t₀ + 1) c' ∧
      ∑ t ∈ Finset.Ico (t₀ + 1) P.Lv, levC P t + k' + 2 ≤
        ∑ t ∈ Finset.Ico t₀ P.Lv, levC P t := by
  obtain ⟨hc, hG, hX, hDa, h182, h181, h284, h285, htle, hkN, hkR, hO, hdone, hlow, hrmE,
    hbhe⟩ := hI
  rw [h182, hG.r101] at hlt
  have ht := hlt
  have hLv := lt_Lv' ht
  have hw := hL.wx
  have hw0 := lay_w hL
  have hbw := bh_le_W hL
  have hLvb : P.Lv * P.b < 2 ^ P.TB := by have := lt_two_pow_TB P; rw [Nat.mul_comm]; exact this
  have hl8 : 8 * P.b * P.Lv * (t₀ + 1) ≤ 8 * P.b * P.Lv * P.Lv := Nat.mul_le_mul_left _ hLv
  have hl32 : 32 * P.b * (t₀ + 1) ≤ 32 * P.b * P.Lv := Nat.mul_le_mul_left _ hLv
  have hlvb : (t₀ + 1) * P.b ≤ P.Lv * P.b := Nat.mul_le_mul_right _ hLv
  have h8e : 8 * P.b * P.Lv * (t₀ + 1) = 8 * P.b * P.Lv * t₀ + 8 * P.b * P.Lv := by ring
  have h32e : 32 * P.b * (t₀ + 1) = 32 * P.b * t₀ + 32 * P.b := by ring
  have hbe' : (t₀ + 1) * P.b = t₀ * P.b + P.b := by ring
  have hbhq : P.bh = P.tb + 32 * P.b * P.Lv := rfl
  have hbr : P.bh + 16 * 2 ^ P.TB = P.rb := rfl
  rw [Finset.sum_eq_sum_Ico_succ_bot (show t₀ < P.Lv by omega)]
  unfold bLevel
  refine spec_seq ?_
  exec_block
  · omega
  · omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have fK : ∀ r, r ≠ 183 → r ≠ 192 → c₁.nreg r = c.nreg r := fun r h1 h2 => by
    rw [← hc₁]; config_simp; upd_tac
  have hI₁ : IBk P c₀ t₀ 0 c₁ := ⟨hw₁, hG.of fun r h1 h2 => fK r (by omega) (by omega),
    hX.of fun r h1 h2 => fK r (by omega) (by omega),
    hDa.of hL (fun a _ => by rw [← hc₁]) (fun a _ => by rw [← hc₁]),
    by rw [fK 182 (by omega) (by omega)]; exact h182,
    by rw [fK 181 (by omega) (by omega)]; exact h181,
    by rw [fK 284 (by omega) (by omega)]; exact h284,
    by rw [fK 285 (by omega) (by omega)]; exact h285,
    by rw [← hc₁]; config_simp, by rw [← hc₁]; config_simp; simp,
    fun r hr => by rw [fK r (by omega) (by omega)]; exact hkN r hr,
    fun r hr => by rw [← hc₁]; exact hkR r hr, by rw [← hc₁]; exact hO,
    fun t k' ht' hk' h => by
      rw [← hc₁]; exact hdone t k' ht' hk' (h.elim id fun ⟨_, h⟩ => by omega),
    fun a ha => by rw [← hc₁]; exact hlow a ha, by rw [← hc₁]; exact hrmE,
    by rw [← hc₁]; exact hbhe⟩
  obtain ⟨k₁, c₂, k₂, e₂, hI₂, hn₂, hk₂⟩ := Exec.whileLtN_ghost (P := I) (W := P.W) (a := 192)
    (b := 101) (body := .seq bInit (block [.addN 183 183 110, .mulN 192 183 182]))
    (IBk P c₀ t₀) (fun k _ => (P.b / 2 ^ t₀ + 1 - k) * (bInitC t₀ + 4)) (fun _ _ h => h.wb)
    (fun k c hI hlt => by
      obtain ⟨c', k', e, h1, h2⟩ := bkBody_exec hL hDc ht c hI hlt
      exact ⟨k + 1, c', k', e, h1, h2⟩) hI₁
  refine spec_seq ⟨c₂, k₂, e₂, ?_⟩
  have hw₂ := hI₂.wb
  have hG₂ := hI₂.glob
  have hX₂ := hI₂.gx
  rw [hI₂.r192, hG₂.r101] at hn₂
  exec_block
  · rw [hI₂.r182]; omega
  · config_simp; rw [hI₂.r181, hX₂.r247]; omega
  · config_simp; rw [hI₂.r284, hX₂.r244]; omega
  · config_simp; rw [hI₂.r285, hG₂.r101]; omega
  refine ⟨⟨‹_›, hG₂.of fun r h1 h2 => by config_simp; upd_tac,
    hX₂.of fun r h1 h2 => by config_simp; upd_tac,
    hI₂.data.of hL (fun _ _ => rfl) (fun _ _ => rfl), ?_, ?_, ?_, ?_, by omega,
    fun r hr => ?_, fun r hr => by config_simp; exact hI₂.keepR r hr, by config_simp; exact hI₂.out,
    fun t k' ht' hk' h => ?_, fun a ha => by config_simp; exact hI₂.lowN a ha,
    by config_simp; exact hI₂.rmE, by config_simp; exact hI₂.bhe⟩, ?_⟩
  · config_simp; rw [hI₂.r182, pow_succ]; ring
  · config_simp; rw [hI₂.r181, hX₂.r247]; ring
  · config_simp; rw [hI₂.r284, hX₂.r244]; ring
  · config_simp; rw [hI₂.r285, hG₂.r101]; ring
  · config_simp; rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
      upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact hI₂.keepN r hr
  · config_simp
    rcases Nat.lt_or_ge t t₀ with h' | h'
    · exact hI₂.done t k' ht' hk' (Or.inl h')
    · obtain rfl : t = t₀ := by omega
      exact hI₂.done t k' ht' hk' (Or.inr ⟨rfl, by
        by_contra hc
        have : k₁ * 2 ^ t ≤ k' * 2 ^ t := Nat.mul_le_mul_right _ (by omega)
        omega⟩)
  · config_simp
    unfold levC
    rw [Nat.sub_zero] at hk₂
    generalize (P.b / 2 ^ t₀ + 1) * (bInitC t₀ + 4) = Z at *
    omega

/-- **All the half blocks are initialized.** -/
theorem bLevels_exec (hL : Lay P) (hDc : Crossing P.b P.D) (c : Config) (hc : WordsBounded P.W c)
    (hG : Glob P c) (hX : GX P c) (hDa : Data P c) (hB : BHE P c.nmem c.rmem) :
    ∃ c' k', Exec I P.W bLevels c c' k' ∧ k' ≤ ∑ t ∈ Finset.range P.Lv, levC P t + 6 ∧
      (Glob P c' ∧ GX P c' ∧ Data P c' ∧ (∀ r < 100, c'.nreg r = c.nreg r) ∧
        (∀ r < 100, c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
        (∀ t k, 2 ^ t < P.b → k * 2 ^ t < P.b → InitB P c'.nmem c'.rmem t k) ∧
        (∀ a < P.tb, c'.nmem a = c.nmem a) ∧ c'.rmem = c.rmem ∧ BHE P c'.nmem c'.rmem) := by
  have hb := hL.b_pos
  unfold bLevels
  refine spec_seq ?_
  exec_block
  · omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have fK : ∀ r, r ≠ 181 → r ≠ 182 → r ≠ 284 → r ≠ 285 → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 h4 => by rw [← hc₁]; config_simp; upd_tac
  have hI₁ : IBl P c 0 c₁ := ⟨hw₁, hG.of fun r h1 h2 => fK r (by omega) (by omega) (by omega)
      (by omega), hX.of fun r h1 h2 => fK r (by omega) (by omega) (by omega) (by omega),
    hDa.of hL (fun a _ => by rw [← hc₁]) (fun a _ => by rw [← hc₁]),
    by rw [← hc₁]; config_simp; rw [hG.r110]; rfl, by rw [← hc₁]; config_simp; rw [hX.r246]; ring,
    by rw [← hc₁]; config_simp; rw [hX.r240]; ring, by rw [← hc₁]; config_simp; ring,
    Nat.zero_le _, fun r hr => fK r (by omega) (by omega) (by omega) (by omega),
    fun r hr => by rw [← hc₁], by rw [← hc₁], fun t k ht hk h => by omega,
    fun a _ => by rw [← hc₁], by rw [← hc₁], by rw [← hc₁]; exact hB⟩
  obtain ⟨t₁, c₂, k₂, e₂, hI₂, hn₂, hk₂⟩ := whileLtN_ghost_pot (P' := I) (W := P.W) (a := 182)
    (b := 101) (body := bLevel) (IBl P c) (fun t _ => ∑ t' ∈ Finset.Ico t P.Lv, levC P t')
    (fun _ _ h => h.wb)
    (fun t c' hI hlt => by
      obtain ⟨c'', k', e, h1, h2⟩ := bLevel_exec hL hDc c' hI hlt
      exact ⟨t + 1, c'', k', e, h1, by omega⟩) hI₁
  refine ⟨c₂, k₂, e₂, ?_⟩
  rw [hI₂.r182, hI₂.glob.r101] at hn₂
  refine ⟨?_, hI₂.glob, hI₂.gx, hI₂.data, hI₂.keepN, hI₂.keepR, hI₂.out,
    fun t k ht hk => hI₂.done t k ht hk ?_, hI₂.lowN, hI₂.rmE, hI₂.bhe⟩
  · simp only [Finset.range_eq_Ico]; omega
  · by_contra h
    exact hn₂ (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega)) ht)

end FR

end Monge

end PlanarFlow
