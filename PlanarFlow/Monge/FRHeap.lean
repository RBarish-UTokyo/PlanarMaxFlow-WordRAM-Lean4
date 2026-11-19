module

public import PlanarFlow.Monge.FRExec

/-!
# FR-Dijkstra on the machine: the heap of the vertices

The heap of the vertices is a tournament tree of winners (`PlanarFlow.Monge.FR.WinOK`) over the
present flags `prV` (natural memory at `wb + x`) and the keys `keyV` (real memory at `wb + x`),
the winners `wnV` at `wb + N + i`.

* `hpFix_exec`: recomputing the winner of a node, within `22` steps;
* `hpUp_exec`: recomputing the path to the root, within `25 lg i + 2` steps;
* `decKey_exec`: decreasing the key of a vertex not settled, within `25 lg N + 40` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace FR

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Heap

/-- The present flags. -/
def prV (P : Prm) (nm : ℕ → ℕ) (x : ℕ) : ℕ := nm (P.wb + x)
/-- The keys. -/
def keyV (P : Prm) (rm : ℕ → ℝ) (x : ℕ) : ℝ := rm (P.wb + x)
/-- The winners. -/
def wnV (P : Prm) (nm : ℕ → ℕ) (i : ℕ) : ℕ := nm (P.wb + P.N + i)

variable {P : Prm} {I : Input}

/-- **Recomputing the winner of the node `r170`.** -/
theorem hpFix_exec (hL : Lay P) (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c)
    (hi1 : 1 ≤ c.nreg 170) (hi2 : c.nreg 170 < P.N)
    (hWa : wnV P c.nmem (2 * c.nreg 170) < P.N) (hWb : wnV P c.nmem (2 * c.nreg 170 + 1) < P.N)
    (hpr : ∀ x < P.N, prV P c.nmem x ≤ 1) :
    ∃ c' k', Exec I P.W hpFix c c' k' ∧ k' ≤ 22 ∧
      (c'.nmem = upd c.nmem (P.wb + P.N + c.nreg 170)
          (better (prV P c.nmem) (keyV P c.rmem) (wnV P c.nmem (2 * c.nreg 170))
            (wnV P c.nmem (2 * c.nreg 170 + 1))) ∧
        c'.rmem = c.rmem ∧ (∀ r, (r < 171 ∨ 175 ≤ r) → c'.nreg r = c.nreg r) ∧
        (∀ r, (r < 170 ∨ 172 ≤ r) → c'.rreg r = c.rreg r) ∧ c'.output = c.output) := by
  have hw := hL.w
  have := hL.m6
  have g109 := hG.r109
  have g110 := hG.r110
  have g111 := hG.r111
  have g114 := hG.r114
  generalize hi : c.nreg 170 = i at hi1 hi2 hWa hWb
  generalize ha : wnV P c.nmem (2 * i) = a at hWa
  generalize hb : wnV P c.nmem (2 * i + 1) = bb at hWb
  have a0 : a < P.N := hWa
  have b0 : bb < P.N := hWb
  have ea : c.nmem (c.nreg 170 * c.nreg 111 + c.nreg 114) = a := by
    rw [hi, g111, g114, ← ha]; unfold wnV; congr 1; ring
  have eb : c.nmem (c.nreg 170 * c.nreg 111 + c.nreg 114 + c.nreg 110) = bb := by
    rw [hi, g111, g114, g110, ← hb]; unfold wnV; congr 1; ring
  have hpa := hpr a a0
  have hpb := hpr bb b0
  -- the final store, from the winner `w` in `r174`
  have fin : ∀ (w : ℕ) (c' : Config), WordsBounded P.W c' → c'.nreg 174 = w →
      w = better (prV P c.nmem) (keyV P c.rmem) a bb →
      (∀ r, (r < 171 ∨ 175 ≤ r) → c'.nreg r = c.nreg r) →
      (∀ r, (r < 170 ∨ 172 ≤ r) → c'.rreg r = c.rreg r) → c'.nmem = c.nmem →
      c'.rmem = c.rmem → c'.output = c.output →
      ∃ c'' k', Exec I P.W (block [.addN 173 114 170, .storeN 173 174]) c' c'' k' ∧
        k' = 2 ∧ (c''.nmem = upd c.nmem (P.wb + P.N + i)
          (better (prV P c.nmem) (keyV P c.rmem) a bb) ∧
        c''.rmem = c.rmem ∧ (∀ r, (r < 171 ∨ 175 ≤ r) → c''.nreg r = c.nreg r) ∧
        (∀ r, (r < 170 ∨ 172 ≤ r) → c''.rreg r = c.rreg r) ∧ c''.output = c.output) := by
    intro w c' hw' h174 hwb hK hR hN hM hO
    have h114 : c'.nreg 114 = P.wb + P.N := (hK 114 (by omega)).trans g114
    have h170 : c'.nreg 170 = i := (hK 170 (by omega)).trans hi
    exec_block
    · rw [h114, h170]; omega
    refine ⟨rfl, ?_, by config_simp; exact hM, fun r hr => ?_, hR, hO⟩
    · config_simp; rw [h114, h170, h174, hN, hwb]
    · config_simp; rw [upd_other _ _ _ (by omega)]; exact hK r hr
  unfold hpFix
  refine spec_seq ?_
  exec_block
  · rw [hi, g111]; omega
  · config_simp; rw [hi, g111, g114]; omega
  · config_simp; rw [hi, g111, g114, g110]; omega
  · config_simp; rw [ea, g109]; omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have f171 : c₁.nreg 171 = a := by rw [← hc₁]; config_simp; exact ea
  have f172 : c₁.nreg 172 = bb := by rw [← hc₁]; config_simp; exact eb
  have f174 : c₁.nreg 174 = prV P c.nmem a := by
    rw [← hc₁]; config_simp; rw [ea, g109]; rfl
  have fK : ∀ r, (r < 171 ∨ 175 ≤ r) → c₁.nreg r = c.nreg r := fun r hr => by
    rw [← hc₁]; config_simp; upd_tac
  have fN : c₁.nmem = c.nmem := by rw [← hc₁]
  have fM : c₁.rmem = c.rmem := by rw [← hc₁]
  have fR : c₁.rreg = c.rreg := by rw [← hc₁]
  have fO : c₁.output = c.output := by rw [← hc₁]
  have k110 : c₁.nreg 110 = 1 := (fK 110 (by omega)).trans g110
  have k109 : c₁.nreg 109 = P.wb := (fK 109 (by omega)).trans g109
  refine spec_seq ?_
  by_cases hA : prV P c.nmem a < 1
  · refine spec_ifLtN_true (by rw [f174, k110]; exact hA) ?_
    refine spec_instr (Exec.copyN hw₁ 174 172) fun hw₂ => ?_
    obtain ⟨c'', k', e', hk', post⟩ := fin bb _ hw₂ (by config_simp; exact f172)
      (by rw [better_eq_right (by omega)])
      (fun r hr => by
        config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact fK r hr)
      (fun r hr => by config_simp; rw [fR]) (by config_simp; exact fN) (by config_simp; exact fM)
      (by config_simp; exact fO)
    exact ⟨c'', k', e', by omega, post⟩
  · refine spec_ifLtN_false (by rw [f174, k110]; exact hA) ?_
    refine spec_seq ?_
    exec_block
    · rw [k109, f172]; omega
    generalize hc₂ : (Config.mk _ _ _ _ _ _ : Config) = c₂
    have hw₂ : WordsBounded P.W c₂ := hc₂ ▸ ‹_›
    have g174 : c₂.nreg 174 = prV P c.nmem bb := by
      rw [← hc₂]; config_simp; rw [k109, f172, fN]; rfl
    have gK : ∀ r, (r < 171 ∨ 175 ≤ r) → c₂.nreg r = c.nreg r := fun r hr => by
      rw [← hc₂]; config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact fK r hr
    have g171 : c₂.nreg 171 = a := by rw [← hc₂]; config_simp; exact f171
    have g172 : c₂.nreg 172 = bb := by rw [← hc₂]; config_simp; exact f172
    have gN : c₂.nmem = c.nmem := by rw [← hc₂]; config_simp; exact fN
    have gM : c₂.rmem = c.rmem := by rw [← hc₂]; config_simp; exact fM
    have gR : c₂.rreg = c.rreg := by rw [← hc₂]; config_simp; exact fR
    have gO : c₂.output = c.output := by rw [← hc₂]; config_simp; exact fO
    have l110 : c₂.nreg 110 = 1 := (gK 110 (by omega)).trans g110
    have l109 : c₂.nreg 109 = P.wb := (gK 109 (by omega)).trans g109
    by_cases hB : prV P c.nmem bb < 1
    · refine spec_ifLtN_true (by rw [g174, l110]; exact hB) ?_
      refine spec_instr (Exec.copyN hw₂ 174 171) fun hw₃ => ?_
      obtain ⟨c'', k', e', hk', post⟩ := fin a _ hw₃ (by config_simp; exact g171)
        (by rw [better_eq_left ⟨by omega, Or.inl (by omega)⟩])
        (fun r hr => by
          config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact gK r hr)
        (fun r hr => by config_simp; rw [gR]) (by config_simp; exact gN) (by config_simp; exact gM)
        (by config_simp; exact gO)
      exact ⟨c'', k', e', by omega, post⟩
    · refine spec_ifLtN_false (by rw [g174, l110]; exact hB) ?_
      refine spec_seq ?_
      exec_block
      · rw [l109, g171]; omega
      · config_simp; rw [l109, g172]; omega
      generalize hc₃ : (Config.mk _ _ _ _ _ _ : Config) = c₃
      have hw₃ : WordsBounded P.W c₃ := hc₃ ▸ ‹_›
      have r170 : c₃.rreg 170 = keyV P c.rmem a := by
        rw [← hc₃]; config_simp; rw [l109, g171, gM]; rfl
      have r171 : c₃.rreg 171 = keyV P c.rmem bb := by
        rw [← hc₃]; config_simp; rw [l109, g172, gM]; rfl
      have hK3 : ∀ r, (r < 171 ∨ 175 ≤ r) → c₃.nreg r = c.nreg r := fun r hr => by
        rw [← hc₃]; config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact gK r hr
      have hR3 : ∀ r, (r < 170 ∨ 172 ≤ r) → c₃.rreg r = c.rreg r := fun r hr => by
        rw [← hc₃]; config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rw [gR]
      have h3a : c₃.nreg 171 = a := by rw [← hc₃]; config_simp; exact g171
      have h3b : c₃.nreg 172 = bb := by rw [← hc₃]; config_simp; exact g172
      have hN3 : c₃.nmem = c.nmem := by rw [← hc₃]; config_simp; exact gN
      have hM3 : c₃.rmem = c.rmem := by rw [← hc₃]; config_simp; exact gM
      have hO3 : c₃.output = c.output := by rw [← hc₃]; config_simp; exact gO
      have hpa1 : prV P c.nmem a = 1 := by omega
      have hpb1 : prV P c.nmem bb = 1 := by omega
      by_cases hC : keyV P c.rmem a < keyV P c.rmem bb
      · refine spec_ifLtR_true (by rw [r170, r171]; exact hC) ?_
        refine spec_instr (Exec.copyN hw₃ 174 171) fun hw₄ => ?_
        obtain ⟨c'', k', e', hk', post⟩ := fin a _ hw₄ (by config_simp; exact h3a)
          (by rw [better_eq_left ⟨hpa1, Or.inr hC⟩])
          (fun r hr => by
            config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hK3 r hr)
          (fun r hr => by config_simp; exact hR3 r hr) (by config_simp; exact hN3)
          (by config_simp; exact hM3) (by config_simp; exact hO3)
        exact ⟨c'', k', e', by omega, post⟩
      · refine spec_ifLtR_false (by rw [r170, r171]; exact hC) ?_
        refine spec_instr (Exec.copyN hw₃ 174 172) fun hw₄ => ?_
        obtain ⟨c'', k', e', hk', post⟩ := fin bb _ hw₄ (by config_simp; exact h3b)
          (by rw [better_eq_right (by rintro ⟨-, h | h⟩ <;> [omega; exact hC h])])
          (fun r hr => by
            config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hK3 r hr)
          (fun r hr => by config_simp; exact hR3 r hr) (by config_simp; exact hN3)
          (by config_simp; exact hM3) (by config_simp; exact hO3)
        exact ⟨c'', k', e', by omega, post⟩

lemma better_congr {pr pr' : ℕ → ℕ} {key key' : ℕ → ℝ} {a b : ℕ} (h1 : pr' a = pr a)
    (h2 : pr' b = pr b) (h3 : key' a = key a) (h4 : key' b = key b) :
    better pr' key' a b = better pr key a b := by
  unfold better; rw [h1, h2, h3, h4]

lemma WinOK.congr {n : ℕ} {pr pr' : ℕ → ℕ} {key key' : ℕ → ℝ} {wn : ℕ → ℕ} {J : ℕ}
    (h : WinOK n pr key wn J) (hp : ∀ x < n, pr' x = pr x) (hk : ∀ x < n, key' x = key x) :
    WinOK n pr' key' wn J := by
  refine ⟨h.leaf, h.under, fun i h1 h2 hA => ?_⟩
  rw [h.eq i h1 h2 hA]
  have a := (h.under (2 * i) (by omega) (by omega)).1
  have b := (h.under (2 * i + 1) (by omega) (by omega)).1
  exact (better_congr (hp _ a) (hp _ b) (hk _ a) (hk _ b)).symm

lemma WinOK.congr_wn {n : ℕ} {pr : ℕ → ℕ} {key : ℕ → ℝ} {wn wn' : ℕ → ℕ} {J : ℕ}
    (h : WinOK n pr key wn J) (hw : ∀ i, 1 ≤ i → i < 2 * n → wn' i = wn i) :
    WinOK n pr key wn' J := by
  refine ⟨fun x hx => by rw [hw _ (by omega) (by omega)]; exact h.leaf x hx,
    fun i h1 h2 => by rw [hw i h1 h2]; exact h.under i h1 h2, fun i h1 h2 hA => ?_⟩
  rw [hw i h1 (by omega), hw (2 * i) (by omega) (by omega), hw (2 * i + 1) (by omega) (by omega)]
  exact h.eq i h1 h2 hA

/-- The state of `hpUp`. -/
structure IHp (P : Prm) (c₀ c : Config) : Prop where
  wb : WordsBounded P.W c
  glob : Glob P c
  keepN : ∀ r, (r < 170 ∨ 175 ≤ r) → c.nreg r = c₀.nreg r
  keepR : ∀ r, (r < 170 ∨ 172 ≤ r) → c.rreg r = c₀.rreg r
  out : c.output = c₀.output
  nm : ∀ a, (a < P.wb + P.N + 1 ∨ P.wb + 2 * P.N ≤ a) → c.nmem a = c₀.nmem a
  rm : c.rmem = c₀.rmem
  lt : c.nreg 170 < P.N
  win : WinOK P.N (prV P c₀.nmem) (keyV P c₀.rmem) (wnV P c.nmem) (c.nreg 170)

lemma prV_congr {nm nm' : ℕ → ℕ} (h : ∀ a, (a < P.wb + P.N + 1 ∨ P.wb + 2 * P.N ≤ a) → nm' a = nm a)
    {x : ℕ} (hx : x < P.N) : prV P nm' x = prV P nm x := h _ (by omega)

theorem hpBody_exec (hL : Lay P) {c₀ : Config} (hpr : ∀ x < P.N, prV P c₀.nmem x ≤ 1) (c : Config)
    (hI : IHp P c₀ c) (hlt : c.nreg 117 < c.nreg 170) :
    ∃ c' k', Exec I P.W (.seq hpFix (.instr (.divN 170 170 111))) c c' k' ∧ IHp P c₀ c' ∧
      lg (c'.nreg 170) * 25 + k' + 2 ≤ lg (c.nreg 170) * 25 := by
  have hc := hI.wb
  have hG := hI.glob
  rw [hG.r117] at hlt
  have hlt' := hI.lt
  have hpr' : ∀ x < P.N, prV P c.nmem x ≤ 1 := fun x hx => by
    rw [prV_congr hI.nm hx]; exact hpr x hx
  have hW : WinOK P.N (prV P c.nmem) (keyV P c.rmem) (wnV P c.nmem) (c.nreg 170) :=
    hI.win.congr (fun x hx => prV_congr hI.nm hx) (fun x hx => by unfold keyV; rw [hI.rm])
  refine spec_seq ?_
  refine spec_use (hpFix_exec (I := I) hL c hc hG (by omega) hlt'
    (hW.under _ (by omega) (by omega)).1 (hW.under _ (by omega) (by omega)).1 hpr') ?_
  intro c₁ k₁ hk₁ hw₁ ⟨hN₁, hM₁, hK₁, hR₁, hO₁⟩
  refine spec_instr (Exec.divN hw₁ 170 170 111) fun hw₂ => ?_
  have g170 : c₁.nreg 170 = c.nreg 170 := hK₁ 170 (by omega)
  have g111 : c₁.nreg 111 = 2 := (hK₁ 111 (by omega)).trans hG.r111
  refine ⟨⟨hw₂,
    hG.of fun r h1 h2 => by config_simp; rw [upd_other _ _ _ (by omega)]; exact hK₁ r (by omega),
    fun r hr => by
      config_simp; rw [upd_other _ _ _ (by omega), hK₁ r (by omega)]; exact hI.keepN r hr,
    fun r hr => by config_simp; rw [hR₁ r hr]; exact hI.keepR r hr,
    by config_simp; rw [hO₁, hI.out],
    fun a ha => by config_simp; rw [hN₁, upd_other _ _ _ (by omega)]; exact hI.nm a ha,
    by config_simp; rw [hM₁, hI.rm], by config_simp; rw [g170, g111]; omega, ?_⟩, ?_⟩
  · config_simp; rw [g170, g111]
    have hst := hI.win.step (by omega) hlt'
    refine (hst.congr_wn fun i h1 h2 => ?_)
    unfold wnV; rw [hN₁]
    by_cases hie : i = c.nreg 170
    · subst hie; rw [upd_same, Function.update_self]
      have hkey : keyV P c.rmem = keyV P c₀.rmem := by funext x; unfold keyV; rw [hI.rm]
      rw [hkey]
      exact better_congr (prV_congr hI.nm (hW.under _ (by omega) (by omega)).1)
        (prV_congr hI.nm (hW.under _ (by omega) (by omega)).1) rfl rfl
    · rw [upd_other _ _ _ (by omega), Function.update_of_ne hie]
  · config_simp; rw [g170, g111]
    rw [lg_pos (show 1 ≤ c.nreg 170 by omega)]
    omega

/-- **Recomputing the winners from the node `r170` up to the root.** -/
theorem hpUp_exec (hL : Lay P) (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c)
    (hlt : c.nreg 170 < P.N) (hpr : ∀ x < P.N, prV P c.nmem x ≤ 1)
    (hW : WinOK P.N (prV P c.nmem) (keyV P c.rmem) (wnV P c.nmem) (c.nreg 170)) :
    ∃ c' k', Exec I P.W hpUp c c' k' ∧ k' ≤ lg (c.nreg 170) * 25 + 2 ∧
      (WinOK P.N (prV P c.nmem) (keyV P c.rmem) (wnV P c'.nmem) 0 ∧
        (∀ r, (r < 170 ∨ 175 ≤ r) → c'.nreg r = c.nreg r) ∧
        (∀ r, (r < 170 ∨ 172 ≤ r) → c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
        (∀ a, (a < P.wb + P.N + 1 ∨ P.wb + 2 * P.N ≤ a) → c'.nmem a = c.nmem a) ∧
        c'.rmem = c.rmem) := by
  obtain ⟨c', k', e, hI, hn, hk⟩ := Exec.whileLtN_potential (P := I) (W := P.W) (a := 117)
    (b := 170) (body := .seq hpFix (.instr (.divN 170 170 111))) (IHp P c)
    (fun c => lg (c.nreg 170) * 25) (fun _ h => h.wb)
    (fun c' hI hlt => hpBody_exec hL hpr c' hI hlt)
    ⟨hc, hG, fun _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, rfl, hlt, hW⟩
  have h0 : c'.nreg 170 = 0 := by rw [hI.glob.r117] at hn; omega
  have := hI.win; rw [h0] at this
  exact ⟨c', k', e, hk, this, hI.keepN, hI.keepR, hI.out, hI.nm, hI.rm⟩

/-- The cost of a decrease of a key. -/
def decCost (N : ℕ) : ℕ := lg N * 25 + 40

/-- The condition of a decrease of the key of `y` to `val`. -/
def DecDo (P : Prm) (nm : ℕ → ℕ) (rm : ℕ → ℝ) (y : ℕ) (val : ℝ) : Prop :=
  nm (P.sb + y) = 0 ∧ (prV P nm y = 0 ∨ val < keyV P rm y)

open Classical in
/-- **Decreasing the key** of the vertex `y = r175` to the real `rr175`, if it is not settled
and its key is absent or larger. -/
theorem decKey_exec (hL : Lay P) (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c)
    (hy : c.nreg 175 < P.N) (hpr : ∀ x < P.N, prV P c.nmem x ≤ 1)
    (hset : c.nmem (P.sb + c.nreg 175) ≤ 1)
    (hW : WinOK P.N (prV P c.nmem) (keyV P c.rmem) (wnV P c.nmem) 0) :
    ∃ c' k', Exec I P.W decKey c c' k' ∧ k' ≤ decCost P.N ∧
      ((∀ x < P.N, prV P c'.nmem x =
          if DecDo P c.nmem c.rmem (c.nreg 175) (c.rreg 175) ∧ x = c.nreg 175 then 1
          else prV P c.nmem x) ∧
        (∀ x < P.N, keyV P c'.rmem x =
          if DecDo P c.nmem c.rmem (c.nreg 175) (c.rreg 175) ∧ x = c.nreg 175 then c.rreg 175
          else keyV P c.rmem x) ∧
        WinOK P.N (prV P c'.nmem) (keyV P c'.rmem) (wnV P c'.nmem) 0 ∧
        (∀ r, (r < 170 ∨ 178 ≤ r) → c'.nreg r = c.nreg r) ∧
        (∀ r, (r < 170 ∨ 177 ≤ r) → c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
        (∀ a, a ≠ P.wb + c.nreg 175 → (a < P.wb + P.N + 1 ∨ P.wb + 2 * P.N ≤ a) →
          c'.nmem a = c.nmem a) ∧
        (∀ a, a ≠ P.wb + c.nreg 175 → c'.rmem a = c.rmem a)) := by
  have hw := hL.w
  have := hL.m5; have := hL.m6; have := hL.bN
  have g107 := hG.r107
  have g109 := hG.r109
  have g110 := hG.r110
  have g117 := hG.r117
  generalize hy' : c.nreg 175 = y at hy hset ⊢
  generalize hv : c.rreg 175 = val
  -- the flag `r176`
  obtain ⟨c₂, k₂, e₂, hk₂, f176, fK, fR, fN, fM, fO⟩ : ∃ c₂ k₂, Exec I P.W (.seq
      (block [.addN 176 107 175, .loadN 177 176, .constN 176 0])
      (.ifLtN 177 110 (.seq (block [.addN 177 109 175, .loadN 177 177])
        (.ifLtN 177 110 (.instr (.copyN 176 110)) (.seq (block [.addN 177 109 175, .loadR 176 177])
          (.ifLtR 175 176 (.instr (.copyN 176 110)) .skip)))) .skip)) c c₂ k₂ ∧ k₂ ≤ 15 ∧
      (c₂.nreg 176 = if DecDo P c.nmem c.rmem y val then 1 else 0) ∧
      (∀ r, r ≠ 176 → r ≠ 177 → c₂.nreg r = c.nreg r) ∧
      (∀ r, r ≠ 176 → c₂.rreg r = c.rreg r) ∧ c₂.nmem = c.nmem ∧ c₂.rmem = c.rmem ∧
      c₂.output = c.output := by
    refine spec_seq ?_
    exec_block
    · rw [g107, hy']; omega
    · omega
    generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
    have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
    have a177 : c₁.nreg 177 = c.nmem (P.sb + y) := by rw [← hc₁]; config_simp; rw [g107, hy']
    have a176 : c₁.nreg 176 = 0 := by rw [← hc₁]; config_simp
    have aK : ∀ r, r ≠ 176 → r ≠ 177 → c₁.nreg r = c.nreg r := fun r h1 h2 => by
      rw [← hc₁]; config_simp; upd_tac
    have aN : c₁.nmem = c.nmem := by rw [← hc₁]
    have aM : c₁.rmem = c.rmem := by rw [← hc₁]
    have aR : c₁.rreg = c.rreg := by rw [← hc₁]
    have aO : c₁.output = c.output := by rw [← hc₁]
    have k110 : c₁.nreg 110 = 1 := (aK 110 (by omega) (by omega)).trans g110
    have k109 : c₁.nreg 109 = P.wb := (aK 109 (by omega) (by omega)).trans g109
    have k175 : c₁.nreg 175 = y := (aK 175 (by omega) (by omega)).trans hy'
    by_cases hs : c.nmem (P.sb + y) < 1
    · refine spec_ifLtN_true (by rw [a177, k110]; exact hs) ?_
      refine spec_seq ?_
      exec_block
      · rw [k109, k175]; omega
      generalize hc₃ : (Config.mk _ _ _ _ _ _ : Config) = c₃
      have hw₃ : WordsBounded P.W c₃ := hc₃ ▸ ‹_›
      have b177 : c₃.nreg 177 = prV P c.nmem y := by
        rw [← hc₃]; config_simp; rw [k109, k175, aN]; rfl
      have bK : ∀ r, r ≠ 176 → r ≠ 177 → c₃.nreg r = c.nreg r := fun r h1 h2 => by
        rw [← hc₃]; config_simp; rw [upd_other _ _ _ h2]; exact aK r h1 h2
      have b176 : c₃.nreg 176 = 0 := by rw [← hc₃]; config_simp; exact a176
      have bN : c₃.nmem = c.nmem := by rw [← hc₃]; config_simp; exact aN
      have bM : c₃.rmem = c.rmem := by rw [← hc₃]; config_simp; exact aM
      have bR : c₃.rreg = c.rreg := by rw [← hc₃]; config_simp; exact aR
      have bO : c₃.output = c.output := by rw [← hc₃]; config_simp; exact aO
      have l110 : c₃.nreg 110 = 1 := (bK 110 (by omega) (by omega)).trans g110
      by_cases hp : prV P c.nmem y < 1
      · refine spec_ifLtN_true (by rw [b177, l110]; exact hp) ?_
        refine spec_instr (Exec.copyN hw₃ 176 110) fun _ => ⟨by omega, ?_, fun r h1 h2 => ?_,
          fun r h => by config_simp; rw [bR], by config_simp; exact bN, by config_simp; exact bM,
          by config_simp; exact bO⟩
        · config_simp; rw [l110]
          simp only [show DecDo P c.nmem c.rmem y val from ⟨by omega, Or.inl (by omega)⟩,
            ↓reduceIte]
        · config_simp; rw [upd_other _ _ _ h1]; exact bK r h1 h2
      · refine spec_ifLtN_false (by rw [b177, l110]; exact hp) ?_
        refine spec_seq ?_
        exec_block
        · rw [bK 109 (by omega) (by omega), g109, bK 175 (by omega) (by omega), hy']; omega
        generalize hc₄ : (Config.mk _ _ _ _ _ _ : Config) = c₄
        have hw₄ : WordsBounded P.W c₄ := hc₄ ▸ ‹_›
        have d176 : c₄.rreg 176 = keyV P c.rmem y := by
          rw [← hc₄]; config_simp; rw [bK 109 (by omega) (by omega), g109,
            bK 175 (by omega) (by omega), hy', bM]; rfl
        have d175 : c₄.rreg 175 = val := by rw [← hc₄]; config_simp; rw [bR, hv]
        have dK : ∀ r, r ≠ 176 → r ≠ 177 → c₄.nreg r = c.nreg r := fun r h1 h2 => by
          rw [← hc₄]; config_simp; rw [upd_other _ _ _ h2]; exact bK r h1 h2
        have d176n : c₄.nreg 176 = 0 := by rw [← hc₄]; config_simp; exact b176
        have dN : c₄.nmem = c.nmem := by rw [← hc₄]; config_simp; exact bN
        have dM : c₄.rmem = c.rmem := by rw [← hc₄]; config_simp; exact bM
        have dR : ∀ r, r ≠ 176 → c₄.rreg r = c.rreg r := fun r h => by
          rw [← hc₄]; config_simp; rw [upd_other _ _ _ h, bR]
        have dO : c₄.output = c.output := by rw [← hc₄]; config_simp; exact bO
        have m110 : c₄.nreg 110 = 1 := (dK 110 (by omega) (by omega)).trans g110
        by_cases hk : val < keyV P c.rmem y
        · refine spec_ifLtR_true (by rw [d175, d176]; exact hk) ?_
          refine spec_instr (Exec.copyN hw₄ 176 110) fun _ => ⟨by omega, ?_, fun r h1 h2 => ?_,
            fun r h => by config_simp; exact dR r h, by config_simp; exact dN,
            by config_simp; exact dM, by config_simp; exact dO⟩
          · config_simp; rw [m110]
            simp only [show DecDo P c.nmem c.rmem y val from ⟨by omega, Or.inr hk⟩, ↓reduceIte]
          · config_simp; rw [upd_other _ _ _ h1]; exact dK r h1 h2
        · refine spec_ifLtR_false (by rw [d175, d176]; exact hk) ?_
          refine spec_skip hw₄ ⟨by omega, ?_, dK, dR, dN, dM, dO⟩
          have : ¬ DecDo P c.nmem c.rmem y val := by
            rintro ⟨-, h | h⟩
            · omega
            · exact hk h
          rw [d176n]; simp only [this, ↓reduceIte]
    · refine spec_ifLtN_false (by rw [a177, k110]; exact hs) ?_
      refine spec_skip hw₁ ⟨by omega, ?_, aK, fun r _ => by rw [aR], aN, aM, aO⟩
      have : ¬ DecDo P c.nmem c.rmem y val := by rintro ⟨h, -⟩; omega
      rw [a176]; simp only [this, ↓reduceIte]
  have hw₂ := e₂.wb_right
  -- the last part
  obtain ⟨c', k₃, e₃, hk₃, post⟩ : ∃ c' k₃, Exec I P.W (.ifLtN 117 176
      (.seq (block [.addN 177 109 175, .storeN 177 110, .storeR 177 175, .addN 170 100 175,
        .divN 170 170 111]) hpUp) .skip) c₂ c' k₃ ∧ k₃ ≤ lg P.N * 25 + 10 ∧
      ((∀ x < P.N, prV P c'.nmem x =
          if DecDo P c.nmem c.rmem y val ∧ x = y then 1 else prV P c.nmem x) ∧
        (∀ x < P.N, keyV P c'.rmem x =
          if DecDo P c.nmem c.rmem y val ∧ x = y then val else keyV P c.rmem x) ∧
        WinOK P.N (prV P c'.nmem) (keyV P c'.rmem) (wnV P c'.nmem) 0 ∧
        (∀ r, (r < 170 ∨ 178 ≤ r) → c'.nreg r = c.nreg r) ∧
        (∀ r, (r < 170 ∨ 177 ≤ r) → c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
        (∀ a, a ≠ P.wb + y → (a < P.wb + P.N + 1 ∨ P.wb + 2 * P.N ≤ a) →
          c'.nmem a = c.nmem a) ∧
        (∀ a, a ≠ P.wb + y → c'.rmem a = c.rmem a)) := by
    have k117 : c₂.nreg 117 = 0 := (fK 117 (by omega) (by omega)).trans g117
    by_cases hd : DecDo P c.nmem c.rmem y val
    · simp only [hd, ↓reduceIte] at f176
      refine spec_ifLtN_true (by rw [k117, f176]; omega) ?_
      refine spec_seq ?_
      have k109 : c₂.nreg 109 = P.wb := (fK 109 (by omega) (by omega)).trans g109
      have k175 : c₂.nreg 175 = y := (fK 175 (by omega) (by omega)).trans hy'
      have k100 : c₂.nreg 100 = P.N := (fK 100 (by omega) (by omega)).trans hG.r100
      have k110 : c₂.nreg 110 = 1 := (fK 110 (by omega) (by omega)).trans g110
      have r175 : c₂.rreg 175 = val := (fR 175 (by omega)).trans hv
      exec_block
      · rw [k109, k175]; omega
      · config_simp; rw [k100, k175]; omega
      generalize hc₃ : (Config.mk _ _ _ _ _ _ : Config) = c₃
      have hw₃ : WordsBounded P.W c₃ := hc₃ ▸ ‹_›
      have hN3 : ∀ a, c₃.nmem a = if a = P.wb + y then 1 else c.nmem a := fun a => by
        rw [← hc₃]; config_simp; rw [k109, k175, k110, fN]; simp only [upd_apply]
      have hM3 : ∀ a, c₃.rmem a = if a = P.wb + y then val else c.rmem a := fun a => by
        rw [← hc₃]; config_simp; rw [k109, k175, r175, fM]; simp only [upd_apply]
      have h170 : c₃.nreg 170 = (P.N + y) / 2 := by
        rw [← hc₃]; config_simp; rw [k100, k175, (fK 111 (by omega) (by omega)).trans hG.r111]
      have hK3 : ∀ r, (r < 170 ∨ 178 ≤ r) → c₃.nreg r = c.nreg r := fun r hr => by
        rw [← hc₃]; config_simp; simp only [upd_apply]
        split_ifs <;> first | omega | exact fK r (by omega) (by omega)
      have hR3 : ∀ r, (r < 170 ∨ 177 ≤ r) → c₃.rreg r = c.rreg r := fun r hr => by
        rw [← hc₃]; config_simp; exact fR r (by omega)
      have hO3 : c₃.output = c.output := by rw [← hc₃]; config_simp; exact fO
      have hG3 : Glob P c₃ := hG.of fun r h1 h2 => hK3 r (by omega)
      have hprE : ∀ x < P.N, prV P c₃.nmem x = if x = y then 1 else prV P c.nmem x := fun x hx => by
        unfold prV; rw [hN3]; split_ifs <;> first | rfl | omega
      have hkeyE : ∀ x < P.N, keyV P c₃.rmem x = if x = y then val else keyV P c.rmem x :=
        fun x hx => by unfold keyV; rw [hM3]; split_ifs <;> first | rfl | omega
      have hwnE : ∀ i, 1 ≤ i → i < 2 * P.N → wnV P c₃.nmem i = wnV P c.nmem i := fun i h1 h2 => by
        unfold wnV; rw [hN3]; simp only [show ¬ (P.wb + P.N + i = P.wb + y) by omega, ↓reduceIte]
      have hset : WinOK P.N (prV P c₃.nmem) (keyV P c₃.rmem) (wnV P c₃.nmem) ((P.N + y) / 2) := by
        refine (WinOK.set (pr' := fun x => if x = y then 1 else prV P c.nmem x)
          (key' := fun x => if x = y then val else keyV P c.rmem x) hW (x := y)
          (fun z hz => by simp [hz]) (fun z hz => by simp [hz])).congr (fun x hx => hprE x hx)
          (fun x hx => hkeyE x hx)
          |>.congr_wn hwnE
      refine spec_use (hpUp_exec (I := I) hL c₃ hw₃ hG3 (by rw [h170]; omega)
        (fun x hx => by rw [hprE x hx]; split_ifs <;> [omega; exact hpr x hx])
        (by rw [h170]; exact hset)) ?_
      intro c₄ k₄ hk₄ hw₄ ⟨hW₄, hK₄, hR₄, hO₄, hN₄, hM₄⟩
      have hpr4 : ∀ x < P.N, prV P c₄.nmem x = prV P c₃.nmem x := fun x hx => hN₄ _ (by omega)
      refine ⟨?_, fun x hx => ?_, fun x hx => ?_, hW₄.congr (fun x hx => hpr4 x hx)
        (fun x hx => by unfold keyV; rw [hM₄]), fun r hr => ?_, fun r hr => ?_, by rw [hO₄, hO3],
        fun a h1 h2 => ?_, fun a h1 => ?_⟩
      · rw [h170] at hk₄
        have : lg ((P.N + y) / 2) ≤ lg P.N := lg_mono (by omega)
        omega
      · rw [hpr4 x hx, hprE x hx]; simp only [hd, true_and]
      · unfold keyV at *; rw [hM₄]; rw [hkeyE x hx]; simp only [hd, true_and]
      · rw [hK₄ r (by omega)]; exact hK3 r hr
      · rw [hR₄ r (by omega)]; exact hR3 r hr
      · rw [hN₄ a h2, hN3]; simp [h1]
      · rw [hM₄, hM3]; simp [h1]
    · simp only [hd, ↓reduceIte] at f176
      refine spec_ifLtN_false (by rw [k117, f176]; omega) ?_
      refine spec_skip hw₂ ⟨by omega, fun x hx => ?_, fun x hx => ?_, ?_, fun r hr => ?_,
        fun r hr => fR r (by omega), fO, fun a _ _ => by rw [fN], fun a _ => by rw [fM]⟩
      · simp only [hd, false_and, ↓reduceIte]; unfold prV; rw [fN]
      · simp only [hd, false_and, ↓reduceIte]; unfold keyV; rw [fM]
      · have e1 : prV P c₂.nmem = prV P c.nmem := by funext x; unfold prV; rw [fN]
        have e2 : keyV P c₂.rmem = keyV P c.rmem := by funext x; unfold keyV; rw [fM]
        have e3 : wnV P c₂.nmem = wnV P c.nmem := by funext x; unfold wnV; rw [fN]
        rw [e1, e2, e3]; exact hW
      · exact fK r (by omega) (by omega)
  unfold decKey
  cases e₂ with
  | seq ea eb =>
    exact ⟨c', _, .seq ea (.seq eb e₃), by unfold decCost; omega, post⟩

end FR

end Monge

end PlanarFlow
