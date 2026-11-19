module

public import PlanarFlow.Spec
public import WordRAM
public import PlanarFlow.Dijkstra.Heap

/-!
# Dijkstra's algorithm on the machine: the input, the program, the heap routines

The input is `[n, m, s, INF, off 0, …, off n, dst 0, len 0, …, dst (m-1), len (m-1)]`: a digraph on
the vertices `0 … n-1` with `m` arcs grouped by their tail (the arcs leaving `u` are
`off u ≤ j < off (u + 1)`), each with a head `dst j` and a nonnegative length `len j`, a source
`s`, and a word `INF` standing for an infinite distance.

The program keeps tentative distances `dist v` (at address `v`), done marks (at `n + v`) and a
tournament tree `t` (`PlanarFlow.Heap`) at `2n + i`, `1 ≤ i < 2n`, whose leaf `n + v` holds
`dist v` for the vertices not yet done and `INF` for the others. Each round reads the minimum at
the root, follows it down to its leaf (`desc`), marks the vertex done, removes it from the tree
and relaxes its arcs; a decreased distance is written to its leaf and the path to the root is
recomputed (`upd`). Each heap operation costs `O(log n)`.

Memory: `dist` at `0 … n-1`, done marks at `n … 2n-1`, the tree at `2n + 1 … 4n - 1`.
Registers: `r1 = 1`, `r2 = n`, `r3 = INF`, `r4 = 2n`, `r5 = n + 5`, `r6 = 2`, `r7 = 4`, `r8 = s`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Dijk

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset Heap

/-! ### The input -/

lemma word_inp (d : List ℕ) (i : ℕ) : (inp d).data.getD i 0 = word d i := rfl

/-! ### The program -/

/-- Constants. -/
def setup : Stmt := block [.constN 1 1, .readIn 2 0, .constN 6 2, .constN 9 3, .readIn 3 9,
  .readIn 8 6, .addN 4 2 2, .constN 7 4, .addN 5 2 7, .addN 5 5 1, .copyN 40 0]

/-- One distance set to `INF`. -/
def distStep : Stmt := block [.storeN 40 3, .addN 40 40 1]

/-- One tree node set to `INF`. -/
def treeStep : Stmt := block [.addN 41 4 40, .storeN 41 3, .addN 40 40 1]

/-- One step of the recomputation of the path from `r40` to the root. -/
def updBody : Stmt :=
  .seq (block [.mulN 41 40 6, .addN 42 4 41, .loadN 43 42, .addN 42 42 1, .loadN 44 42,
      .addN 45 4 40])
    (.seq (.ifLtN 44 43 (.instr (.storeN 45 44)) (.instr (.storeN 45 43)))
      (.instr (.divN 40 40 6)))

/-- Recompute the path from `r40` to the root. -/
def updS : Stmt := .whileLtN 0 40 updBody

/-- One step down from `r46` towards the smaller child. -/
def descBody : Stmt :=
  .seq (block [.mulN 41 46 6, .addN 42 4 41, .loadN 43 42, .addN 42 42 1, .loadN 44 42])
    (.ifLtN 44 43 (block [.mulN 46 46 6, .addN 46 46 1]) (.instr (.mulN 46 46 6)))

/-- Follow the minimum from the root down to a leaf `r46`. -/
def desc : Stmt := .seq (.instr (.copyN 46 1)) (.whileLtN 46 2 descBody)

/-- Relax the arc `r50` of the vertex being processed, of key `r47`. -/
def relax : Stmt :=
  .seq (block [.mulN 48 50 6, .addN 48 48 5, .readIn 52 48, .addN 48 48 1, .readIn 53 48,
      .addN 53 53 47, .loadN 54 52])
    (.seq (.ifLtN 53 54 (.seq (block [.storeN 52 53, .addN 40 2 52, .addN 48 4 40, .storeN 48 53,
        .divN 40 40 6]) updS) .skip)
      (.instr (.addN 50 50 1)))

/-- One round: extract the vertex of least key and relax its arcs. -/
def round : Stmt :=
  .seq desc <| .seq (block [.subN 49 46 2, .addN 48 2 49, .storeN 48 1, .addN 48 4 46,
    .storeN 48 3, .divN 40 46 6]) <| .seq updS <|
  .seq (block [.addN 48 49 7, .readIn 50 48, .addN 48 48 1, .readIn 51 48]) <|
  .seq (.whileLtN 50 51 relax) (block [.addN 48 4 1, .loadN 47 48])

/-- Print `dist r55`. -/
def outStep : Stmt := block [.loadN 56 55, .outN 56, .addN 55 55 1]

/-- **Dijkstra's algorithm.** -/
def prog : Stmt :=
  .seq setup <| .seq (.whileLtN 40 2 distStep) <| .seq (.instr (.constN 40 1)) <|
  .seq (.whileLtN 40 4 treeStep) <|
  .seq (block [.storeN 8 0, .addN 40 2 8, .addN 41 4 40, .storeN 41 0, .divN 40 40 6]) <|
  .seq updS <| .seq (block [.addN 48 4 1, .loadN 47 48]) <| .seq (.whileLtN 47 3 round) <|
  .seq (.instr (.copyN 55 0)) (.whileLtN 55 2 outStep)

/-! ### Registers and memory -/

/-- The constant registers. -/
def Regs (d : List ℕ) (c : Config) : Prop :=
  c.nreg 0 = 0 ∧ c.nreg 1 = 1 ∧ c.nreg 2 = nn d ∧ c.nreg 3 = inf d ∧ c.nreg 4 = 2 * nn d ∧
    c.nreg 5 = nn d + 5 ∧ c.nreg 6 = 2 ∧ c.nreg 7 = 4 ∧ c.nreg 8 = src d

/-- The registers below `lo` and from `hi` on are unchanged. -/
def KeepR (lo hi : ℕ) (c c' : Config) : Prop := ∀ r, (r < lo ∨ hi ≤ r) → c'.nreg r = c.nreg r

theorem regs_of {d : List ℕ} {c c' : Config} (hR : Regs d c) (h : ∀ r < 10, c'.nreg r = c.nreg r) :
    Regs d c' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hR
  exact ⟨(h 0 (by omega)).trans h0, (h 1 (by omega)).trans h1, (h 2 (by omega)).trans h2,
    (h 3 (by omega)).trans h3, (h 4 (by omega)).trans h4, (h 5 (by omega)).trans h5,
    (h 6 (by omega)).trans h6, (h 7 (by omega)).trans h7, (h 8 (by omega)).trans h8⟩

/-- The tree, on the memory `m`. -/
def tv (d : List ℕ) (m : ℕ → ℕ) (i : ℕ) : ℕ := m (2 * nn d + i)

/-! ### The heap routines -/

variable {d : List ℕ} {W : ℕ}

/-- The state of `upd`, started from `c₀`. -/
structure IU (d : List ℕ) (W : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  keep : KeepR 40 46 c₀ c
  out : c.output = c₀.output
  r40 : c.nreg 40 < nn d
  exc : IsTourExc (nn d) (tv d c.nmem) (c.nreg 40)
  frame : ∀ a, (a < 2 * nn d + 1 ∨ 3 * nn d ≤ a) → c.nmem a = c₀.nmem a

theorem updBody_exec (he : DEnc d W) {c₀ : Config} (hR : Regs d c₀) (c : Config) (hI : IU d W c₀ c)
    (hlt : c.nreg 0 < c.nreg 40) :
    ∃ c' k, Exec (inp d) W updBody c c' k ∧ IU d W c₀ c' ∧ lg (c'.nreg 40) * 13 + k + 2 ≤
      lg (c.nreg 40) * 13 := by
  have hc := hI.wb
  have hs := he.size
  have hR' := regs_of hR fun r hr => hI.keep r (Or.inl (by omega))
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hR'
  rw [h0] at hlt
  have hj := hI.r40
  unfold updBody
  refine spec_seq ?_
  exec_block
  · config_simp; rw [h6]; omega
  · config_simp; rw [h6, h4]; omega
  · config_simp; rw [h6, h4, h1]; omega
  · config_simp; rw [h4]; omega
  config_simp
  refine spec_seq ?_
  have hlg := lg_pos (show 1 ≤ c.nreg 40 by omega)
  have hmin : ∀ x : ℕ, x = min (tv d c.nmem (2 * c.nreg 40)) (tv d c.nmem (2 * c.nreg 40 + 1)) →
      ∀ c' : Config, WordsBounded W c' → KeepR 40 46 c c' → c'.output = c.output →
      c'.nreg 40 = c.nreg 40 / 2 →
      c'.nmem = upd c.nmem (2 * nn d + c.nreg 40) x → IU d W c₀ c' := by
    intro x hx c' hw hK ho h40 hm
    refine ⟨hw, fun r hr => (hK r hr).trans (hI.keep r hr), ho.trans hI.out, by omega, ?_,
      fun a ha => ?_⟩
    · rw [h40]
      refine isTourExc_step hI.exc (by omega) hj (fun a ha => ?_) ?_
      · simp only [tv, hm]; rw [upd_other _ _ _ (by omega)]
      · simp only [tv, hm, upd_same]; exact hx
    · rw [hm, upd_other _ _ _ (by omega)]; exact hI.frame a ha
  by_cases hcmp : c.nmem (c.nreg 4 + c.nreg 40 * c.nreg 6 + c.nreg 1) <
      c.nmem (c.nreg 4 + c.nreg 40 * c.nreg 6)
  · refine spec_ifLtN_true (by config_simp; exact hcmp) ?_
    refine spec_instr (Exec.storeN ‹_› _ _) fun hw => ?_
    refine spec_instr (Exec.divN hw _ _ _) fun hw' => ?_
    have hcmp' : tv d c.nmem (2 * c.nreg 40 + 1) < tv d c.nmem (2 * c.nreg 40) := by
      simp only [tv]; rw [h4, h6, h1] at hcmp; convert hcmp using 2 <;> ring
    refine ⟨hmin (c.nmem (c.nreg 4 + c.nreg 40 * c.nreg 6 + c.nreg 1)) ?_ _ hw' (fun r hr => ?_)
      (by config_simp) (by config_simp; rw [h6]) (by config_simp; rw [h4]), ?_⟩
    · rw [min_eq_right hcmp'.le]; simp only [tv]; rw [h4, h6, h1]; congr 1; ring
    · config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega
    · config_simp; rw [h6, hlg]; have := lg_mono (Nat.div_le_self (c.nreg 40) 2); omega
  · refine spec_ifLtN_false (by config_simp; exact hcmp) ?_
    refine spec_instr (Exec.storeN ‹_› _ _) fun hw => ?_
    refine spec_instr (Exec.divN hw _ _ _) fun hw' => ?_
    have hcmp' : ¬ tv d c.nmem (2 * c.nreg 40 + 1) < tv d c.nmem (2 * c.nreg 40) := by
      simp only [tv]; rw [h4, h6, h1] at hcmp; convert hcmp using 3 <;> ring
    refine ⟨hmin (c.nmem (c.nreg 4 + c.nreg 40 * c.nreg 6)) ?_ _ hw' (fun r hr => ?_)
      (by config_simp) (by config_simp; rw [h6]) (by config_simp; rw [h4]), ?_⟩
    · rw [min_eq_left (not_lt.1 hcmp')]; simp only [tv]; rw [h4, h6]; congr 1; ring
    · config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega
    · config_simp; rw [h6, hlg]; omega

/-- **The recomputation of a path.** From `r40 = j < n` with the tournament property broken only
at the ancestors of `j`, `upd` restores it within `13 lg j + 2` steps, changing only the internal
nodes and the registers `r40 … r45`. -/
theorem upd_exec (he : DEnc d W) (c : Config) (hc : WordsBounded W c) (hR : Regs d c)
    (hj : c.nreg 40 < nn d) (hexc : IsTourExc (nn d) (tv d c.nmem) (c.nreg 40)) :
    ∃ c' k, Exec (inp d) W updS c c' k ∧ WordsBounded W c' ∧ KeepR 40 46 c c' ∧
      c'.output = c.output ∧ IsTour (nn d) (tv d c'.nmem) ∧
      (∀ a, (a < 2 * nn d + 1 ∨ 3 * nn d ≤ a) → c'.nmem a = c.nmem a) ∧
      k ≤ lg (c.nreg 40) * 13 + 2 := by
  obtain ⟨c', k, e, hI, hn, hk⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 0)
    (b := 40) (body := updBody) (IU d W c) (fun c => lg (c.nreg 40) * 13) (fun c h => h.wb)
    (fun c' hc' hlt => updBody_exec he hR c' hc' hlt)
    ⟨hc, fun _ _ => rfl, rfl, hj, hexc, fun _ _ => rfl⟩
  have h0 : c'.nreg 0 = 0 := (hI.keep 0 (Or.inl (by omega))).trans hR.1
  have h40 : c'.nreg 40 = 0 := by rw [h0] at hn; omega
  have := hI.exc
  rw [h40] at this
  exact ⟨c', k, e, hI.wb, hI.keep, hI.out, isTour_of_exc this, hI.frame, hk⟩

/-- The state of the descent. -/
structure IDs (d : List ℕ) (W : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  keep : ∀ r < 41, c.nreg r = c₀.nreg r
  keep46 : ∀ r, 47 ≤ r → c.nreg r = c₀.nreg r
  out : c.output = c₀.output
  mem : c.nmem = c₀.nmem
  r46 : 1 ≤ c.nreg 46 ∧ c.nreg 46 < 2 * nn d
  val : tv d c.nmem (c.nreg 46) = tv d c.nmem 1

theorem descBody_exec (he : DEnc d W) {c₀ : Config} (hR : Regs d c₀)
    (hT : IsTour (nn d) (tv d c₀.nmem)) (c : Config) (hI : IDs d W c₀ c)
    (hlt : c.nreg 46 < c.nreg 2) :
    ∃ c' k, Exec (inp d) W descBody c c' k ∧ IDs d W c₀ c' ∧
      (lg (2 * nn d) - lg (c'.nreg 46)) * 10 + k + 2 ≤ (lg (2 * nn d) - lg (c.nreg 46)) * 10 := by
  have hc := hI.wb
  have hs := he.size
  have hR' := regs_of hR fun r hr => hI.keep r (by omega)
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hR'
  rw [h2] at hlt
  have hi := hI.r46
  have hmin := hT (c.nreg 46) hi.1 hlt
  rw [← hI.mem] at hmin
  have hval := hI.val
  have hL : lg (2 * c.nreg 46 + 1) ≤ lg (2 * nn d) := lg_mono (by omega)
  have hL2 := lg_two_mul hi.1
  have hL3 := lg_two_mul_add_one (c.nreg 46)
  unfold descBody
  refine spec_seq ?_
  exec_block
  · config_simp; rw [h6]; omega
  · config_simp; rw [h6, h4]; omega
  · config_simp; rw [h6, h4, h1]; omega
  config_simp
  by_cases hcmp : c.nmem (c.nreg 4 + c.nreg 46 * c.nreg 6 + c.nreg 1) <
      c.nmem (c.nreg 4 + c.nreg 46 * c.nreg 6)
  · refine spec_ifLtN_true (by config_simp; exact hcmp) ?_
    exec_block
    · config_simp; rw [h6]; omega
    · config_simp; rw [h6, h1]; omega
    have hcmp' : tv d c.nmem (2 * c.nreg 46 + 1) < tv d c.nmem (2 * c.nreg 46) := by
      simp only [tv]; rw [h4, h6, h1] at hcmp; convert hcmp using 2 <;> ring
    refine ⟨⟨‹_›, fun r hr => ?_, fun r hr => ?_, by config_simp; exact hI.out,
      by config_simp; exact hI.mem, by config_simp; rw [h6, h1]; omega, ?_⟩, ?_⟩
    · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hI.keep r hr
    · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hI.keep46 r hr
    · config_simp; rw [h6, h1, ← hval, hmin, min_eq_right hcmp'.le]
      simp only [tv]; congr 1; ring
    · config_simp; rw [h6, h1, show c.nreg 46 * 2 + 1 = 2 * c.nreg 46 + 1 by ring, hL3]; omega
  · refine spec_ifLtN_false (by config_simp; exact hcmp) ?_
    refine spec_instr (Exec.mulN ‹_› _ _ _ (by config_simp; rw [h6]; omega)) fun hw => ?_
    have hcmp' : ¬ tv d c.nmem (2 * c.nreg 46 + 1) < tv d c.nmem (2 * c.nreg 46) := by
      simp only [tv]; rw [h4, h6, h1] at hcmp; convert hcmp using 3 <;> ring
    refine ⟨⟨hw, fun r hr => ?_, fun r hr => ?_, by config_simp; exact hI.out,
      by config_simp; exact hI.mem, by config_simp; rw [h6]; omega, ?_⟩, ?_⟩
    · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hI.keep r hr
    · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hI.keep46 r hr
    · config_simp; rw [h6, ← hval, hmin, min_eq_left (not_lt.1 hcmp')]
      simp only [tv]; congr 1; ring
    · config_simp; rw [h6, show c.nreg 46 * 2 = 2 * c.nreg 46 by ring, hL2]; omega

/-- **The descent.** Following the smaller child from the root reaches a leaf holding the
minimum, within `10 lg (2n) + 3` steps. -/
theorem desc_exec (he : DEnc d W) (c : Config) (hc : WordsBounded W c) (hR : Regs d c)
    (hT : IsTour (nn d) (tv d c.nmem)) :
    ∃ c' k, Exec (inp d) W desc c c' k ∧ WordsBounded W c' ∧ KeepR 41 47 c c' ∧
      c'.output = c.output ∧ c'.nmem = c.nmem ∧ nn d ≤ c'.nreg 46 ∧ c'.nreg 46 < 2 * nn d ∧
      tv d c.nmem (c'.nreg 46) = tv d c.nmem 1 ∧ k ≤ lg (2 * nn d) * 10 + 3 := by
  have hn := he.n_pos
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hR
  have e₁ := Exec.copyN (P := inp d) hc 46 1
  have hI : IDs d W c { c with nreg := upd c.nreg 46 (c.nreg 1) } := by
    refine ⟨e₁.wb_right, fun r hr => ?_, fun r hr => ?_, rfl, rfl, ?_, ?_⟩
    · config_simp; rw [upd_other _ _ _ (by omega)]
    · config_simp; rw [upd_other _ _ _ (by omega)]
    · config_simp; rw [h1]; omega
    · config_simp; rw [h1]
  obtain ⟨c', k, e, hI', hn', hk⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 46)
    (b := 2) (body := descBody) (IDs d W c)
    (fun c' => (lg (2 * nn d) - lg (c'.nreg 46)) * 10) (fun c h => h.wb)
    (fun c' hc' hlt => descBody_exec he ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ hT c' hc' hlt) hI
  have h2' : c'.nreg 2 = nn d := (hI'.keep 2 (by omega)).trans h2
  have hge : nn d ≤ c'.nreg 46 := by rw [h2'] at hn'; omega
  refine ⟨c', 1 + k, .seq e₁ e, hI'.wb, fun r hr => ?_, hI'.out, hI'.mem, hge, hI'.r46.2,
    by rw [← hI'.mem]; exact hI'.val, ?_⟩
  · rcases hr with hr | hr
    · exact hI'.keep r hr
    · exact hI'.keep46 r (by omega)
  · beta_reduce at hk; config_simp at hk; omega

end Dijk

end PlanarFlow
