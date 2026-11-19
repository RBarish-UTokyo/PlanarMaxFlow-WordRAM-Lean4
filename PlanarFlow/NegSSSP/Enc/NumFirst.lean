module

public import PlanarFlow.NegSSSP.Enc.BlScat
public import PlanarFlow.NegSSSP.LinNode

/-!
# Numbering values by first appearance (the vertex numbering of a node)

The node's encoding numbers the vertices of its piece `0, …, w − 1` (`ν`, with inverse `ι`) and
stores the numbers of the tails and heads of its darts (`encT`, `encH`). From an array `A` of
global identifiers (the tails, then the heads), `nmProg` numbers the identifiers by their first
appearance, with a scratch table `G` (all zero before and after: `G[g] = ν g + 1` while the
identifier `g` is numbered).

`nmProg` (registers `2875 … 2886`; `r2875 = n`, `r2876 = Ab`, `r2877 = Gb`, `r2878 = Ob`,
`r2879 = Ib`): for `i < n`, `g = A[i]`; if `G[g] = 0` then `w := w + 1`, `G[g] := w`,
`I[w − 1] := g`; then `O[i] := G[g] − 1`. Then `G[I[v]] := 0` for `v < w`.

**`nmProg_exec`**: within `25 n + 9` steps, for some `w ≤ n` (in `r2882`) and `ν : ℕ → ℕ`:
`O[i] = ν A[i]`, `ν A[i] < w`, `I[ν A[i]] = A[i]` (so `ν` is injective on the values of `A`),
every `v < w` is some `ν A[i]`, the table `G` zero again; memory outside `[Ob, Ob + n)` and
`[Ib, Ib + n)` kept; registers outside `2880 … 2886` kept; reals, output kept.

**`nm_nodeEnc`**: run on `A = [gid (tail (e d)) | d < m] ++ [gid (head (e d)) | d < m]` (`gid`
global vertex identifiers with a left inverse `gi`), the numbering is a node encoding
`NodeEnc N P₀ P₁ m w e (ν ∘ gid) (gi ∘ I)` and `O` holds `encT` then `encH`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- `g := A[i]`, `x := G[g]` (address of `G[g]` in `r2884`). -/
def nmL : Stmt := block [.addN 2884 2876 2880, .loadN 2883 2884, .addN 2884 2877 2883,
  .loadN 2885 2884]

/-- A new identifier: `w := w + 1`, `G[g] := w`, `I[w − 1] := g`, `x := w`. -/
def nmN : Stmt := block [.addN 2882 2882 2881, .storeN 2884 2882, .addN 2884 2879 2882,
  .subN 2884 2884 2881, .storeN 2884 2883, .copyN 2885 2882]

/-- `O[i] := x − 1`, `i := i + 1`. -/
def nmS : Stmt := block [.subN 2885 2885 2881, .addN 2884 2878 2880, .storeN 2884 2885,
  .addN 2880 2880 2881]

/-- One step of the numbering. -/
def nmBody : Stmt := .seq nmL (.seq (.ifLtN 2886 2885 .skip nmN) nmS)

/-- One step of the clean-up: `G[I[v]] := 0`. -/
def nmClean : Stmt := block [.addN 2884 2879 2880, .loadN 2883 2884, .addN 2884 2877 2883,
  .storeN 2884 2886, .addN 2880 2880 2881]

/-- **Numbering by first appearance** (see the module docstring). -/
def nmProg : Stmt :=
  .seq (block [.constN 2880 0, .constN 2881 1, .constN 2882 0, .constN 2886 0]) <|
  .seq (.whileLtN 2880 2875 nmBody) <|
  .seq (block [.constN 2880 0]) (.whileLtN 2880 2882 nmClean)

theorem nmProg_natOnly : Klein.natOnly nmProg = true := by kernel_rfl

/-- The memory after one step of the numbering. -/
def nmMem (mem : ℕ → ℕ) (Gb Ob Ib i w g x : ℕ) : ℕ → ℕ :=
  if 0 < x then upd mem (Ob + i) (x - 1)
  else upd (upd (upd mem (Gb + g) (w + 1)) (Ib + w) g) (Ob + i) w

theorem nmBody_exec (c : Config) (hc : WordsBounded W c) {Ab Gb Ob Ib i w : ℕ}
    (r76 : c.nreg 2876 = Ab) (r77 : c.nreg 2877 = Gb) (r78 : c.nreg 2878 = Ob)
    (r79 : c.nreg 2879 = Ib) (r80 : c.nreg 2880 = i) (r81 : c.nreg 2881 = 1)
    (r82 : c.nreg 2882 = w) (r86 : c.nreg 2886 = 0)
    (w1 : Ab + i ≤ W) (w2 : Gb + c.nmem (Ab + i) ≤ W) (w3 : Ib + w + 1 ≤ W) (w4 : Ob + i ≤ W)
    (w5 : i + 1 ≤ W) (w6 : w + 1 ≤ W) :
    ∃ c' k, Exec P W nmBody c c' k ∧ k ≤ 16 ∧
      c'.nmem = nmMem c.nmem Gb Ob Ib i w (c.nmem (Ab + i)) (c.nmem (Gb + c.nmem (Ab + i))) ∧
      c'.nreg 2880 = i + 1 ∧
      c'.nreg 2882 = (if 0 < c.nmem (Gb + c.nmem (Ab + i)) then w else w + 1) ∧
      (∀ r, (r < 2880 ∨ r = 2881 ∨ 2886 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold nmBody
  set g := c.nmem (Ab + i) with hg
  set x := c.nmem (Gb + g) with hx
  obtain ⟨c₁, k₁, e₁, hk₁, g83, g84, g85, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W nmL c c₁ k₁ ∧ k₁ = 4 ∧ c₁.nreg 2883 = g ∧ c₁.nreg 2884 = Gb + g ∧
      c₁.nreg 2885 = x ∧ (∀ r, r ≠ 2883 → r ≠ 2884 → r ≠ 2885 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold nmL
    exec_block
    all_goals try ((try config_simp); (try simp only [r76, r77, r80, ← hg]); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r76, r77, r80, ← hg, ← hx])
    simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ r, (r < 2883 ∨ 2885 < r) → c₁.nreg r = c.nreg r := fun r h =>
    gn₁ r (by omega) (by omega) (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, h82, h85, gn₂, gm₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
      Exec P W (.ifLtN 2886 2885 .skip nmN) c₁ c₂ k₂ ∧ k₂ ≤ 8 ∧
      c₂.nreg 2882 = (if 0 < x then w else w + 1) ∧
      c₂.nreg 2885 = (if 0 < x then x else w + 1) ∧
      (∀ r, (r < 2882 ∨ (2882 < r ∧ r < 2884) ∨ 2885 < r) → c₂.nreg r = c₁.nreg r) ∧
      c₂.nmem = (if 0 < x then c.nmem else upd (upd c.nmem (Gb + g) (w + 1)) (Ib + w) g) ∧
      c₂.rreg = c.rreg ∧ c₂.rmem = c.rmem ∧ c₂.output = c.output := by
    by_cases hx0 : 0 < x
    · have hlt : c₁.nreg 2886 < c₁.nreg 2885 := by rw [q 2886 (by omega), r86, g85]; exact hx0
      refine ⟨c₁, _, .ifLtN_true hlt (.skip hw₁), by omega, ?_, ?_, fun _ _ => rfl, ?_, gr₁,
        grm₁, go₁⟩
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hx0), q 2882 (by omega), r82]
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hx0), g85]
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hx0), gm₁]
    · have hlt : ¬ c₁.nreg 2886 < c₁.nreg 2885 := by
        rw [q 2886 (by omega), r86, g85]; exact hx0
      have q79 : c₁.nreg 2879 = Ib := by rw [q _ (by omega), r79]
      have q81 : c₁.nreg 2881 = 1 := by rw [q _ (by omega), r81]
      have q82 : c₁.nreg 2882 = w := by rw [q _ (by omega), r82]
      obtain ⟨c₃, k₃, e₃, hk₃, h82, h85, hn₃, hm₃, hr₃, hrm₃, ho₃⟩ : ∃ c₃ k₃,
          Exec P W nmN c₁ c₃ k₃ ∧ k₃ = 6 ∧ c₃.nreg 2882 = w + 1 ∧ c₃.nreg 2885 = w + 1 ∧
          (∀ r, (r < 2882 ∨ (2882 < r ∧ r < 2884) ∨ 2885 < r) → c₃.nreg r = c₁.nreg r) ∧
          c₃.nmem = upd (upd c.nmem (Gb + g) (w + 1)) (Ib + w) g ∧ c₃.rreg = c₁.rreg ∧
          c₃.rmem = c₁.rmem ∧ c₃.output = c₁.output := by
        unfold nmN
        exec_block
        all_goals try ((try config_simp); (try simp only [q79, q81, q82, g83, g84, gm₁]); omega)
        refine ⟨rfl, ?_, ?_, fun r hr => ?_, ?_, rfl, rfl, rfl⟩
        all_goals config_simp
        all_goals try (simp only [q79, q81, q82, g83, g84, gm₁])
        all_goals try (simp only [upd_apply]; split_ifs <;> omega)
        all_goals try (congr 1 <;> omega)
      refine ⟨c₃, _, .ifLtN_false hlt e₃, by omega, ?_, ?_, hn₃, ?_, by rw [hr₃, gr₁],
        by rw [hrm₃, grm₁], by rw [ho₃, go₁]⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hx0)]; exact h82
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hx0)]; exact h85
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hx0)]; exact hm₃
  have hw₂ := e₂.wb_right
  have q78 : c₂.nreg 2878 = Ob := by rw [gn₂ _ (by omega), q _ (by omega), r78]
  have q80 : c₂.nreg 2880 = i := by rw [gn₂ _ (by omega), q _ (by omega), r80]
  have q81 : c₂.nreg 2881 = 1 := by rw [gn₂ _ (by omega), q _ (by omega), r81]
  obtain ⟨c₃, k₃, e₃, hk₃, h80, hn₃, hm₃, hr₃, hrm₃, ho₃⟩ : ∃ c₃ k₃,
      Exec P W nmS c₂ c₃ k₃ ∧ k₃ = 4 ∧ c₃.nreg 2880 = i + 1 ∧
      (∀ r, r ≠ 2880 → r ≠ 2884 → r ≠ 2885 → c₃.nreg r = c₂.nreg r) ∧
      c₃.nmem = upd c₂.nmem (Ob + i) (c₂.nreg 2885 - 1) ∧ c₃.rreg = c₂.rreg ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    unfold nmS
    exec_block
    all_goals try ((try config_simp); (try simp only [q78, q80, q81]); omega)
    refine ⟨rfl, ?_, fun r h1 h2 h3 => ?_, ?_, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [q78, q80, q81])
    simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, ?_, h80, ?_, fun r hr => ?_,
    by rw [hr₃, gr₂], by rw [hrm₃, grm₂], by rw [ho₃, go₂]⟩
  · rw [hm₃, gm₂, h85]
    unfold nmMem
    by_cases hx0 : 0 < x
    · simp only [hx0, ↓reduceIte]
    · simp only [hx0, ↓reduceIte]
      congr 1
  · rw [hn₃ _ (by omega) (by omega) (by omega)]; exact h82
  · rw [hn₃ r (by omega) (by omega) (by omega), gn₂ r (by omega), q r (by omega)]

theorem nmClean_exec (c : Config) (hc : WordsBounded W c) {Gb Ib v : ℕ}
    (r77 : c.nreg 2877 = Gb) (r79 : c.nreg 2879 = Ib) (r80 : c.nreg 2880 = v)
    (r81 : c.nreg 2881 = 1) (r86 : c.nreg 2886 = 0)
    (w1 : Ib + v ≤ W) (w2 : Gb + c.nmem (Ib + v) ≤ W) (w5 : v + 1 ≤ W) :
    ∃ c' k, Exec P W nmClean c c' k ∧ k = 5 ∧
      c'.nmem = upd c.nmem (Gb + c.nmem (Ib + v)) 0 ∧ c'.nreg 2880 = v + 1 ∧
      (∀ r, (r < 2880 ∨ r = 2881 ∨ r = 2882 ∨ 2885 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold nmClean
  exec_block
  all_goals try ((try config_simp); (try simp only [r77, r79, r80, r81, r86]); omega)
  refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r77, r79, r80, r81, r86])
  simp only [upd_apply]; split_ifs <;> omega

/-- **Numbering by first appearance on the machine** (see the module docstring). -/
theorem nmProg_exec {n Ab Gb Ob Ib nG : ℕ} (c : Config) (hc : WordsBounded W c)
    (r75 : c.nreg 2875 = n) (r76 : c.nreg 2876 = Ab) (r77 : c.nreg 2877 = Gb)
    (r78 : c.nreg 2878 = Ob) (r79 : c.nreg 2879 = Ib) (h1 : n + 1 ≤ W)
    (wA : Ab + n ≤ W) (wG : Gb + nG ≤ W) (wO : Ob + n ≤ W) (wI : Ib + n ≤ W)
    (dAG : Ab + n ≤ Gb ∨ Gb + nG ≤ Ab) (dAO : Ab + n ≤ Ob ∨ Ob + n ≤ Ab)
    (dAI : Ab + n ≤ Ib ∨ Ib + n ≤ Ab) (dGO : Gb + nG ≤ Ob ∨ Ob + n ≤ Gb)
    (dGI : Gb + nG ≤ Ib ∨ Ib + n ≤ Gb) (dOI : Ob + n ≤ Ib ∨ Ib + n ≤ Ob)
    (hA : ∀ i < n, c.nmem (Ab + i) < nG) (hG : ∀ g < nG, c.nmem (Gb + g) = 0) :
    ∃ c' k, Exec P W nmProg c c' k ∧ k ≤ 25 * n + 9 ∧ ∃ (w : ℕ) (ν : ℕ → ℕ), w ≤ n ∧
      c'.nreg 2882 = w ∧
      (∀ i < n, c'.nmem (Ob + i) = ν (c.nmem (Ab + i))) ∧
      (∀ i < n, ν (c.nmem (Ab + i)) < w) ∧
      (∀ i < n, c'.nmem (Ib + ν (c.nmem (Ab + i))) = c.nmem (Ab + i)) ∧
      (∀ v < w, ∃ i < n, ν (c.nmem (Ab + i)) = v) ∧
      (∀ a, (a < Ob ∨ Ob + n ≤ a) → (a < Ib ∨ Ib + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2880 ∨ 2886 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold nmProg
  set A : ℕ → ℕ := fun i => c.nmem (Ab + i) with hAdef
  have hA' : ∀ i < n, A i < nG := hA
  obtain ⟨c₁, k₁, e₁, hk₁, g80, g81, g82, g86, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 2880 0, .constN 2881 1, .constN 2882 0, .constN 2886 0]) c c₁
        k₁ ∧ k₁ = 4 ∧ c₁.nreg 2880 = 0 ∧ c₁.nreg 2881 = 1 ∧ c₁.nreg 2882 = 0 ∧
      c₁.nreg 2886 = 0 ∧
      (∀ r, (r < 2880 ∨ (2882 < r ∧ r < 2886) ∨ 2886 < r) → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  -- the numbering
  let J : ℕ → Config → Prop := fun i c' => ∃ (w : ℕ) (ν : ℕ → ℕ), w ≤ i ∧
      c'.nreg 2882 = w ∧
      (∀ g < nG, c'.nmem (Gb + g) = if ∃ j < i, A j = g then ν g + 1 else 0) ∧
      (∀ j < i, c'.nmem (Ob + j) = ν (A j)) ∧
      (∀ j < i, ν (A j) < w) ∧
      (∀ j < i, c'.nmem (Ib + ν (A j)) = A j) ∧
      (∀ v < w, ∃ j < i, ν (A j) = v) ∧
      (∀ a, (a < Gb ∨ Gb + nG ≤ a) → (a < Ob ∨ Ob + i ≤ a) → (a < Ib ∨ Ib + w ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2880 ∨ 2886 < r) → c'.nreg r = c.nreg r) ∧
      c'.nreg 2881 = 1 ∧ c'.nreg 2886 = 0 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, hJ⟩ := forLoop_exec (P := P) (a := 2880) (bR := 2875)
    (body := nmBody) J (K := 16) (n := n) c₁ e₁.wb_right g80
    (by rw [gn₁ 2875 (by omega)]; exact r75)
    ⟨0, fun _ => 0, le_refl _, g82, fun g hg => by
        rw [gm₁, hG g hg, ite_eq_right_of_eq_false _ _ (eq_false (by rintro ⟨j, hj, -⟩; omega))],
      fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
      fun j hj => absurd hj (by omega), fun v hv => absurd hv (by omega),
      fun a _ _ _ => by rw [gm₁], fun r hr => gn₁ r (by omega), g81, g86, gr₁, grm₁, go₁⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨w, ν, hwi, j82, jG, jO, jlt, jI, jsurj, jm, jr, j81, j86, jrr, jrm, jo⟩ := hJ
      have eA : c'.nmem (Ab + i) = A i := jm _ (by omega) (by omega) (by omega)
      have hAi := hA' i hi
      obtain ⟨c'', k, ex, hk, hm, h80, h82, hn, hrr, hrm, ho⟩ := nmBody_exec (P := P)
        (Ab := Ab) (Gb := Gb) (Ob := Ob) (Ib := Ib) (i := i) (w := w) c' hw
        (by rw [jr _ (by omega)]; exact r76) (by rw [jr _ (by omega)]; exact r77)
        (by rw [jr _ (by omega)]; exact r78) (by rw [jr _ (by omega)]; exact r79) ha j81 j82
        j86 (by omega) (by rw [eA]; omega) (by omega) (by omega) (by omega) (by omega)
      rw [eA] at hm h82
      have eG := jG (A i) hAi
      refine ⟨c'', k, ex, hk, h80, by rw [hn _ (by omega)]; exact hb, ?_⟩
      by_cases hold : ∃ j < i, A j = A i
      · -- an identifier already numbered
        rw [ite_eq_left_of_eq_true _ _ (eq_true hold)] at eG
        have hx0 : 0 < c'.nmem (Gb + A i) := by rw [eG]; omega
        rw [ite_eq_left_of_eq_true _ _ (eq_true hx0)] at h82
        have hm' : c''.nmem = upd c'.nmem (Ob + i) (ν (A i)) := by
          rw [hm]; unfold nmMem; rw [ite_eq_left_of_eq_true _ _ (eq_true hx0), eG]; rfl
        obtain ⟨j₀, hj₀, ej₀⟩ := hold
        refine ⟨w, ν, by omega, h82, fun g hg => ?_, fun j hj => ?_, fun j hj => ?_,
          fun j hj => ?_, fun v hv => ?_, fun a h1 h2 h3 => ?_, fun r hr => ?_,
          by rw [hn _ (by omega)]; exact j81, by rw [hn _ (by omega)]; exact j86,
          by rw [hrr, jrr], by rw [hrm, jrm], by rw [ho, jo]⟩
        · rw [hm', upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), jG g hg]
          by_cases hg' : ∃ j < i, A j = g
          · rw [ite_eq_left_of_eq_true _ _ (eq_true hg'), ite_eq_left_of_eq_true _ _
              (eq_true (let ⟨j, h1, h2⟩ := hg'; ⟨j, by omega, h2⟩))]
          · rw [ite_eq_right_of_eq_false _ _ (eq_false hg')]
            by_cases hgi : A i = g
            · exact absurd ⟨j₀, hj₀, ej₀.trans hgi⟩ hg'
            · rw [ite_eq_right_of_eq_false _ _ (eq_false (by
                rintro ⟨j, hj, e⟩
                rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
                · exact hg' ⟨j, hj, e⟩
                · exact hgi e))]
        · rw [hm', upd_apply]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact jO j hj
          · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact jlt j hj
          · rw [← ej₀]; exact jlt j₀ hj₀
        · have hlt : ν (A j) < w := by
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
            · exact jlt j hj
            · rw [← ej₀]; exact jlt j₀ hj₀
          rw [hm', upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by
            rcases dOI with h | h <;> omega))]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact jI j hj
          · rw [← ej₀]; exact jI j₀ hj₀
        · obtain ⟨j, hj, e⟩ := jsurj v hv
          exact ⟨j, by omega, e⟩
        · rw [hm', upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
          exact jm a h1 (by omega) h3
        · rw [hn r (by omega)]; exact jr r hr
      · -- a new identifier
        rw [ite_eq_right_of_eq_false _ _ (eq_false hold)] at eG
        have hx0 : ¬ 0 < c'.nmem (Gb + A i) := by rw [eG]; omega
        rw [ite_eq_right_of_eq_false _ _ (eq_false hx0)] at h82
        have hm' : c''.nmem = upd (upd (upd c'.nmem (Gb + A i) (w + 1)) (Ib + w) (A i))
            (Ob + i) w := by
          rw [hm]; unfold nmMem; rw [ite_eq_right_of_eq_false _ _ (eq_false hx0)]
        set ν' : ℕ → ℕ := fun g => if g = A i then w else ν g with hν'
        have hν'o : ∀ j < i, ν' (A j) = ν (A j) := fun j hj => by
          rw [hν']; simp only
          rw [ite_eq_right_of_eq_false _ _ (eq_false (fun e => hold ⟨j, hj, e⟩))]
        have hν'i : ν' (A i) = w := by rw [hν']; simp
        have hIb : Ib + w + 1 ≤ Ib + n := by omega
        refine ⟨w + 1, ν', by omega, h82, fun g hg => ?_, fun j hj => ?_, fun j hj => ?_,
          fun j hj => ?_, fun v hv => ?_, fun a h1 h2 h3 => ?_, fun r hr => ?_,
          by rw [hn _ (by omega)]; exact j81, by rw [hn _ (by omega)]; exact j86,
          by rw [hrr, jrr], by rw [hrm, jrm], by rw [ho, jo]⟩
        · rw [hm', upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), upd_apply,
            ite_eq_right_of_eq_false _ _ (eq_false (by omega)), upd_apply]
          by_cases hgi : A i = g
          · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
              ite_eq_left_of_eq_true _ _ (eq_true ⟨i, by omega, hgi⟩), ← hgi, hν'i]
          · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), jG g hg]
            have hν'g : ν' g = ν g := by
              rw [hν']; simp only; rw [ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm hgi))]
            rw [hν'g]
            congr 1
            apply propext
            constructor
            · rintro ⟨j, hj, e⟩; exact ⟨j, by omega, e⟩
            · rintro ⟨j, hj, e⟩
              rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
              · exact ⟨j, hj, e⟩
              · exact absurd e hgi
        · rw [hm', upd_apply]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), upd_apply,
              ite_eq_right_of_eq_false _ _ (eq_false (by rcases dOI with h | h <;> omega)),
              upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by
                rcases dGO with h | h <;> omega)), jO j hj, hν'o j hj]
          · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), hν'i]
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · rw [hν'o j hj]; have := jlt j hj; omega
          · rw [hν'i]; omega
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · have := jlt j hj
            rw [hν'o j hj, hm', upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by
              rcases dOI with h | h <;> omega)), upd_apply,
              ite_eq_right_of_eq_false _ _ (eq_false (by omega)), upd_apply,
              ite_eq_right_of_eq_false _ _ (eq_false (by rcases dGI with h | h <;> omega))]
            exact jI j hj
          · rw [hν'i, hm', upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by
              rcases dOI with h | h <;> omega)), upd_apply,
              ite_eq_left_of_eq_true _ _ (eq_true rfl)]
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
          · obtain ⟨j, hj, e⟩ := jsurj v hv
            exact ⟨j, by omega, by rw [hν'o j hj]; exact e⟩
          · exact ⟨i, by omega, hν'i⟩
        · rw [hm', upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), upd_apply,
            ite_eq_right_of_eq_false _ _ (eq_false (by omega)), upd_apply,
            ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
          exact jm a h1 (by omega) (by omega)
        · rw [hn r (by omega)]; exact jr r hr)
  obtain ⟨w, ν, hwn, j82, jG, jO, jlt, jI, jsurj, jm, jr, j81, j86, jrr, jrm, jo⟩ := hJ
  -- the clean-up
  obtain ⟨c₃, k₃, e₃, hk₃, h80, hn₃, hm₃, hr₃, hrm₃, ho₃⟩ : ∃ c₃ k₃,
      Exec P W (block [.constN 2880 0]) c₂ c₃ k₃ ∧ k₃ = 1 ∧ c₃.nreg 2880 = 0 ∧
      (∀ r, r ≠ 2880 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hinj : ∀ j < n, ∀ j' < n, ν (A j) = ν (A j') → A j = A j' := fun j hj j' hj' e => by
    rw [← jI j hj, ← jI j' hj', e]
  let K : ℕ → Config → Prop := fun v c' =>
      (∀ g < nG, c'.nmem (Gb + g) = if (∃ j < n, A j = g) ∧ v ≤ ν g then ν g + 1 else 0) ∧
      (∀ a, (a < Gb ∨ Gb + nG ≤ a) → c'.nmem a = c₂.nmem a) ∧
      (∀ r, (r < 2880 ∨ r = 2881 ∨ r = 2882 ∨ 2885 < r) → c'.nreg r = c₂.nreg r) ∧
      c'.nreg 2881 = 1 ∧ c'.nreg 2886 = 0 ∧
      c'.rreg = c₂.rreg ∧ c'.rmem = c₂.rmem ∧ c'.output = c₂.output
  obtain ⟨c₄, k₄, e₄, hk₄, -, hK⟩ := forLoop_exec (P := P) (a := 2880) (bR := 2882)
    (body := nmClean) K (K := 5) (n := w) c₃ e₃.wb_right h80
    (by rw [hn₃ _ (by omega)]; exact j82)
    ⟨fun g hg => by
        rw [hm₃, jG g hg]
        congr 1; apply propext; exact ⟨fun h => ⟨h, by omega⟩, fun h => h.1⟩,
      fun a _ => by rw [hm₃], fun r hr => hn₃ r (by omega),
      by rw [hn₃ _ (by omega)]; exact j81, by rw [hn₃ _ (by omega)]; exact j86,
      hr₃, hrm₃, ho₃⟩
    (fun v c' hv hw ha hb hK => by
      obtain ⟨q1, q2, q3, q81, q86, qr, qrm, qo⟩ := hK
      obtain ⟨j, hj, ej⟩ := jsurj v hv
      have eI : c'.nmem (Ib + v) = A j := by
        rw [q2 _ (by rcases dGI with h | h <;> omega), ← ej]; exact jI j hj
      have hAj := hA' j hj
      obtain ⟨c'', k, ex, hk, hm, h80', hn, hrr, hrm, ho⟩ := nmClean_exec (P := P)
        (Gb := Gb) (Ib := Ib) (v := v) c' hw (by rw [q3 _ (by omega), jr _ (by omega)]; exact r77)
        (by rw [q3 _ (by omega), jr _ (by omega)]; exact r79) ha q81 q86 (by omega)
        (by rw [eI]; omega) (by omega)
      rw [eI] at hm
      refine ⟨c'', k, ex, by omega, h80', by rw [hn _ (by omega)]; exact hb, fun g hg => ?_,
        fun a ha' => ?_, fun r hr => by rw [hn r hr]; exact q3 r hr,
        by rw [hn _ (by omega)]; exact q81, by rw [hn _ (by omega)]; exact q86,
        by rw [hrr, qr], by rw [hrm, qrm], by rw [ho, qo]⟩
      · rw [hm, upd_apply, q1 g hg]
        by_cases hgj : g = A j
        · subst hgj
          rw [ite_eq_left_of_eq_true _ _ (eq_true rfl),
            ite_eq_right_of_eq_false _ _ (eq_false (by rintro ⟨-, h⟩; omega))]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
          congr 1; apply propext
          constructor
          · rintro ⟨⟨j', hj', e⟩, h⟩
            refine ⟨⟨j', hj', e⟩, ?_⟩
            rcases Nat.lt_or_ge v (ν g) with h' | h'
            · omega
            · have : ν g = v := by omega
              rw [← e] at this
              have e2 : A j' = A j := hinj j' hj' j hj (this.trans ej.symm)
              exact absurd (e.symm.trans e2) hgj
          · rintro ⟨h, h'⟩; exact ⟨h, by omega⟩
      · rw [hm, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact q2 a ha')
  obtain ⟨q1, q2, q3, -, -, qr, qrm, qo⟩ := hK
  refine ⟨c₄, k₁ + (k₂ + (k₃ + k₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), ?_, w, ν, hwn, ?_,
    fun i hi => ?_, jlt, fun i hi => ?_, jsurj, fun a h1 h2 => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · have : (5 + 2) * w ≤ 7 * n := by nlinarith
    omega
  · rw [q3 _ (by omega)]; exact j82
  · rw [q2 _ (by rcases dGO with h | h <;> omega)]; exact jO i hi
  · have : ν (c.nmem (Ab + i)) < w := jlt i hi
    rw [q2 _ (by rcases dGI with h | h <;> omega)]; exact jI i hi
  · by_cases hg : Gb ≤ a ∧ a < Gb + nG
    · obtain ⟨g, rfl⟩ : ∃ g, a = Gb + g := ⟨a - Gb, by omega⟩
      rw [q1 g (by omega), hG g (by omega),
        ite_eq_right_of_eq_false _ _ (eq_false (by
          rintro ⟨⟨j, hj, e⟩, h⟩
          have := jlt j hj
          rw [e] at this
          omega))]
    · rw [q2 a (by omega)]
      exact jm a (by omega) (by omega) (by omega)
  · rw [q3 r (by omega)]; exact jr r hr
  · rw [qr, jrr]
  · rw [qrm, jrm]
  · rw [qo, jo]

section Sem

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {N : CombMap D V F}

/-- **The numbering by first appearance is a node encoding** (see the module docstring). -/
theorem nm_nodeEnc {P₀ P₁ : Finset D} {m : ℕ} {e : ℕ → D} (hen : IsEnum m e (P₀ ∪ P₁))
    (hdisj : Disjoint P₀ P₁) (gid : V → ℕ) (gi : ℕ → V) (hgi : ∀ x, gi (gid x) = x)
    {mem mem' : ℕ → ℕ} {Ab Ob Ib w : ℕ} {ν : ℕ → ℕ}
    (hAT : ∀ d < m, mem (Ab + d) = gid (N.tail (e d)))
    (hAH : ∀ d < m, mem (Ab + m + d) = gid (N.head (e d))) (hw : w ≤ 2 * m)
    (hO : ∀ i < 2 * m, mem' (Ob + i) = ν (mem (Ab + i)))
    (hlt : ∀ i < 2 * m, ν (mem (Ab + i)) < w)
    (hI : ∀ i < 2 * m, mem' (Ib + ν (mem (Ab + i))) = mem (Ab + i)) :
    NodeEnc N P₀ P₁ m w e (fun x => ν (gid x)) (fun v => gi (mem' (Ib + v))) ∧
      (∀ d < m, mem' (Ob + d) = encT N e (fun x => ν (gid x)) d) ∧
      (∀ d < m, mem' (Ob + m + d) = encH N e (fun x => ν (gid x)) d) := by
  have hT : ∀ d < m, mem (Ab + d) = gid (N.tail (e d)) := hAT
  have hH : ∀ d < m, mem (Ab + (m + d)) = gid (N.head (e d)) := fun d hd => by
    rw [← Nat.add_assoc]; exact hAH d hd
  have key : ∀ x ∈ verts N (P₀ ∪ P₁), ∃ i < 2 * m, mem (Ab + i) = gid x := fun x hx => by
    obtain ⟨d, hd, h⟩ := mem_verts.1 hx
    obtain ⟨i, hi, rfl⟩ := hen.surj d hd
    rcases h with h | h
    · exact ⟨i, by omega, by rw [hT i hi, h]⟩
    · exact ⟨m + i, by omega, by rw [hH i hi, h]⟩
  refine ⟨⟨hen, hdisj, fun x hx => ?_, fun x hx => ?_, hw⟩, fun d hd => ?_, fun d hd => ?_⟩
  · obtain ⟨i, hi, e1⟩ := key x hx
    have := hlt i hi
    rwa [e1] at this
  · obtain ⟨i, hi, e1⟩ := key x hx
    have := hI i hi
    rw [e1] at this
    show gi (mem' (Ib + ν (gid x))) = x
    rw [this, hgi]
  · rw [hO d (by omega), hT d hd]; rfl
  · rw [Nat.add_assoc, hO (m + d) (by omega), hH d hd]; rfl

end Sem

end NegSSSP

end PlanarFlow
