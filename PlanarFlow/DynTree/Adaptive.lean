module

public import PlanarFlow.DynTree.RegVal
public import PlanarFlow.DynTree.Init

/-!
# Dynamic trees with evert: adaptive programs

A calculus for programs that call the register-operand blocks of
`PlanarFlow/DynTree/RegOps.lean` and `PlanarFlow/DynTree/RegVal.lean` with operands they compute,
branch on the results, and loop, without fixing the list of operations in advance.

**Amortised runs.** `LRun P W B n s c G c' F' G' m g`: the statement `s` runs from `c`, where the
structure stores some forest as the virtual forest `G`, to `c'`, where it stores `F'` as `G'`
(`LCTE`), at a cost `k` with `k + 16400 Φ(G') ≤ 16400 Φ(G) + m · opCostE n + g`;
`opCostE n = 311600 ⌊log₂ n⌋ + 42220` is the amortised cost of one operation of
`eopStmt_exec`, `m` counts the operations and `g` the further steps. `ORun` adds the list of
operations performed: `ORun … F os …` is `ValidOpsE n F os` and an `LRun` to
`(runOpsE n F os).1`.

* `LRun.seq`, `LRun.glue` (code that touches neither the structure nor `r151`; it may write the
  memory outside `B … B + 16 (n + 1) - 1`, by `LCTE.congr`), `LRun.ifLtN_true` and the other
  branches, `LRun.mono`; the same for `ORun`.
* `LRun.whileLtN`: **the loop rule.** A loop whose body, from any state of the invariant
  `I x F G c` with the test true, makes an amortised run counted `j` operations and `h` further
  steps, to a state of the invariant with `cnt x' = cnt x + j` and `ext x' + h + 2 ≤ ext x`,
  runs counted `cnt x' - cnt x` operations and `ext x + 2 - ext x'` further steps: the
  operations are summed over the iterations, however many each performs, and the further cost is
  paid by the potential `ext` (which also bounds the number of iterations).
  `ORun.whileLtN`: the same with the list of operations performed, the ghost forest following
  `runOpsE` from the forest at the start of the loop. `LRun.whileLtN_abs`, `ORun.whileLtN_abs`:
  the further steps of each iteration (at most `opCostE n - 2`) paid by its operations (at least
  one), the iterations bounded by a decreasing measure: the loop is counted twice the operations
  of its iterations and two further steps.
* `…_orun`: the register-operand blocks as `ORun`s (the forest-changing ones with their
  `EOp`, the queries with the empty list), each counted one operation (`regVal`: two).
* `lctE_adaptive_runsWithin`: **an adaptive program** `r151 := n; init; s`, where `s` from the
  initialised structure makes an amortised run counted at most `m` operations and `g` further
  steps and prints `out`, prints `out` within `400000 (n + m + 1) (⌊log₂ n⌋ + 1) + g` steps, as
  `lctE_runsWithin` for a fixed list.
-/

@[expose] public noncomputable section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs VT

/-! ### The structure under a change of the memory outside it -/

/-- **Frame lemma**: the structure survives any change of the memory outside the words
`B … B + 16 (n + 1) - 1` and of the registers other than `r151`. -/
theorem LCTE.congr {B n : ℕ} {F : Forest} {G : List VT} {c c' : Config} (hS : LCTE B n F G c)
    (hm : ∀ a, B ≤ a → a < B + 16 * (n + 1) → c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a)
    (h151 : c'.nreg 151 = c.nreg 151) : LCTE B n F G c' := by
  have hA : ∀ u ≤ n, Agr B (mem c) (mem c') u := fun u hu j hj =>
    hm _ (by simp only [adr]; omega) (by simp only [adr]; nlinarith)
  have hN : NilOK B n (mem c') := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hS.inv.nil
    have a := hA n le_rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact ((a 1 (by omega)).1).trans h1
    · exact ((a 2 (by omega)).1).trans h2
    · exact ((a 4 (by omega)).2).trans h3
    · exact ((a 3 (by omega)).2).trans h4
    · exact ((a 8 (by omega)).2).trans h5
  have hlt : ∀ u ∈ nodesL G, u < n := fun u hu => (hS.inv.cover u).mp hu
  have hV : ∀ u ∈ nodesL G, AgrV B (mem c) (mem c') u := fun u hu => by
    have a := hA u (hlt u hu).le
    exact ⟨(a 0 (by omega)).2, (a 1 (by omega)).2, (a 5 (by omega)).2, (a 6 (by omega)).2,
      by simp only [DynTree.rv, rvw]; rw [(a 10 (by omega)).1]⟩
  refine ⟨⟨fun T hT => ?_, hS.inv.nodup, hS.inv.cover, hN⟩, ⟨hS.rep.par, ?_, ?_⟩, ?_, ?_⟩
  · have hE := hS.inv.enc T hT
    have hTn : ∀ u ∈ nodes T, u < n := fun u hu => hlt u (mem_nodesL_of hT hu)
    refine hE.frame B n hS.inv.nil hN (hS.inv.nodup_of B n hT) n
      (fun u hu _ => hA u (hTn u hu).le) (fun hne => (hA _ (hTn _ (rt_mem_nodes hne n)).le).agrC)
      (fun hne => ?_)
    exact ((hA _ (hTn _ (rt_mem_nodes hne n)).le 0 (by omega)).1).trans (Enc.par_rt B n hE hne)
  · intro u w huw
    rw [dVL_frame B G hV false] at huw
    exact hS.rep.val u w huw
  · intro u w huw
    rw [dVL_frame B G hV true] at huw
    exact hS.rep.val2 u w huw
  · intro u hu j hj hj10
    rw [(hA u hu j hj).1]
    exact hS.bnd u hu j hj hj10
  · rw [h151]; exact hS.hn

/-! ### Amortised runs -/

/-- The amortised cost of one operation (`eopStmt_exec`). -/
def opCostE (n : ℕ) : ℕ := 311600 * Nat.log 2 n + 42220

/-- **An amortised run**: `s` runs from `c`, where the structure is stored as `G`, to `c'`,
where it stores `F'` as `G'`, at a cost `k` with
`k + 16400 Φ(G') ≤ 16400 Φ(G) + m · opCostE n + g`. -/
def LRun (P : Input) (W B n : ℕ) (s : Stmt) (c : Config) (G : List VT) (c' : Config)
    (F' : Forest) (G' : List VT) (m g : ℕ) : Prop :=
  ∃ k, Exec P W s c c' k ∧ LCTE B n F' G' c' ∧
    k + 16400 * potL G' ≤ 16400 * potL G + m * opCostE n + g

section
variable {P : Input} {W B n : ℕ}

lemma LRun.of_exec {s : Stmt} {c c' : Config} {G G' : List VT} {F' : Forest} {k K m g : ℕ}
    (e : Exec P W s c c' k) (hS : LCTE B n F' G' c')
    (hk : k + 16400 * potL G' ≤ 16400 * potL G + K) (hK : K ≤ m * opCostE n + g) :
    LRun P W B n s c G c' F' G' m g :=
  ⟨k, e, hS, by omega⟩

lemma LRun.mono {s : Stmt} {c c' : Config} {G G' : List VT} {F' : Forest} {m g m' g' : ℕ}
    (h : LRun P W B n s c G c' F' G' m g) (hm : m ≤ m') (hg : g ≤ g') :
    LRun P W B n s c G c' F' G' m' g' := by
  obtain ⟨k, e, hS, hk⟩ := h
  exact ⟨k, e, hS, by nlinarith [Nat.mul_le_mul_right (opCostE n) hm]⟩

lemma LRun.seq {s t : Stmt} {c c₁ c₂ : Config} {G G₁ G₂ : List VT} {F₁ F₂ : Forest}
    {m₁ g₁ m₂ g₂ : ℕ} (h₁ : LRun P W B n s c G c₁ F₁ G₁ m₁ g₁)
    (h₂ : LRun P W B n t c₁ G₁ c₂ F₂ G₂ m₂ g₂) :
    LRun P W B n (.seq s t) c G c₂ F₂ G₂ (m₁ + m₂) (g₁ + g₂) := by
  obtain ⟨k₁, e₁, -, hk₁⟩ := h₁
  obtain ⟨k₂, e₂, hS₂, hk₂⟩ := h₂
  exact ⟨k₁ + k₂, .seq e₁ e₂, hS₂, by rw [Nat.add_mul]; omega⟩

/-- **Glue code**: a statement that keeps the memory of the structure and `r151` (it may write
the registers and the memory outside the structure) is an amortised run of no operation. -/
lemma LRun.glue {s : Stmt} {c c' : Config} {F : Forest} {G : List VT} {k : ℕ}
    (e : Exec P W s c c' k) (hS : LCTE B n F G c)
    (hm : ∀ a, B ≤ a → a < B + 16 * (n + 1) → c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a)
    (h151 : c'.nreg 151 = c.nreg 151) : LRun P W B n s c G c' F G 0 k :=
  ⟨k, e, hS.congr hm h151, by omega⟩

lemma LRun.skip {c : Config} {F : Forest} {G : List VT} (hc : WordsBounded W c)
    (hS : LCTE B n F G c) : LRun P W B n .skip c G c F G 0 0 :=
  ⟨0, .skip hc, hS, by omega⟩

lemma LRun.ifLtN_true {a b : ℕ} {t e : Stmt} {c c' : Config} {G G' : List VT} {F' : Forest}
    {m g : ℕ} (ht : c.nreg a < c.nreg b) (h : LRun P W B n t c G c' F' G' m g) :
    LRun P W B n (.ifLtN a b t e) c G c' F' G' m (g + 1) := by
  obtain ⟨k, ex, hS, hk⟩ := h
  exact ⟨k + 1, .ifLtN_true ht ex, hS, by omega⟩

lemma LRun.ifLtN_false {a b : ℕ} {t e : Stmt} {c c' : Config} {G G' : List VT} {F' : Forest}
    {m g : ℕ} (ht : ¬ c.nreg a < c.nreg b) (h : LRun P W B n e c G c' F' G' m g) :
    LRun P W B n (.ifLtN a b t e) c G c' F' G' m (g + 2) := by
  obtain ⟨k, ex, hS, hk⟩ := h
  exact ⟨k + 2, .ifLtN_false ht ex, hS, by omega⟩

lemma LRun.ifLtR_true {a b : ℕ} {t e : Stmt} {c c' : Config} {G G' : List VT} {F' : Forest}
    {m g : ℕ} (ht : c.rreg a < c.rreg b) (h : LRun P W B n t c G c' F' G' m g) :
    LRun P W B n (.ifLtR a b t e) c G c' F' G' m (g + 1) := by
  obtain ⟨k, ex, hS, hk⟩ := h
  exact ⟨k + 1, .ifLtR_true ht ex, hS, by omega⟩

lemma LRun.ifLtR_false {a b : ℕ} {t e : Stmt} {c c' : Config} {G G' : List VT} {F' : Forest}
    {m g : ℕ} (ht : ¬ c.rreg a < c.rreg b) (h : LRun P W B n e c G c' F' G' m g) :
    LRun P W B n (.ifLtR a b t e) c G c' F' G' m (g + 2) := by
  obtain ⟨k, ex, hS, hk⟩ := h
  exact ⟨k + 2, .ifLtR_false ht ex, hS, by omega⟩

/-- **The loop rule.** The ghost state `x : α` (with the stored forest `F` and virtual forest
`G`) carries the invariant `I`, a count `cnt` of the operations made and a potential `ext` for
the further steps. If every iteration makes an amortised run counted `j` operations and `h`
further steps with `cnt x' = cnt x + j` and `ext x' + h + 2 ≤ ext x`, the loop is an amortised
run counted `cnt x' - cnt x` operations and `ext x + 2 - ext x'` further steps. -/
theorem LRun.whileLtN {α : Type*} {a b : ℕ} {body : Stmt}
    (I : α → Forest → List VT → Config → Prop) (cnt ext : α → ℕ)
    (hI : ∀ x F G c, I x F G c → LCTE B n F G c ∧ WordsBounded W c)
    (hbody : ∀ x F G c, I x F G c → c.nreg a < c.nreg b →
      ∃ x' c' F' G' j h, LRun P W B n body c G c' F' G' j h ∧ I x' F' G' c' ∧
        cnt x' = cnt x + j ∧ ext x' + h + 2 ≤ ext x)
    {x : α} {F : Forest} {G : List VT} {c : Config} (hc : I x F G c) :
    ∃ x' c' F' G', LRun P W B n (.whileLtN a b body) c G c' F' G' (cnt x' - cnt x)
        (ext x + 2 - ext x') ∧ I x' F' G' c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      cnt x ≤ cnt x' ∧ ext x' ≤ ext x := by
  induction hN : ext x using Nat.strong_induction_on generalizing x F G c with
  | _ N ih =>
    by_cases ht : c.nreg a < c.nreg b
    · obtain ⟨x₁, c₁, F₁, G₁, j, h, ⟨k₁, e₁, -, hk₁⟩, hI₁, hc₁, he₁⟩ := hbody x F G c hc ht
      obtain ⟨x', c', F', G', ⟨k₂, e₂, hS', hk₂⟩, hI', ht', hcnt, hext⟩ :=
        ih (ext x₁) (by omega) hI₁ rfl
      refine ⟨x', c', F', G', ⟨k₁ + 2 + k₂, .whileLtN_true ht e₁ e₂, hS', ?_⟩, hI', ht',
        by omega, by omega⟩
      have hm : cnt x' - cnt x = j + (cnt x' - cnt x₁) := by omega
      rw [hm, Nat.add_mul]
      omega
    · obtain ⟨hS, hw⟩ := hI x F G c hc
      exact ⟨x, c, F, G, ⟨2, .whileLtN_false ht hw, hS, by omega⟩, hc, ht, le_rfl, by omega⟩

end

/-! ### Runs with the list of operations performed -/

lemma runOpsE_fst_append (n : ℕ) : ∀ (F : Forest) (os os' : List EOp),
    (runOpsE n F (os ++ os')).1 = (runOpsE n (runOpsE n F os).1 os').1
  | _, [], _ => rfl
  | F, o :: os, os' => runOpsE_fst_append n (o.apply n F) os os'

lemma validOpsE_append_iff (n : ℕ) : ∀ (F : Forest) (os os' : List EOp),
    ValidOpsE n F (os ++ os') ↔ ValidOpsE n F os ∧ ValidOpsE n (runOpsE n F os).1 os'
  | _, [], _ => by simp [ValidOpsE, runOpsE]
  | F, o :: os, os' => by
    simp only [List.cons_append, ValidOpsE, runOpsE, validOpsE_append_iff n _ os os', and_assoc]

/-- **An amortised run performing the operations `os`** from the stored forest `F`: they are
valid, and the run ends with `(runOpsE n F os).1` stored. -/
def ORun (P : Input) (W B n : ℕ) (s : Stmt) (c : Config) (F : Forest) (G : List VT)
    (c' : Config) (os : List EOp) (G' : List VT) (m g : ℕ) : Prop :=
  ValidOpsE n F os ∧ LRun P W B n s c G c' (runOpsE n F os).1 G' m g

section
variable {P : Input} {W B n : ℕ}

lemma ORun.seq {s t : Stmt} {c c₁ c₂ : Config} {F : Forest} {G G₁ G₂ : List VT}
    {os₁ os₂ : List EOp} {m₁ g₁ m₂ g₂ : ℕ} (h₁ : ORun P W B n s c F G c₁ os₁ G₁ m₁ g₁)
    (h₂ : ORun P W B n t c₁ (runOpsE n F os₁).1 G₁ c₂ os₂ G₂ m₂ g₂) :
    ORun P W B n (.seq s t) c F G c₂ (os₁ ++ os₂) G₂ (m₁ + m₂) (g₁ + g₂) :=
  ⟨(validOpsE_append_iff n F os₁ os₂).2 ⟨h₁.1, h₂.1⟩, by
    rw [runOpsE_fst_append]; exact h₁.2.seq h₂.2⟩

lemma ORun.mono {s : Stmt} {c c' : Config} {F : Forest} {G G' : List VT} {os : List EOp}
    {m g m' g' : ℕ} (h : ORun P W B n s c F G c' os G' m g) (hm : m ≤ m') (hg : g ≤ g') :
    ORun P W B n s c F G c' os G' m' g' := ⟨h.1, h.2.mono hm hg⟩

/-- Glue code (`LRun.glue`) performs no operation. -/
lemma ORun.glue {s : Stmt} {c c' : Config} {F : Forest} {G : List VT} {k : ℕ}
    (e : Exec P W s c c' k) (hS : LCTE B n F G c)
    (hm : ∀ a, B ≤ a → a < B + 16 * (n + 1) → c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a)
    (h151 : c'.nreg 151 = c.nreg 151) : ORun P W B n s c F G c' [] G 0 k :=
  ⟨trivial, LRun.glue e hS hm h151⟩

lemma ORun.ifLtN_true {a b : ℕ} {t e : Stmt} {c c' : Config} {F : Forest} {G G' : List VT}
    {os : List EOp} {m g : ℕ} (ht : c.nreg a < c.nreg b) (h : ORun P W B n t c F G c' os G' m g) :
    ORun P W B n (.ifLtN a b t e) c F G c' os G' m (g + 1) := ⟨h.1, h.2.ifLtN_true ht⟩

lemma ORun.ifLtN_false {a b : ℕ} {t e : Stmt} {c c' : Config} {F : Forest} {G G' : List VT}
    {os : List EOp} {m g : ℕ} (ht : ¬ c.nreg a < c.nreg b)
    (h : ORun P W B n e c F G c' os G' m g) :
    ORun P W B n (.ifLtN a b t e) c F G c' os G' m (g + 2) := ⟨h.1, h.2.ifLtN_false ht⟩

lemma ORun.ifLtR_true {a b : ℕ} {t e : Stmt} {c c' : Config} {F : Forest} {G G' : List VT}
    {os : List EOp} {m g : ℕ} (ht : c.rreg a < c.rreg b) (h : ORun P W B n t c F G c' os G' m g) :
    ORun P W B n (.ifLtR a b t e) c F G c' os G' m (g + 1) := ⟨h.1, h.2.ifLtR_true ht⟩

lemma ORun.ifLtR_false {a b : ℕ} {t e : Stmt} {c c' : Config} {F : Forest} {G G' : List VT}
    {os : List EOp} {m g : ℕ} (ht : ¬ c.rreg a < c.rreg b)
    (h : ORun P W B n e c F G c' os G' m g) :
    ORun P W B n (.ifLtR a b t e) c F G c' os G' m (g + 2) := ⟨h.1, h.2.ifLtR_false ht⟩

/-- **The loop rule with the operations performed.** The ghost state is `x : α` and the list
`hs` of the operations performed since the forest `F₀`: the stored forest is
`(runOpsE n F₀ hs).1`. If every iteration performs operations `os` (an `ORun`, counted `j`
operations and `h` further steps) with `cnt x' = cnt x + j` and `ext x' + h + 2 ≤ ext x`, the
loop performs the concatenation `os` of the operations of its iterations, counted
`cnt x' - cnt x` operations and `ext x + 2 - ext x'` further steps. -/
theorem ORun.whileLtN {α : Type*} {a b : ℕ} {body : Stmt} (F₀ : Forest)
    (I : α → List EOp → List VT → Config → Prop) (cnt ext : α → ℕ)
    (hI : ∀ x hs G c, I x hs G c → ValidOpsE n F₀ hs →
      LCTE B n (runOpsE n F₀ hs).1 G c ∧ WordsBounded W c)
    (hbody : ∀ x hs G c, I x hs G c → ValidOpsE n F₀ hs → c.nreg a < c.nreg b →
      ∃ x' c' os G' j h, ORun P W B n body c (runOpsE n F₀ hs).1 G c' os G' j h ∧
        I x' (hs ++ os) G' c' ∧ cnt x' = cnt x + j ∧ ext x' + h + 2 ≤ ext x)
    {x : α} {hs : List EOp} {G : List VT} {c : Config} (hc : I x hs G c)
    (hv : ValidOpsE n F₀ hs) :
    ∃ x' os c' G', ORun P W B n (.whileLtN a b body) c (runOpsE n F₀ hs).1 G c' os G'
        (cnt x' - cnt x) (ext x + 2 - ext x') ∧ I x' (hs ++ os) G' c' ∧
      ¬ c'.nreg a < c'.nreg b ∧ cnt x ≤ cnt x' ∧ ext x' ≤ ext x := by
  let J : α × List EOp → Forest → List VT → Config → Prop := fun y F G c =>
    I y.1 y.2 G c ∧ ValidOpsE n F₀ y.2 ∧ F = (runOpsE n F₀ y.2).1 ∧ ∃ os, y.2 = hs ++ os
  obtain ⟨⟨x', hs'⟩, c', F', G', hrun, ⟨hI', hv', rfl, os, rfl⟩, ht', hcnt, hext⟩ :=
    LRun.whileLtN (P := P) (W := W) (B := B) (n := n) (a := a) (b := b) (body := body) J
      (fun y => cnt y.1) (fun y => ext y.1)
      (fun y F G c ⟨h1, h2, h3, _⟩ => h3 ▸ hI y.1 y.2 G c h1 h2)
      (fun y F G c ⟨h1, h2, h3, os₀, h4⟩ ht => by
        obtain ⟨x₁, c₁, os₁, G₁, j, h, ⟨hv₁, hr₁⟩, hI₁, hc₁, he₁⟩ := hbody y.1 y.2 G c h1 h2 ht
        refine ⟨(x₁, y.2 ++ os₁), c₁, _, G₁, j, h, h3 ▸ hr₁, ⟨hI₁,
          (validOpsE_append_iff n F₀ _ _).2 ⟨h2, hv₁⟩, (runOpsE_fst_append n F₀ _ _).symm,
          os₀ ++ os₁, by rw [h4, List.append_assoc]⟩, hc₁, he₁⟩)
      (x := (x, hs)) ⟨hc, hv, rfl, [], by simp⟩
  refine ⟨x', os, c', G', ⟨((validOpsE_append_iff n F₀ hs os).1 hv').2, ?_⟩, hI', ht', hcnt,
    hext⟩
  rw [← runOpsE_fst_append]; exact hrun

/-- **The loop rule paying the further steps by the operations.** -/
theorem LRun.whileLtN_abs {α : Type*} {a b : ℕ} {body : Stmt}
    (I : α → Forest → List VT → Config → Prop) (cnt μ : α → ℕ)
    (hI : ∀ x F G c, I x F G c → LCTE B n F G c ∧ WordsBounded W c)
    (hbody : ∀ x F G c, I x F G c → c.nreg a < c.nreg b →
      ∃ x' c' F' G' j h, LRun P W B n body c G c' F' G' j h ∧ I x' F' G' c' ∧
        cnt x' = cnt x + j ∧ 1 ≤ j ∧ h + 2 ≤ opCostE n ∧ μ x' < μ x)
    {x : α} {F : Forest} {G : List VT} {c : Config} (hc : I x F G c) :
    ∃ x' c' F' G', LRun P W B n (.whileLtN a b body) c G c' F' G' (2 * (cnt x' - cnt x)) 2 ∧
      I x' F' G' c' ∧ ¬ c'.nreg a < c'.nreg b ∧ cnt x ≤ cnt x' := by
  induction hN : μ x using Nat.strong_induction_on generalizing x F G c with
  | _ N ih =>
    by_cases ht : c.nreg a < c.nreg b
    · obtain ⟨x₁, c₁, F₁, G₁, j, h, ⟨k₁, e₁, -, hk₁⟩, hI₁, hc₁, hj, hh, hμ⟩ :=
        hbody x F G c hc ht
      obtain ⟨x', c', F', G', ⟨k₂, e₂, hS', hk₂⟩, hI', ht', hcnt⟩ :=
        ih (μ x₁) (by omega) hI₁ rfl
      refine ⟨x', c', F', G', ⟨k₁ + 2 + k₂, .whileLtN_true ht e₁ e₂, hS', ?_⟩, hI', ht',
        by omega⟩
      have hm : 2 * (cnt x' - cnt x) = 2 * j + 2 * (cnt x' - cnt x₁) := by omega
      have hO : opCostE n ≤ j * opCostE n := Nat.le_mul_of_pos_left _ hj
      rw [hm, Nat.add_mul]
      have : 2 * j * opCostE n = j * opCostE n + j * opCostE n := by ring
      omega
    · obtain ⟨hS, hw⟩ := hI x F G c hc
      exact ⟨x, c, F, G, ⟨2, .whileLtN_false ht hw, hS, by omega⟩, hc, ht, le_rfl⟩

/-- **The loop rule paying the further steps by the operations, with the operations
performed** (as `ORun.whileLtN`). -/
theorem ORun.whileLtN_abs {α : Type*} {a b : ℕ} {body : Stmt}
    (F₀ : Forest) (I : α → List EOp → List VT → Config → Prop) (cnt μ : α → ℕ)
    (hI : ∀ x hs G c, I x hs G c → ValidOpsE n F₀ hs →
      LCTE B n (runOpsE n F₀ hs).1 G c ∧ WordsBounded W c)
    (hbody : ∀ x hs G c, I x hs G c → ValidOpsE n F₀ hs → c.nreg a < c.nreg b →
      ∃ x' c' os G' j h, ORun P W B n body c (runOpsE n F₀ hs).1 G c' os G' j h ∧
        I x' (hs ++ os) G' c' ∧ cnt x' = cnt x + j ∧ 1 ≤ j ∧ h + 2 ≤ opCostE n ∧ μ x' < μ x)
    {x : α} {hs : List EOp} {G : List VT} {c : Config} (hc : I x hs G c)
    (hv : ValidOpsE n F₀ hs) :
    ∃ x' os c' G', ORun P W B n (.whileLtN a b body) c (runOpsE n F₀ hs).1 G c' os G'
        (2 * (cnt x' - cnt x)) 2 ∧ I x' (hs ++ os) G' c' ∧
      ¬ c'.nreg a < c'.nreg b ∧ cnt x ≤ cnt x' := by
  let J : α × List EOp → Forest → List VT → Config → Prop := fun y F G c =>
    I y.1 y.2 G c ∧ ValidOpsE n F₀ y.2 ∧ F = (runOpsE n F₀ y.2).1 ∧ ∃ os, y.2 = hs ++ os
  obtain ⟨⟨x', hs'⟩, c', F', G', hrun, ⟨hI', hv', rfl, os, rfl⟩, ht', hcnt⟩ :=
    LRun.whileLtN_abs (P := P) (W := W) (B := B) (n := n) (a := a) (b := b) (body := body) J
      (fun y => cnt y.1) (fun y => μ y.1)
      (fun y F G c ⟨h1, h2, h3, _⟩ => h3 ▸ hI y.1 y.2 G c h1 h2)
      (fun y F G c ⟨h1, h2, h3, os₀, h4⟩ ht => by
        obtain ⟨x₁, c₁, os₁, G₁, j, h, ⟨hv₁, hr₁⟩, hI₁, hc₁, hj, hh, hμ⟩ :=
          hbody y.1 y.2 G c h1 h2 ht
        refine ⟨(x₁, y.2 ++ os₁), c₁, _, G₁, j, h, h3 ▸ hr₁, ⟨hI₁,
          (validOpsE_append_iff n F₀ _ _).2 ⟨h2, hv₁⟩, (runOpsE_fst_append n F₀ _ _).symm,
          os₀ ++ os₁, by rw [h4, List.append_assoc]⟩, hc₁, hj, hh, hμ⟩)
      (x := (x, hs)) ⟨hc, hv, rfl, [], by simp⟩
  refine ⟨x', os, c', G', ⟨((validOpsE_append_iff n F₀ hs os).1 hv').2, ?_⟩, hI', ht', hcnt⟩
  rw [← runOpsE_fst_append]; exact hrun

/-! ### The register-operand blocks as runs -/

lemma ORun.single {s : Stmt} {c c' : Config} {F : Forest} {G G' : List VT} {o : EOp} {k : ℕ}
    (e : Exec P W s c c' k) (hv : o.Valid n F) (hS : LCTE B n (o.apply n F) G' c')
    (hk : k + 16400 * potL G' ≤ 16400 * potL G + opCostE n) :
    ORun P W B n s c F G c' [o] G' 1 0 :=
  ⟨⟨hv, trivial⟩, LRun.of_exec e hS hk (by omega)⟩

lemma ORun.query {s : Stmt} {c c' : Config} {F : Forest} {G G' : List VT} {k m : ℕ}
    (e : Exec P W s c c' k) (hS : LCTE B n F G' c')
    (hk : k + 16400 * potL G' ≤ 16400 * potL G + m * opCostE n) :
    ORun P W B n s c F G c' [] G' m 0 :=
  ⟨trivial, LRun.of_exec e hS hk (by omega)⟩

theorem regLink_orun (hW : B + 16 * (n + 1) ≤ W) {c : Config} (hc : WordsBounded W c)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {ra rb v w : ℕ} (hrb : rb ≠ 193)
    (hv : c.nreg ra = v) (hw : c.nreg rb = w) (hvn : v < n) (hwn : w < n) (hp : F.par v = n)
    (hroot : findRoot F n w ≠ v) :
    ∃ c' G', ORun P W B n (regLinkS B ra rb) c F G c' [.link v w] G' 1 0 ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', k, e, G', hS', hmf, hfr, hk⟩ :=
    regLink_exec (P := P) B n hc hW hS hrb hv hw hvn hwn hp hroot
  exact ⟨c', G', ORun.single e ⟨hvn, hwn, hp, hroot⟩ hS' (by unfold opCostE; linarith), hmf,
    hfr⟩

theorem regCut_orun (hW : B + 16 * (n + 1) ≤ W) {c : Config} (hc : WordsBounded W c)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {ra v : ℕ} (hv : c.nreg ra = v)
    (hvn : v < n) (hp : F.par v < n) :
    ∃ c' G', ORun P W B n (regCutS B ra) c F G c' [.cut v] G' 1 0 ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', k, e, G', hS', hmf, hfr, hk⟩ := regCut_exec (P := P) B n hc hW hS hv hvn hp
  exact ⟨c', G', ORun.single e ⟨hvn, hp⟩ hS' (by unfold opCostE; linarith), hmf, hfr⟩

/-- `add` with an integer amount `z` in the real `r rz`. -/
theorem regAdd_orun (hW : B + 16 * (n + 1) ≤ W) {c : Config} (hc : WordsBounded W c)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {ra rz v : ℕ} {z : ℤ} (hv : c.nreg ra = v)
    (hz : c.rreg rz = (z : ℝ)) (hvn : v < n) :
    ∃ c' G', ORun P W B n (regAddS B ra rz) c F G c' [.add v z] G' 1 0 ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', k, e, G', hS', hmf, hfr, hk⟩ := regAdd_exec (P := P) B n hc hW hS (rz := rz) hv hvn
  rw [hz] at hS'
  exact ⟨c', G', ORun.single e hvn hS' (by unfold opCostE; linarith), hmf, hfr⟩

/-- `add2` with an integer amount `z` in the real `r rz`. -/
theorem regAdd2_orun (hW : B + 16 * (n + 1) ≤ W) {c : Config} (hc : WordsBounded W c)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {ra rz v : ℕ} {z : ℤ} (hv : c.nreg ra = v)
    (hz : c.rreg rz = (z : ℝ)) (hvn : v < n) :
    ∃ c' G', ORun P W B n (regAdd2S B ra rz) c F G c' [.add2 v z] G' 1 0 ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', k, e, G', hS', hmf, hfr, hk⟩ := regAdd2_exec (P := P) B n hc hW hS (rz := rz) hv hvn
  rw [hz] at hS'
  exact ⟨c', G', ORun.single e hvn hS' (by unfold opCostE; linarith), hmf, hfr⟩

theorem regEvert_orun (hW : B + 16 * (n + 1) ≤ W) {c : Config} (hc : WordsBounded W c)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {ra v : ℕ} (hv : c.nreg ra = v)
    (hvn : v < n) :
    ∃ c' G', ORun P W B n (regEvertS B ra) c F G c' [.evert v] G' 1 0 ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', k, e, G', hS', hmf, hfr, hk⟩ := regEvert_exec (P := P) B n hc hW hS hv hvn
  exact ⟨c', G', ORun.single e hvn hS' (by unfold opCostE; linarith), hmf, hfr⟩

theorem regQuery_orun (hW : B + 16 * (n + 1) ≤ W) {c : Config} (hc : WordsBounded W c)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {ra v : ℕ} (hv : c.nreg ra = v)
    (hvn : v < n) :
    ∃ c' G', ORun P W B n (regQueryS B ra) c F G c' [] G' 1 0 ∧
      c'.nreg 195 = findRoot F n v ∧ c'.nreg 196 = (pathMin F n v).2 ∧
      c'.rreg 195 = (pathMin F n v).1 ∧ c'.rreg 196 = pathSum F n v ∧
      c'.rreg 200 = c.rreg 200 ∧ MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', k, e, G', hS', h1, h2, h3, h4, h5, hmf, hfr, hk⟩ :=
    regQuery_exec (P := P) B n hc hW hS hv hvn
  exact ⟨c', G', ORun.query e hS' (by unfold opCostE; linarith), h1, h2, h3, h4, h5, hmf, hfr⟩

theorem regQuery2_orun (hW : B + 16 * (n + 1) ≤ W) {c : Config} (hc : WordsBounded W c)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {ra v : ℕ} (hv : c.nreg ra = v)
    (hvn : v < n) :
    ∃ c' G', ORun P W B n (regQuery2S B ra) c F G c' [] G' 1 0 ∧
      c'.nreg 196 = (pathMin2 F n v).2 ∧ c'.rreg 195 = (pathMin2 F n v).1 ∧
      c'.rreg 196 = pathSum2 F n v ∧
      c'.rreg 200 = c.rreg 200 ∧ MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', k, e, G', hS', h2, h3, h4, h5, hmf, hfr, hk⟩ :=
    regQuery2_exec (P := P) B n hc hW hS hv hvn
  exact ⟨c', G', ORun.query e hS' (by unfold opCostE; linarith), h2, h3, h4, h5, hmf, hfr⟩

theorem regMin_orun (hW : B + 16 * (n + 1) ≤ W) {c : Config} (hc : WordsBounded W c)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {ra rz v : ℕ} (hv : c.nreg ra = v)
    (hvn : v < n) :
    ∃ c' G', ORun P W B n (regMinS B ra rz) c F G c' [] G' 1 0 ∧
      c'.nreg 196 = (pathMin F n v).2 ∧ c'.rreg 195 = (pathMin F n v).1 ∧
      c'.nreg 198 = (if (pathMin F n v).1 < c.rreg rz then 1 else 0) ∧
      c'.nreg 195 = findRoot F n v ∧ c'.rreg 196 = pathSum F n v ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', k, e, G', hS', h1, h2, h3, h4, h5, hmf, hfr, hk⟩ :=
    regMin_exec (P := P) B n hc hW hS (rz := rz) hv hvn
  exact ⟨c', G', ORun.query e hS' (by unfold opCostE; linarith), h1, h2, h3, h4, h5, hmf, hfr⟩

theorem regMin2_orun (hW : B + 16 * (n + 1) ≤ W) {c : Config} (hc : WordsBounded W c)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {ra rz v : ℕ} (hv : c.nreg ra = v)
    (hvn : v < n) :
    ∃ c' G', ORun P W B n (regMin2S B ra rz) c F G c' [] G' 1 0 ∧
      c'.nreg 196 = (pathMin2 F n v).2 ∧ c'.rreg 195 = (pathMin2 F n v).1 ∧
      c'.nreg 198 = (if (pathMin2 F n v).1 < c.rreg rz then 1 else 0) ∧
      c'.rreg 196 = pathSum2 F n v ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', k, e, G', hS', h1, h2, h3, h4, hmf, hfr, hk⟩ :=
    regMin2_exec (P := P) B n hc hW hS (rz := rz) hv hvn
  exact ⟨c', G', ORun.query e hS' (by unfold opCostE; linarith), h1, h2, h3, h4, hmf, hfr⟩

theorem regParent_orun (hW : B + 16 * (n + 1) ≤ W) {c : Config} (hc : WordsBounded W c)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {ra v : ℕ} (hv : c.nreg ra = v)
    (hvn : v < n) :
    ∃ c' G', ORun P W B n (regParentS B ra) c F G c' [] G' 1 0 ∧
      c'.nreg 195 = F.par v ∧
      c'.rreg 200 = c.rreg 200 ∧ MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', k, e, G', hS', h1, h2, hmf, hfr, hk⟩ := regParent_exec (P := P) B n hc hW hS hv hvn
  exact ⟨c', G', ORun.query e hS' (by unfold opCostE; linarith), h1, h2, hmf, hfr⟩

/-- Reading the value of one node: counted two operations. -/
theorem regVal_orun (hW : B + 16 * (n + 1) ≤ W) (k : Bool) {c : Config} (hc : WordsBounded W c)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {ra v : ℕ} (hv : c.nreg ra = v)
    (hvn : v < n) :
    ∃ c' G', ORun P W B n (regValS B k ra) c F G c' [] G' 2 0 ∧
      c'.rreg 195 = F.valc k v ∧ MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', k', e, G', hS', h1, hmf, hfr, hk⟩ := regVal_exec (P := P) B n k hc hW hS hv hvn
  exact ⟨c', G', ORun.query e hS' (by unfold opCostE; linarith), h1, hmf, hfr⟩

/-- Setting the value of a root to `x = ` the real `r rz`, with `x - valc k v = q` an integer:
the operation `add v q` (`add2 v q` for `k = true`). -/
theorem regSet_orun (hW : B + 16 * (n + 1) ≤ W) (k : Bool) {c : Config} (hc : WordsBounded W c)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {ra rz v : ℕ} {q : ℤ} (hv : c.nreg ra = v)
    (hvn : v < n) (hp : F.par v = n) (hq : c.rreg rz - F.valc k v = (q : ℝ)) :
    ∃ c' G', ORun P W B n (regSetS B k ra rz) c F G c'
        [if k then .add2 v q else .add v q] G' 1 0 ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', k', e, G', hS', hmf, hfr, hk⟩ :=
    regSet_exec (P := P) B n k hc hW hS (rz := rz) hv hvn hp
  have hF : F.setValC k v (c.rreg rz) =
      (if k then EOp.add2 v q else EOp.add v q).apply n F := by
    rw [← addPathC_root hvn hp.ge k, hq]
    cases k <;> rfl
  rw [hF] at hS'
  refine ⟨c', G', ORun.single e ?_ hS' (by unfold opCostE; linarith), hmf, hfr⟩
  cases k <;> exact hvn

end

/-! ### Adaptive programs -/

section
variable {W : ℕ}

/-- **An adaptive program on the evertable link-cut tree.** `r151 := n`, the initialisation, then
`s`: if `s`, from the initialised structure (any configuration that the initialisation may
leave: the empty forest stored as `G0 n`, nothing printed, the registers outside `r160 … r199`
other than `r151` and the memory outside the structure as at the start), makes an amortised run
counted at most `m` operations and `g` further steps and prints `out`, the program prints `out`
within `140 (n + 1) + 22 + m · opCostE n + g` steps. -/
theorem lctE_adaptive_run (B n : ℕ) (s : Stmt) (P : Input) (m g : ℕ) (out : List ℕ)
    (hs : ∀ c, WordsBounded (B + 16 * (n + 1)) c → LCTE B n (Forest.init n) (G0 n) c →
      c.output = [] → MemFrame B n (mem initConfig) (mem c) →
      (∀ r, (r < 160 ∨ 200 ≤ r) → r ≠ 151 → c.nreg r = 0 ∧ c.rreg r = 0) →
      ∃ c' F' G' m', LRun P (B + 16 * (n + 1)) B n s c (G0 n) c' F' G' m' g ∧ m' ≤ m ∧
        c'.output = out) :
    RunsWithin (compile (.seq (.instr (.constN 151 n)) (.seq (initS B) s)) 0 ++ [Instr.halt]) P
      (B + 16 * (n + 1)) (140 * (n + 1) + 22 + m * opCostE n + g) out := by
  have hc := wordsBounded_initConfig (B + 16 * (n + 1))
  have e1 := Exec.constN (P := P) hc 151 n (by omega)
  obtain ⟨c2, k2, e2, hk2, hS2, hpot, hmf2, hfr2⟩ := init_exec (P := P) B n e1.wb_right le_rfl
    (by simp)
  obtain ⟨c3, F3, G3, m', ⟨k3, e3, -, hk3⟩, hm', ho⟩ := hs c2 e2.wb_right hS2.toE
    (by rw [hfr2.2.2]; rfl) hmf2 (fun r hr h151 => by
      rw [(hfr2.1 r hr).1, (hfr2.1 r hr).2]; simp [initConfig, h151])
  refine RunsWithin.mono_steps (runsWithin_of_exec_output (.seq e1 (.seq e2 e3)) ho) ?_
  rw [hpot] at hk3
  have := Nat.mul_le_mul_right (opCostE n) hm'
  omega

/-- **The cost of an adaptive program**: `400000 (n + m + 1) (⌊log₂ n⌋ + 1) + g` steps, with
words at most `B + 16 (n + 1)` (`lctE_runsWithin` for a fixed list). -/
theorem lctE_adaptive_runsWithin (B n : ℕ) (s : Stmt) (P : Input) (m g : ℕ) (out : List ℕ)
    (hs : ∀ c, WordsBounded (B + 16 * (n + 1)) c → LCTE B n (Forest.init n) (G0 n) c →
      c.output = [] → MemFrame B n (mem initConfig) (mem c) →
      (∀ r, (r < 160 ∨ 200 ≤ r) → r ≠ 151 → c.nreg r = 0 ∧ c.rreg r = 0) →
      ∃ c' F' G' m', LRun P (B + 16 * (n + 1)) B n s c (G0 n) c' F' G' m' g ∧ m' ≤ m ∧
        c'.output = out) :
    RunsWithin (compile (.seq (.instr (.constN 151 n)) (.seq (initS B) s)) 0 ++ [Instr.halt]) P
      (B + 16 * (n + 1)) (400000 * (n + m + 1) * (Nat.log 2 n + 1) + g) out := by
  refine RunsWithin.mono_steps (lctE_adaptive_run B n s P m g out hs) ?_
  unfold opCostE
  nlinarith

/-- The hypothesis of `lctE_adaptive_runsWithin` is met: the empty program. -/
example (B n : ℕ) (P : Input) :
    RunsWithin (compile (.seq (.instr (.constN 151 n)) (.seq (initS B) .skip)) 0 ++
      [Instr.halt]) P (B + 16 * (n + 1)) (400000 * (n + 0 + 1) * (Nat.log 2 n + 1) + 0) [] :=
  lctE_adaptive_runsWithin B n .skip P 0 0 [] fun c hc hS ho _ _ =>
    ⟨c, _, _, 0, LRun.skip hc hS, le_rfl, ho⟩

end

end DynTree

end PlanarFlow
