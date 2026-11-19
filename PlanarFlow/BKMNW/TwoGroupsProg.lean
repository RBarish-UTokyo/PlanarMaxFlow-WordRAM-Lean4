module

public import PlanarFlow.BKMNW.ExistGroupD
public import WordRAM.Programs.Tactics

/-!
# The two groups of a split on the machine

`PlanarFlow.BKMNW.twoGroupsL ω A l` (the first group of a split: the first item of weight
`> A/2`, else the longest prefix of weight `≤ A`, or the first item alone if that prefix is all of
`l`) computed by a natural-word program in two linear scans over an array of weights.

Layout: the items are `0, …, m-1` (the classes listed in some order), their weights
`WT[j] = nmem (Wb + j)`. Registers: `4000 = m`, `4001 = Wb`, `4002 = A`; constants
`4003 = 1`, `4004 = 0`; loop index `4005`; scan 1: flag `4006`, index `4007`; scan 2: sum `4010`,
length `4011`; scratch `4008`, `4009`, `4013`. Output: `4006 = 1` and `4007 = h` (the group is
`[h]`), or `4006 = 0` and the group `List.range (min r4011 m)`.

* `twoGroupsL_map` (the group commutes with renaming the items), `twoGroupsL_congr`,
  `pfx_append`, `find?_range_succ`, `pfx_range_succ`, `tgStep2`;
* `tgBody1`, `tgBody2`, `tgFix`, **`tgProg`**;
* **`tgProg_exec`**: within `23 m + 15` steps, `twoGroupsL ω A (List.range m) = if r4006 = 1
  then [r4007] else List.range (min r4011 m)` for `ω j = nmem (Wb + j)`; registers outside
  `4003 … 4013`, the memory, the reals and the output kept (word bounds: `Wb + m ≤ W`,
  `A + 2 WT[j] ≤ W`, `m + 1 ≤ W`); **`tgProg_exec_list`**: the same for any list
  `(List.range m).map g` of items with weights `ω (g j) = WT[j]`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The functional side -/

section Fun

lemma tgIteT {α : Sort*} {p : Prop} [Decidable p] {a b : α} (h : p) :
    (if p then a else b) = a := by simp [h]

lemma tgIteF {α : Sort*} {p : Prop} [Decidable p] {a b : α} (h : ¬ p) :
    (if p then a else b) = b := by simp [h]

variable {ι κ : Type*}

lemma pfx_map (ω : κ → ℕ) (A : ℕ) (g : ι → κ) :
    ∀ (l : List ι) (s : ℕ), pfx ω A (l.map g) s = (pfx (ω ∘ g) A l s).map g
  | [], _ => rfl
  | i :: l, s => by
    simp only [List.map_cons, pfx, Function.comp_apply]
    split_ifs
    · rw [List.map_cons, pfx_map ω A g l]
    · rfl

/-- **The group commutes with renaming the items.** -/
theorem twoGroupsL_map (ω : κ → ℕ) (A : ℕ) (g : ι → κ) (l : List ι) :
    twoGroupsL ω A (l.map g) = (twoGroupsL (ω ∘ g) A l).map g := by
  unfold twoGroupsL
  rw [List.find?_map]
  have hp : ((fun i => decide (A < 2 * ω i)) ∘ g) = fun i => decide (A < 2 * (ω ∘ g) i) := rfl
  rw [hp]
  cases l.find? (fun i => decide (A < 2 * (ω ∘ g) i)) with
  | some i => rfl
  | none =>
    simp only [Option.map_none, pfx_map, List.length_map]
    split_ifs
    · rw [List.map_take]
    · rfl

/-- The prefix of a concatenation. -/
lemma pfx_append (ω : ι → ℕ) (A : ℕ) :
    ∀ (l₁ l₂ : List ι) (s : ℕ), pfx ω A (l₁ ++ l₂) s =
      if (pfx ω A l₁ s).length = l₁.length then l₁ ++ pfx ω A l₂ (s + (l₁.map ω).sum)
      else pfx ω A l₁ s
  | [], l₂, s => by simp [pfx]
  | i :: l, l₂, s => by
    by_cases h : s + ω i ≤ A
    · have ih := pfx_append ω A l l₂ (s + ω i)
      simp only [List.cons_append, pfx, h, ↓reduceIte, List.length_cons, add_left_inj,
        List.map_cons, List.sum_cons]
      rw [ih]
      split_ifs
      · simp only [List.cons_append, add_assoc]
      · rfl
    · simp [pfx, h]

lemma find?_range_succ (p : ℕ → Bool) (i : ℕ) :
    (List.range (i + 1)).find? p = match (List.range i).find? p with
      | some h => some h
      | none => if p i then some i else none := by
  rw [List.range_succ, List.find?_append]
  cases (List.range i).find? p with
  | some h => rfl
  | none =>
    simp only [Option.none_or, List.find?_cons, List.find?_nil]
    cases p i <;> rfl

lemma pfx_range_succ (ω : ℕ → ℕ) (A : ℕ) {i k : ℕ}
    (h : pfx ω A (List.range i) 0 = List.range k) (hk : k ≤ i) :
    pfx ω A (List.range (i + 1)) 0 = if k < i then List.range k else
      if ((List.range i).map ω).sum + ω i ≤ A then List.range (i + 1) else List.range i := by
  rw [List.range_succ, pfx_append, h, List.length_range, List.length_range]
  by_cases hki : k < i
  · simp only [hki, ↓reduceIte, show k ≠ i by omega]
  · have hk' : k = i := by omega
    subst hk'
    simp only [lt_self_iff_false, ↓reduceIte, pfx, zero_add, List.append_nil]
    split_ifs <;> simp

/-- The extension test of scan 2: the prefix is whole and the item fits. -/
def tgExt (A k j s w : ℕ) : Prop := ¬ k < j ∧ s + w ≤ A

instance (A k j s w : ℕ) : Decidable (tgExt A k j s w) := by unfold tgExt; infer_instance

/-- One step of scan 2 on the prefix, its length and its weight. -/
lemma tgStep2 (ω : ℕ → ℕ) (A : ℕ) {i k s : ℕ} (h : pfx ω A (List.range i) 0 = List.range k)
    (hk : k ≤ i) (hs : s = ((List.range k).map ω).sum) (hsA : s ≤ A) :
    pfx ω A (List.range (i + 1)) 0 =
        List.range (if tgExt A k i s (ω i) then k + 1 else k) ∧
      (if tgExt A k i s (ω i) then k + 1 else k) ≤ i + 1 ∧
      (if tgExt A k i s (ω i) then s + ω i else s) =
        ((List.range (if tgExt A k i s (ω i) then k + 1 else k)).map ω).sum ∧
      (if tgExt A k i s (ω i) then s + ω i else s) ≤ A := by
  rw [pfx_range_succ ω A h hk]
  by_cases hki : k < i
  · have hn : ¬ tgExt A k i s (ω i) := fun h => h.1 hki
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [tgIteF hn, tgIteT hki] <;>
      first | rfl | omega | exact hs | exact hsA
  · have hk' : k = i := by omega
    subst hk'
    rw [tgIteF hki]
    by_cases hfit : s + ω k ≤ A
    · have hy : tgExt A k k s (ω k) := ⟨hki, hfit⟩
      rw [← hs]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [tgIteT hy, tgIteT hfit] <;>
        first | rfl | omega | exact hfit |
          (rw [List.range_succ, List.map_append, List.sum_append, ← hs]; simp)
    · have hn : ¬ tgExt A k k s (ω k) := fun h => hfit h.2
      rw [← hs]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [tgIteF hn, tgIteF hfit] <;>
        first | rfl | omega | exact hs | exact hsA


lemma pfx_congr {ω ω' : ι → ℕ} (A : ℕ) :
    ∀ (l : List ι), (∀ i ∈ l, ω i = ω' i) → ∀ s, pfx ω A l s = pfx ω' A l s
  | [], _, _ => rfl
  | i :: l, h, s => by
    have hi := h i (List.mem_cons_self ..)
    simp only [pfx, hi, pfx_congr A l (fun j hj => h j (List.mem_cons_of_mem _ hj))]

/-- The group depends only on the weights of the items of the list. -/
lemma twoGroupsL_congr {ω ω' : ι → ℕ} (A : ℕ) {l : List ι} (h : ∀ i ∈ l, ω i = ω' i) :
    twoGroupsL ω A l = twoGroupsL ω' A l := by
  unfold twoGroupsL
  rw [List.find?_congr (fun i hi => by rw [h i hi]), pfx_congr A l h]

end Fun

/-! ### The programs -/

/-- Scan 1 at the item `j = r4005`: `r4009 := 2 WT[j]`; if no heavy item yet (`r4006 = 0`) and
`A < 2 WT[j]`, record `j`. -/
def tgBody1 : Stmt :=
  .seq (block [.addN 4008 4001 4005, .loadN 4008 4008, .addN 4009 4008 4008])
    (.seq (.ifLtN 4004 4006 .skip
      (.ifLtN 4002 4009 (block [.constN 4006 1, .copyN 4007 4005]) .skip))
      (block [.addN 4005 4005 4003]))

/-- Scan 2 at the item `j = r4005`: if the prefix is still whole (`¬ r4011 < j`) and
`s + WT[j] ≤ A`, extend it. -/
def tgBody2 : Stmt :=
  .seq (.ifLtN 4011 4005 .skip
    (.seq (block [.addN 4008 4001 4005, .loadN 4008 4008, .addN 4013 4010 4008])
      (.ifLtN 4002 4013 .skip (block [.copyN 4010 4013, .addN 4011 4011 4003]))))
    (block [.addN 4005 4005 4003])

/-- The prefix of all the items is replaced by the first item. -/
def tgFix : Stmt := .ifLtN 4011 4000 .skip (.instr (.constN 4011 1))

/-- **The two groups, on the machine.** -/
def tgProg : Stmt :=
  .seq (block [.constN 4003 1, .constN 4004 0, .constN 4005 0, .constN 4006 0, .constN 4007 0])
    (.seq (.whileLtN 4005 4000 tgBody1)
      (.seq (block [.constN 4005 0, .constN 4010 0, .constN 4011 0])
        (.seq (.whileLtN 4005 4000 tgBody2) tgFix)))


/-! ### The runs -/

section Exec

variable {P : Input} {W : ℕ}


/-- A loop over `[lo, hi)` with an invariant `J i` and a body of cost at most `B`. -/
theorem tgRange {a b : ℕ} {body : Stmt} (J : ℕ → Config → Prop) {lo hi B : ℕ} (c : Config)
    (hc : WordsBounded W c) (ha : c.nreg a = lo) (hb : c.nreg b = hi) (hle : lo ≤ hi)
    (hJ : J lo c)
    (hbody : ∀ i c, lo ≤ i → i < hi → WordsBounded W c → c.nreg a = i → c.nreg b = hi →
      J i c → ∃ c' k, Exec P W body c c' k ∧ k ≤ B ∧ c'.nreg a = i + 1 ∧ c'.nreg b = hi ∧
        J (i + 1) c') :
    ∃ c' k, Exec P W (.whileLtN a b body) c c' k ∧ k ≤ (B + 2) * (hi - lo) + 2 ∧
      WordsBounded W c' ∧ c'.nreg a = hi ∧ J hi c' := by
  obtain ⟨c', k, e, ⟨hw, h1, h2, h3, hJ'⟩, hn, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := a) (b := b) (body := body)
    (fun c => WordsBounded W c ∧ lo ≤ c.nreg a ∧ c.nreg a ≤ hi ∧ c.nreg b = hi ∧ J (c.nreg a) c)
    (fun c => (B + 2) * (hi - c.nreg a)) (fun c h => h.1)
    (fun c ⟨hw, h1, h2, h3, hJ⟩ hlt => by
      rw [h3] at hlt
      obtain ⟨c', k, e, hk, ha', hb', hJ'⟩ := hbody _ c h1 hlt hw rfl h3 hJ
      refine ⟨c', k, e, ⟨e.wb_right, by omega, by omega, hb', by rw [ha']; exact hJ'⟩, ?_⟩
      rw [ha']
      have : (B + 2) * (hi - (c.nreg a + 1)) + (B + 2) ≤ (B + 2) * (hi - c.nreg a) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
      omega) ⟨hc, by omega, by omega, hb, by rw [ha]; exact hJ⟩
  have e' : c'.nreg a = hi := by omega
  refine ⟨c', k, e, by rw [ha] at hk; exact hk, hw, e', by rw [e'] at hJ'; exact hJ'⟩

/-- The heavy test of scan 1. -/
def tgHv (A w f : ℕ) : Prop := f = 0 ∧ A < 2 * w

instance (A w f : ℕ) : Decidable (tgHv A w f) := by unfold tgHv; infer_instance

/-- **Scan 1 at one item.** -/
theorem tgBody1_exec (c : Config) (hc : WordsBounded W c) {Wb A j f : ℕ}
    (r1 : c.nreg 4001 = Wb) (r2 : c.nreg 4002 = A) (r3 : c.nreg 4003 = 1)
    (r4 : c.nreg 4004 = 0) (r5 : c.nreg 4005 = j) (r6 : c.nreg 4006 = f) (hf : f ≤ 1)
    (w1 : Wb + j ≤ W) (w2 : 2 * c.nmem (Wb + j) ≤ W) (w3 : j + 1 ≤ W) :
    ∃ c' k, Exec P W tgBody1 c c' k ∧ k ≤ 9 ∧ c'.nreg 4005 = j + 1 ∧
      c'.nreg 4006 = (if tgHv A (c.nmem (Wb + j)) f then 1 else f) ∧
      c'.nreg 4007 = (if tgHv A (c.nmem (Wb + j)) f then j else c.nreg 4007) ∧
      (∀ r, (r < 4005 ∨ 4009 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tgBody1
  set w := c.nmem (Wb + j) with hw
  obtain ⟨c₁, k₁, e₁, hk₁, g9, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.addN 4008 4001 4005, .loadN 4008 4008, .addN 4009 4008 4008]) c c₁ k₁ ∧
      k₁ = 3 ∧ c₁.nreg 4009 = 2 * w ∧
      (∀ r, r ≠ 4008 → r ≠ 4009 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [r1, r5, ← hw]); omega)
    refine ⟨rfl, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [r1, r5, ← hw]; omega
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q2 : c₁.nreg 4002 = A := by rw [gn₁ _ (by omega) (by omega), r2]
  have q3 : c₁.nreg 4003 = 1 := by rw [gn₁ _ (by omega) (by omega), r3]
  have q4 : c₁.nreg 4004 = 0 := by rw [gn₁ _ (by omega) (by omega), r4]
  have q5 : c₁.nreg 4005 = j := by rw [gn₁ _ (by omega) (by omega), r5]
  have q6 : c₁.nreg 4006 = f := by rw [gn₁ _ (by omega) (by omega), r6]
  obtain ⟨c₂, k₂, e₂, hk₂, g6, g7, gn₂, gm₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
      Exec P W (.ifLtN 4004 4006 .skip
        (.ifLtN 4002 4009 (block [.constN 4006 1, .copyN 4007 4005]) .skip)) c₁ c₂ k₂ ∧
      k₂ ≤ 5 ∧ c₂.nreg 4006 = (if tgHv A w f then 1 else f) ∧
      c₂.nreg 4007 = (if tgHv A w f then j else c₁.nreg 4007) ∧
      (∀ r, r ≠ 4006 → r ≠ 4007 → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    by_cases h0 : c₁.nreg 4004 < c₁.nreg 4006
    · have hn : ¬ tgHv A w f := fun h => by rw [q4, q6] at h0; exact absurd h.1 (by omega)
      refine ⟨c₁, 1, .ifLtN_true h0 (.skip hw₁), by omega, ?_, ?_, fun r _ _ => rfl, rfl, rfl,
        rfl, rfl⟩
      · simp only [hn, ↓reduceIte, q6]
      · simp only [hn, ↓reduceIte]
    · by_cases h1 : c₁.nreg 4002 < c₁.nreg 4009
      · have hy : tgHv A w f := ⟨by rw [q4, q6] at h0; omega, by rw [q2, g9] at h1; exact h1⟩
        obtain ⟨c₃, k₃, e₃, hk₃, h6, h7, hn₃, hm₃, hr₃, hrm₃, ho₃⟩ : ∃ c₃ k₃,
            Exec P W (block [.constN 4006 1, .copyN 4007 4005]) c₁ c₃ k₃ ∧ k₃ = 2 ∧
            c₃.nreg 4006 = 1 ∧ c₃.nreg 4007 = j ∧
            (∀ r, r ≠ 4006 → r ≠ 4007 → c₃.nreg r = c₁.nreg r) ∧ c₃.nmem = c₁.nmem ∧
            c₃.rreg = c₁.rreg ∧ c₃.rmem = c₁.rmem ∧ c₃.output = c₁.output := by
          exec_block
          all_goals try ((try config_simp); omega)
          refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
          · config_simp
          · config_simp; exact q5
          · config_simp; simp only [upd_apply]; split_ifs <;> omega
        refine ⟨c₃, k₃ + 1 + 2, .ifLtN_false h0 (.ifLtN_true h1 e₃), by omega, ?_, ?_, hn₃, hm₃,
          hr₃, hrm₃, ho₃⟩
        · simp only [hy, ↓reduceIte, h6]
        · simp only [hy, ↓reduceIte, h7]
      · have hn : ¬ tgHv A w f := fun h => h1 (by rw [q2, g9]; exact h.2)
        refine ⟨c₁, 0 + 2 + 2, .ifLtN_false h0 (.ifLtN_false h1 (.skip hw₁)), by omega, ?_, ?_,
          fun r _ _ => rfl, rfl, rfl, rfl, rfl⟩
        · simp only [hn, ↓reduceIte, q6]
        · simp only [hn, ↓reduceIte]
  have hw₂ := e₂.wb_right
  have p3 : c₂.nreg 4003 = 1 := by rw [gn₂ _ (by omega) (by omega), q3]
  have p5 : c₂.nreg 4005 = j := by rw [gn₂ _ (by omega) (by omega), q5]
  obtain ⟨c₃, k₃, e₃, hk₃, h5, hn₃, hm₃, hr₃, hrm₃, ho₃⟩ : ∃ c₃ k₃,
      Exec P W (block [.addN 4005 4005 4003]) c₂ c₃ k₃ ∧ k₃ = 1 ∧ c₃.nreg 4005 = j + 1 ∧
      (∀ r, r ≠ 4005 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [p3, p5]); omega)
    refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [p3, p5]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, h5,
    by rw [hn₃ _ (by omega), g6], ?_, fun r hr => ?_, by rw [hm₃, gm₂, gm₁],
    by rw [hr₃, gr₂, gr₁], by rw [hrm₃, grm₂, grm₁], by rw [ho₃, go₂, go₁]⟩
  · rw [hn₃ _ (by omega), g7, gn₁ _ (by omega) (by omega)]
  · rw [hn₃ _ (by omega), gn₂ _ (by omega) (by omega), gn₁ _ (by omega) (by omega)]

/-- **Scan 2 at one item.** -/
theorem tgBody2_exec (c : Config) (hc : WordsBounded W c) {Wb A j s k : ℕ}
    (r1 : c.nreg 4001 = Wb) (r2 : c.nreg 4002 = A) (r3 : c.nreg 4003 = 1)
    (r5 : c.nreg 4005 = j) (r10 : c.nreg 4010 = s) (r11 : c.nreg 4011 = k) (hs : s ≤ A)
    (hk : k ≤ j) (w1 : Wb + j ≤ W) (w2 : A + c.nmem (Wb + j) ≤ W) (w3 : j + 1 ≤ W) :
    ∃ c' t, Exec P W tgBody2 c c' t ∧ t ≤ 10 ∧ c'.nreg 4005 = j + 1 ∧
      c'.nreg 4010 = (if tgExt A k j s (c.nmem (Wb + j)) then s + c.nmem (Wb + j) else s) ∧
      c'.nreg 4011 = (if tgExt A k j s (c.nmem (Wb + j)) then k + 1 else k) ∧
      (∀ r, r ≠ 4005 → r ≠ 4008 → r ≠ 4010 → r ≠ 4011 → r ≠ 4013 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tgBody2
  set w := c.nmem (Wb + j) with hw
  obtain ⟨c₂, k₂, e₂, hk₂, g10, g11, gn₂, gm₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
      Exec P W (.ifLtN 4011 4005 .skip
        (.seq (block [.addN 4008 4001 4005, .loadN 4008 4008, .addN 4013 4010 4008])
          (.ifLtN 4002 4013 .skip (block [.copyN 4010 4013, .addN 4011 4011 4003])))) c c₂ k₂ ∧
      k₂ ≤ 9 ∧ c₂.nreg 4010 = (if tgExt A k j s w then s + w else s) ∧
      c₂.nreg 4011 = (if tgExt A k j s w then k + 1 else k) ∧
      (∀ r, r ≠ 4008 → r ≠ 4010 → r ≠ 4011 → r ≠ 4013 → c₂.nreg r = c.nreg r) ∧
      c₂.nmem = c.nmem ∧ c₂.rreg = c.rreg ∧ c₂.rmem = c.rmem ∧ c₂.output = c.output := by
    by_cases h0 : c.nreg 4011 < c.nreg 4005
    · have hn : ¬ tgExt A k j s w := fun h => h.1 (by rw [r11, r5] at h0; exact h0)
      refine ⟨c, 1, .ifLtN_true h0 (.skip hc), by omega, ?_, ?_, fun r _ _ _ _ => rfl, rfl, rfl,
        rfl, rfl⟩
      · simp only [hn, ↓reduceIte, r10]
      · simp only [hn, ↓reduceIte, r11]
    · obtain ⟨c₁, k₁, e₁, hk₁, g13, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
          Exec P W (block [.addN 4008 4001 4005, .loadN 4008 4008, .addN 4013 4010 4008]) c c₁
            k₁ ∧ k₁ = 3 ∧ c₁.nreg 4013 = s + w ∧
          (∀ r, r ≠ 4008 → r ≠ 4013 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
          c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
        exec_block
        all_goals try ((try config_simp); (try simp only [r1, r5, r10, ← hw]); omega)
        refine ⟨rfl, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp; simp only [r1, r5, r10, ← hw]
        · config_simp; simp only [upd_apply]; split_ifs <;> omega
      have hw₁ := e₁.wb_right
      have q2 : c₁.nreg 4002 = A := by rw [gn₁ _ (by omega) (by omega), r2]
      have q3 : c₁.nreg 4003 = 1 := by rw [gn₁ _ (by omega) (by omega), r3]
      have q10 : c₁.nreg 4010 = s := by rw [gn₁ _ (by omega) (by omega), r10]
      have q11 : c₁.nreg 4011 = k := by rw [gn₁ _ (by omega) (by omega), r11]
      by_cases h1 : c₁.nreg 4002 < c₁.nreg 4013
      · have hn : ¬ tgExt A k j s w := fun h => by rw [q2, g13] at h1; exact absurd h.2 (by omega)
        refine ⟨c₁, k₁ + 1 + 2, .ifLtN_false h0 (.seq e₁ (.ifLtN_true h1 (.skip hw₁))),
          by omega, ?_, ?_, fun r a b c d => gn₁ r a d, gm₁, gr₁, grm₁, go₁⟩
        · simp only [hn, ↓reduceIte, q10]
        · simp only [hn, ↓reduceIte, q11]
      · have hy : tgExt A k j s w := ⟨by rw [r11, r5] at h0; exact h0,
          by rw [q2, g13] at h1; omega⟩
        obtain ⟨c₃, k₃, e₃, hk₃, h10, h11, hn₃, hm₃, hr₃, hrm₃, ho₃⟩ : ∃ c₃ k₃,
            Exec P W (block [.copyN 4010 4013, .addN 4011 4011 4003]) c₁ c₃ k₃ ∧ k₃ = 2 ∧
            c₃.nreg 4010 = s + w ∧ c₃.nreg 4011 = k + 1 ∧
            (∀ r, r ≠ 4010 → r ≠ 4011 → c₃.nreg r = c₁.nreg r) ∧ c₃.nmem = c₁.nmem ∧
            c₃.rreg = c₁.rreg ∧ c₃.rmem = c₁.rmem ∧ c₃.output = c₁.output := by
          exec_block
          all_goals try ((try config_simp); (try simp only [q3, q11]); omega)
          refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
          · config_simp; exact g13
          · config_simp; simp only [q3, q11]
          · config_simp; simp only [upd_apply]; split_ifs <;> omega
        refine ⟨c₃, k₁ + (k₃ + 2) + 2, .ifLtN_false h0 (.seq e₁ (.ifLtN_false h1 e₃)), by omega,
          ?_, ?_, fun r a b c d => ?_, by rw [hm₃, gm₁], by rw [hr₃, gr₁], by rw [hrm₃, grm₁],
          by rw [ho₃, go₁]⟩
        · simp only [hy, ↓reduceIte, h10]
        · simp only [hy, ↓reduceIte, h11]
        · rw [hn₃ r b c, gn₁ r a d]
  have hw₂ := e₂.wb_right
  have p3 : c₂.nreg 4003 = 1 := by rw [gn₂ _ (by omega) (by omega) (by omega) (by omega), r3]
  have p5 : c₂.nreg 4005 = j := by rw [gn₂ _ (by omega) (by omega) (by omega) (by omega), r5]
  obtain ⟨c₃, k₃, e₃, hk₃, h5, hn₃, hm₃, hr₃, hrm₃, ho₃⟩ : ∃ c₃ k₃,
      Exec P W (block [.addN 4005 4005 4003]) c₂ c₃ k₃ ∧ k₃ = 1 ∧ c₃.nreg 4005 = j + 1 ∧
      (∀ r, r ≠ 4005 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [p3, p5]); omega)
    refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [p3, p5]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₃, k₂ + k₃, .seq e₂ e₃, by omega, h5, by rw [hn₃ _ (by omega), g10],
    by rw [hn₃ _ (by omega), g11], fun r a b c d e => ?_, by rw [hm₃, gm₂],
    by rw [hr₃, gr₂], by rw [hrm₃, grm₂], by rw [ho₃, go₂]⟩
  rw [hn₃ r a, gn₂ r b c d e]

/-- **The two groups on the machine**: from the weights `WT[j] = nmem (Wb + j)`, `j < m`, and the
bound `A`, within `23 m + 15` steps, the first group `twoGroupsL ω A (List.range m)` is `[r4007]`
if `r4006 = 1`, else `List.range (min r4011 m)`. -/
theorem tgProg_exec (c : Config) (hc : WordsBounded W c) {m Wb A : ℕ}
    (r0 : c.nreg 4000 = m) (r1 : c.nreg 4001 = Wb) (r2 : c.nreg 4002 = A)
    (w1 : Wb + m ≤ W) (w2 : ∀ j < m, A + 2 * c.nmem (Wb + j) ≤ W) (w3 : m + 1 ≤ W) :
    ∃ c' t, Exec P W tgProg c c' t ∧ t ≤ 23 * m + 15 ∧
      twoGroupsL (fun j => c.nmem (Wb + j)) A (List.range m) =
        (if c'.nreg 4006 = 1 then [c'.nreg 4007] else List.range (min (c'.nreg 4011) m)) ∧
      (∀ r, (r < 4003 ∨ 4013 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tgProg
  set p : ℕ → Bool := fun j => decide (A < 2 * c.nmem (Wb + j)) with hp
  -- the constants
  obtain ⟨c₁, k₁, e₁, hk₁, g3, g4, g5, g6, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 4003 1, .constN 4004 0, .constN 4005 0, .constN 4006 0,
        .constN 4007 0]) c c₁ k₁ ∧ k₁ = 5 ∧ c₁.nreg 4003 = 1 ∧ c₁.nreg 4004 = 0 ∧
      c₁.nreg 4005 = 0 ∧ c₁.nreg 4006 = 0 ∧
      (∀ r, (r < 4003 ∨ 4007 < r) → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try config_simp
    simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  -- scan 1
  let J1 : ℕ → Config → Prop := fun i c' =>
    (∀ r, (r < 4005 ∨ 4009 < r) → c'.nreg r = c₁.nreg r) ∧ c'.nmem = c.nmem ∧
    c'.nreg 4006 = (if ((List.range i).find? p).isSome then 1 else 0) ∧
    (∀ h, (List.range i).find? p = some h → c'.nreg 4007 = h) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h5₂, j1, j2, j3, j4, j5, j6, j7⟩ := tgRange (P := P) (a := 4005)
    (b := 4000) (body := tgBody1) J1 (B := 9) c₁ hw₁ g5 (by rw [gn₁ _ (by omega), r0])
    (Nat.zero_le m)
    ⟨fun _ _ => rfl, gm₁, by simp [g6], fun h hh => by simp at hh, rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h5 h0 ⟨j1, j2, j3, j4, j5, j6, j7⟩ => by
      have q1 : c'.nreg 4001 = Wb := by rw [j1 _ (by omega), gn₁ _ (by omega), r1]
      have q2 : c'.nreg 4002 = A := by rw [j1 _ (by omega), gn₁ _ (by omega), r2]
      have q3 : c'.nreg 4003 = 1 := by rw [j1 _ (by omega), g3]
      have q4 : c'.nreg 4004 = 0 := by rw [j1 _ (by omega), g4]
      have hwi : c'.nmem (Wb + i) = c.nmem (Wb + i) := by rw [j2]
      have hf1 : c'.nreg 4006 ≤ 1 := by rw [j3]; split_ifs <;> omega
      obtain ⟨c'', t, ex, ht, h5', h6', h7', hn', hm', hr', hrm', ho'⟩ := tgBody1_exec (P := P)
        c' hw q1 q2 q3 q4 h5 rfl hf1 (by omega) (by have := w2 i hhi; rw [hwi]; omega)
        (by omega)
      rw [hwi] at h6' h7'
      refine ⟨c'', t, ex, ht, h5', by rw [hn' _ (by omega)]; exact h0,
        fun r hr => by rw [hn' r hr]; exact j1 r hr, by rw [hm', j2], ?_, ?_,
        by rw [hr', j5], by rw [hrm', j6], by rw [ho', j7]⟩
      · rw [h6', find?_range_succ]
        cases hfi : (List.range i).find? p with
        | some h =>
          have hf : c'.nreg 4006 = 1 := by rw [j3, hfi]; rfl
          have hn : ¬ tgHv A (c.nmem (Wb + i)) (c'.nreg 4006) :=
            fun h => by rw [hf] at h; exact absurd h.1 one_ne_zero
          rw [tgIteF hn, hf]; rfl
        | none =>
          have hf : c'.nreg 4006 = 0 := by rw [j3, hfi]; rfl
          by_cases hpi : p i = true
          · have hy : tgHv A (c.nmem (Wb + i)) (c'.nreg 4006) := ⟨hf, by simpa [hp] using hpi⟩
            rw [tgIteT hy]; simp [hpi]
          · have hn : ¬ tgHv A (c.nmem (Wb + i)) (c'.nreg 4006) :=
              fun h => hpi (by simpa [hp] using h.2)
            have hpf : p i = false := by simpa using hpi
            rw [tgIteF hn, hf]; simp [hpf]
      · intro h hh
        rw [h7']
        rw [find?_range_succ] at hh
        cases hfi : (List.range i).find? p with
        | some h₀ =>
          rw [hfi] at hh
          have hf : c'.nreg 4006 = 1 := by rw [j3, hfi]; rfl
          have hn : ¬ tgHv A (c.nmem (Wb + i)) (c'.nreg 4006) :=
            fun h => by rw [hf] at h; exact absurd h.1 one_ne_zero
          rw [tgIteF hn, j4 h₀ hfi]; simpa using hh
        | none =>
          rw [hfi] at hh
          have hf : c'.nreg 4006 = 0 := by rw [j3, hfi]; rfl
          by_cases hpi : p i = true
          · have hy : tgHv A (c.nmem (Wb + i)) (c'.nreg 4006) := ⟨hf, by simpa [hp] using hpi⟩
            rw [tgIteT hy]
            simp only [hpi, ↓reduceIte, Option.some.injEq] at hh; exact hh
          · simp only [hpi, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hh)
  have hw₂' := e₂.wb_right
  -- the second set-up
  obtain ⟨c₃, k₃, e₃, hk₃, g5', g10, g11, gn₃, gm₃, gr₃, grm₃, go₃⟩ : ∃ c₃ k₃,
      Exec P W (block [.constN 4005 0, .constN 4010 0, .constN 4011 0]) c₂ c₃ k₃ ∧ k₃ = 3 ∧
      c₃.nreg 4005 = 0 ∧ c₃.nreg 4010 = 0 ∧ c₃.nreg 4011 = 0 ∧
      (∀ r, r ≠ 4005 → r ≠ 4010 → r ≠ 4011 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try config_simp
    simp only [upd_apply]; split_ifs <;> omega
  have hw₃ := e₃.wb_right
  -- scan 2
  let J2 : ℕ → Config → Prop := fun i c' =>
    (∀ r, r ≠ 4005 → r ≠ 4008 → r ≠ 4010 → r ≠ 4011 → r ≠ 4013 → c'.nreg r = c₃.nreg r) ∧
    c'.nmem = c.nmem ∧
    pfx (fun j => c.nmem (Wb + j)) A (List.range i) 0 = List.range (c'.nreg 4011) ∧
    c'.nreg 4011 ≤ i ∧
    c'.nreg 4010 = ((List.range (c'.nreg 4011)).map fun j => c.nmem (Wb + j)).sum ∧
    c'.nreg 4010 ≤ A ∧ c'.rreg = c₃.rreg ∧ c'.rmem = c₃.rmem ∧ c'.output = c₃.output
  have q0₃ : c₃.nreg 4000 = m := by
    rw [gn₃ _ (by omega) (by omega) (by omega), j1 _ (by omega), gn₁ _ (by omega), r0]
  obtain ⟨c₄, k₄, e₄, hk₄, hw₄, h5₄, i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ := tgRange (P := P)
    (a := 4005) (b := 4000) (body := tgBody2) J2 (B := 10) c₃ hw₃ g5' q0₃ (Nat.zero_le m)
    ⟨fun _ _ _ _ _ _ => rfl, by rw [gm₃, j2], by rw [g11]; rfl, by rw [g11],
      by rw [g10, g11]; rfl, by rw [g10]; exact Nat.zero_le _, rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h5 h0 ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ => by
      have f1 : c'.nreg 4001 = Wb := by
        rw [i1 _ (by omega) (by omega) (by omega) (by omega) (by omega),
          gn₃ _ (by omega) (by omega) (by omega), j1 _ (by omega), gn₁ _ (by omega), r1]
      have f2 : c'.nreg 4002 = A := by
        rw [i1 _ (by omega) (by omega) (by omega) (by omega) (by omega),
          gn₃ _ (by omega) (by omega) (by omega), j1 _ (by omega), gn₁ _ (by omega), r2]
      have f3 : c'.nreg 4003 = 1 := by
        rw [i1 _ (by omega) (by omega) (by omega) (by omega) (by omega),
          gn₃ _ (by omega) (by omega) (by omega), j1 _ (by omega), g3]
      have hwi : c'.nmem (Wb + i) = c.nmem (Wb + i) := by rw [i2]
      obtain ⟨c'', t, ex, ht, h5', h10', h11', hn', hm', hr', hrm', ho'⟩ := tgBody2_exec
        (P := P) c' hw f1 f2 f3 h5 rfl rfl i6 i4 (by omega)
        (by have := w2 i hhi; rw [hwi]; omega) (by omega)
      rw [hwi] at h10' h11'
      have h0' : c''.nreg 4000 = m := by
        rw [hn' _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h0
      have hfr : ∀ r, r ≠ 4005 → r ≠ 4008 → r ≠ 4010 → r ≠ 4011 → r ≠ 4013 →
          c''.nreg r = c₃.nreg r := fun r a b d e f => by
        rw [hn' r a b d e f]; exact i1 r a b d e f
      obtain ⟨t1, t2, t3, t4⟩ := tgStep2 (fun j => c.nmem (Wb + j)) A i3 i4 i5 i6
      refine ⟨c'', t, ex, ht, h5', h0', hfr, by rw [hm', i2], ?_, ?_, ?_, ?_, by rw [hr', i7],
        by rw [hrm', i8], by rw [ho', i9]⟩
      · rw [h11']; exact t1
      · rw [h11']; exact t2
      · rw [h10', h11']; exact t3
      · rw [h10']; exact t4)
  -- the fix
  have hw₄' := e₄.wb_right
  obtain ⟨c₅, k₅, e₅, hk₅, h11₅, gn₅, gm₅, gr₅, grm₅, go₅⟩ : ∃ c₅ k₅,
      Exec P W tgFix c₄ c₅ k₅ ∧ k₅ ≤ 3 ∧
      c₅.nreg 4011 = (if c₄.nreg 4011 < m then c₄.nreg 4011 else 1) ∧
      (∀ r, r ≠ 4011 → c₅.nreg r = c₄.nreg r) ∧ c₅.nmem = c₄.nmem ∧
      c₅.rreg = c₄.rreg ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output := by
    have h0₄ : c₄.nreg 4000 = m := by
      rw [i1 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact q0₃
    unfold tgFix
    by_cases hk : c₄.nreg 4011 < c₄.nreg 4000
    · refine ⟨c₄, 1, .ifLtN_true hk (.skip hw₄), by omega, ?_, fun r _ => rfl, rfl, rfl, rfl,
        rfl⟩
      rw [h0₄] at hk; rw [tgIteT hk]
    · refine ⟨_, _, .ifLtN_false hk (Exec.constN hw₄ 4011 1 (by omega)), le_refl _, ?_,
        fun r hr => ?_, rfl, rfl, rfl, rfl⟩
      · rw [h0₄] at hk; rw [tgIteF hk]; config_simp
      · config_simp; simp only [upd_apply]; split_ifs <;> omega
  -- the frame
  have fr : ∀ r, r ≠ 4005 → r ≠ 4008 → r ≠ 4010 → r ≠ 4011 → r ≠ 4013 →
      c₅.nreg r = c₂.nreg r := fun r a b d e f => by
    rw [gn₅ r e, i1 r a b d e f, gn₃ r a d e]
  have e6 : c₅.nreg 4006 = c₂.nreg 4006 := fr _ (by omega) (by omega) (by omega) (by omega)
    (by omega)
  have e7 : c₅.nreg 4007 = c₂.nreg 4007 := fr _ (by omega) (by omega) (by omega) (by omega)
    (by omega)
  refine ⟨c₅, k₁ + (k₂ + (k₃ + (k₄ + k₅))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), ?_, ?_,
    fun r hr => ?_, by rw [gm₅, i2], by rw [gr₅, i7, gr₃, j5, gr₁],
    by rw [grm₅, i8, grm₃, j6, grm₁], by rw [go₅, i9, go₃, j7, go₁]⟩
  · have : (11 : ℕ) * m + 2 + (12 * m + 2) = 23 * m + 4 := by ring
    simp only [Nat.sub_zero] at hk₂ hk₄
    omega
  · unfold twoGroupsL
    have hfi' : List.find? (fun i => decide (A < 2 * c.nmem (Wb + i))) (List.range m) =
        (List.range m).find? p := rfl
    rw [hfi', e6, e7]
    cases hfi : (List.range m).find? p with
    | some h =>
      have hf : c₂.nreg 4006 = 1 := by rw [j3, hfi]; rfl
      rw [hf, tgIteT rfl, j4 h hfi]
    | none =>
      have hf : c₂.nreg 4006 = 0 := by rw [j3, hfi]; rfl
      rw [hf, tgIteF (show ¬ (0 : ℕ) = 1 by omega), h11₅]
      simp only [i3, List.length_range]
      by_cases hkm : c₄.nreg 4011 < m
      · rw [tgIteF (by omega : ¬ c₄.nreg 4011 = m), tgIteT hkm, Nat.min_eq_left hkm.le]
      · have hk' : c₄.nreg 4011 = m := by omega
        rw [tgIteT hk', tgIteF hkm, List.take_range]
  · rcases hr with hr | hr
    · rw [fr r (by omega) (by omega) (by omega) (by omega) (by omega), j1 r (by omega),
        gn₁ r (by omega)]
    · rw [fr r (by omega) (by omega) (by omega) (by omega) (by omega), j1 r (by omega),
        gn₁ r (by omega)]

/-- **The two groups of any list on the machine**: for items `g 0, …, g (m-1)` whose weights
`ω (g j)` are stored at `Wb + j`, the run of `tgProg` gives `twoGroupsL ω A` of the list:
`[g r4007]` if `r4006 = 1`, else the first `min r4011 m` items. -/
theorem tgProg_exec_list {ι : Type*} (c : Config) (hc : WordsBounded W c) {m Wb A : ℕ}
    (r0 : c.nreg 4000 = m) (r1 : c.nreg 4001 = Wb) (r2 : c.nreg 4002 = A)
    (w1 : Wb + m ≤ W) (w2 : ∀ j < m, A + 2 * c.nmem (Wb + j) ≤ W) (w3 : m + 1 ≤ W)
    (g : ℕ → ι) (ω : ι → ℕ) (hm : ∀ j < m, c.nmem (Wb + j) = ω (g j)) :
    ∃ c' t, Exec P W tgProg c c' t ∧ t ≤ 23 * m + 15 ∧
      twoGroupsL ω A ((List.range m).map g) =
        (if c'.nreg 4006 = 1 then [g (c'.nreg 4007)]
          else (List.range (min (c'.nreg 4011) m)).map g) ∧
      (∀ r, (r < 4003 ∨ 4013 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', t, e, ht, hg, rest⟩ := tgProg_exec (P := P) c hc r0 r1 r2 w1 w2 w3
  refine ⟨c', t, e, ht, ?_, rest⟩
  rw [twoGroupsL_map, twoGroupsL_congr A (ω := ω ∘ g) (ω' := fun j => c.nmem (Wb + j))
    (fun j hj => (hm j (List.mem_range.1 hj)).symm), hg]
  split_ifs <;> rfl

end Exec

end BKMNW

end PlanarFlow
