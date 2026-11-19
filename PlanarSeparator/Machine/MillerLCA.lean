module

public import PlanarSeparator.Machine.MillerRoot

/-!
# Miller's separator on the machine: lowest common ancestors by binary lifting

Part of step 8 of the plan in `PlanarSeparator/Machine/Miller.lean`. A rooted tree on the
vertices `0, …, n - 1` is given numerically by its parent function `f` (the root `r₀` fixed) and
its depths `dep` (`PTree`); `PlanarSeparator/Machine/MillerRoot.lean` stores both (`rspass`), the
parents at `bU`.

* `lgprog` computes `L ≥ 1` with `n ≤ 2 ^ L` and `L ≤ log₂ n + 1` (`lgprog_exec`, within
  `4 log₂ n + 4` steps);
* `tbuild` fills the table of the `2 ^ j`-th ancestors, `f^[2 ^ j] v` at `bU + j n + v` for
  `j < L` (`Tab`; `tbuild_exec`, within `(9 n + 8) L + 5` steps, so `O(n log n)`);
* `lcaq` answers a query: from two vertices `u`, `v` it returns their lowest common ancestor,
  lifting the deeper one to the depth of the other and then both together while their ancestors
  differ (`lcaq_exec`, within `25 L + 26` steps, so `O(log n)`). The result `l` is the lowest
  common ancestor in the numeric sense `IsLCA` (an ancestor of both, below every common
  ancestor), which determines it (`IsLCA.unique`).

The bridge: for a spanning tree `T` with its vertices numbered by `vi` (parents and depths as
stored by `rspass_tree`), `IsLCA` of the numbers of `x`, `y` means the deepest common ancestor
(`isLCA_tree`), and for the two ends of a dart `δ` it is `lca T δ` of
`PlanarSeparator/SimpleCycle.lean` (`isLCA_lca`, through `anc_inter_anc`).

Registers: `r140 = 0`, `r141 = 1`, `r161 = n`, `r253 = bD`, `r254 = bU`; `lgprog` writes
`r270`, `r271 = L`; `tbuild` writes `r272 … r278`; `lcaq` reads `u = r280`, `v = r281`, writes
`r282` (the answer) and `r280 … r291`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### Numeric trees -/

/-- A rooted tree on `0, …, n - 1`: the parent function `f` fixes the root `r₀` and lowers the
depth by one elsewhere. -/
structure PTree (n r₀ : ℕ) (f dep : ℕ → ℕ) : Prop where
  r₀_lt : r₀ < n
  f_lt : ∀ v < n, f v < n
  f_r₀ : f r₀ = r₀
  dep_r₀ : dep r₀ = 0
  dep_f : ∀ v < n, v ≠ r₀ → dep (f v) + 1 = dep v
  dep_lt : ∀ v < n, dep v < n

/-- `a` is an ancestor of `v`. -/
def IsAnc (f : ℕ → ℕ) (a v : ℕ) : Prop := ∃ m, f^[m] v = a

/-- `l` is the lowest common ancestor of `u` and `v`: a common ancestor below every common
ancestor. -/
def IsLCA (f : ℕ → ℕ) (u v l : ℕ) : Prop :=
  IsAnc f l u ∧ IsAnc f l v ∧ ∀ a, IsAnc f a u → IsAnc f a v → IsAnc f a l

theorem IsLCA.symm {f : ℕ → ℕ} {u v l : ℕ} (h : IsLCA f u v l) : IsLCA f v u l :=
  ⟨h.2.1, h.1, fun a h1 h2 => h.2.2 a h2 h1⟩

section PTree

variable {n r₀ : ℕ} {f dep : ℕ → ℕ} (hT : PTree n r₀ f dep)
include hT

theorem PTree.iter_lt (m : ℕ) {v : ℕ} (hv : v < n) : f^[m] v < n := by
  induction m generalizing v with
  | zero => exact hv
  | succ m ih => rw [Function.iterate_succ_apply]; exact ih (hT.f_lt v hv)

theorem PTree.dep_iter (m : ℕ) {v : ℕ} (hv : v < n) : dep (f^[m] v) = dep v - m := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih (hT.f_lt v hv)]
    by_cases h : v = r₀
    · subst h; rw [hT.f_r₀, hT.dep_r₀]; simp
    · have := hT.dep_f v hv h; omega

theorem PTree.eq_r₀ {v : ℕ} (hv : v < n) (h : dep v = 0) : v = r₀ := by
  by_contra hne
  have := hT.dep_f v hv hne; omega

theorem PTree.iter_r₀ (m : ℕ) : f^[m] r₀ = r₀ := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, hT.f_r₀, ih]

theorem PTree.iter_of_le {v m : ℕ} (hv : v < n) (hm : dep v ≤ m) : f^[m] v = r₀ :=
  hT.eq_r₀ (hT.iter_lt m hv) (by rw [hT.dep_iter m hv]; omega)

/-- Ancestors of each other are equal. -/
theorem PTree.anc_antisymm {a b : ℕ} (hb : b < n) (h1 : IsAnc f a b) (h2 : IsAnc f b a) :
    a = b := by
  obtain ⟨m, rfl⟩ := h1
  obtain ⟨m', hm'⟩ := h2
  rw [← Function.iterate_add_apply] at hm'
  have hd := hT.dep_iter (m' + m) hb
  rw [hm'] at hd
  by_cases h0 : m = 0
  · subst h0; rfl
  · have hd0 : dep b = 0 := by omega
    have := hT.eq_r₀ hb hd0
    subst this
    exact hT.iter_r₀ m

/-- **The lowest common ancestor is unique.** -/
theorem IsLCA.unique {u v l l' : ℕ} (hu : u < n) (h : IsLCA f u v l) (h' : IsLCA f u v l') :
    l = l' := by
  have hl : l' < n := by obtain ⟨m, rfl⟩ := h'.1; exact hT.iter_lt m hu
  have e1 : IsAnc f l l' := h'.2.2 l h.1 h.2.1
  have e2 : IsAnc f l' l := h.2.2 l' h'.1 h'.2.1
  exact hT.anc_antisymm hl e1 e2

/-- **The lifted vertices.** Let `u₁ = f^[s] u₀` be at the depth of `v₀`, and `t` the last number
of steps up from `u₁` and `v₀` at which they still differ. Then the parent of `f^[t] u₁` is the
lowest common ancestor of `u₀` and `v₀`. -/
theorem PTree.isLCA_of_lift {u₀ v₀ s t : ℕ} (hu : u₀ < n) (hv : v₀ < n)
    (hd : dep (f^[s] u₀) = dep v₀) (hne : f^[t] (f^[s] u₀) ≠ f^[t] v₀)
    (heq : f^[t + 1] (f^[s] u₀) = f^[t + 1] v₀) : IsLCA f u₀ v₀ (f^[t + 1] (f^[s] u₀)) := by
  generalize hu₁' : f^[s] u₀ = u₁ at hd hne heq ⊢
  have hu₁ : u₁ = f^[s] u₀ := hu₁'.symm
  have hu₁n : u₁ < n := hu₁ ▸ hT.iter_lt s hu
  -- the two vertices `f^[t] u₁`, `f^[t] v₀` are not the root
  have hdt : dep (f^[t] u₁) = dep (f^[t] v₀) := by
    rw [hT.dep_iter t hu₁n, hT.dep_iter t hv, hd]
  have hpos : 0 < dep (f^[t] v₀) := by
    by_contra h0
    have e1 := hT.eq_r₀ (hT.iter_lt t hv) (by omega)
    have e2 := hT.eq_r₀ (hT.iter_lt t hu₁n) (by omega)
    exact hne (e2.trans e1.symm)
  have htv : t < dep v₀ := by rw [hT.dep_iter t hv] at hpos; omega
  have hsu : s ≤ dep u₀ := by
    by_contra hs
    have : dep u₁ = 0 := by rw [hu₁, hT.dep_iter s hu]; omega
    omega
  refine ⟨⟨t + 1 + s, by rw [Function.iterate_add_apply, hu₁]⟩, ⟨t + 1, heq.symm⟩, ?_⟩
  rintro a ⟨p, rfl⟩ ⟨q, hq⟩
  by_cases hp : t + 1 + s ≤ p
  · refine ⟨p - (t + 1 + s), ?_⟩
    rw [hu₁, ← Function.iterate_add_apply, ← Function.iterate_add_apply]
    congr 1; omega
  · exfalso
    have hdp := hT.dep_iter p hu
    have hdq := hT.dep_iter q hv
    rw [hq] at hdq
    by_cases hps : p < s
    · -- above the depth of `v₀`: impossible
      have : dep u₁ = dep u₀ - s := hu₁ ▸ hT.dep_iter s hu
      omega
    · -- `a = f^[p - s] u₁ = f^[q] v₀` with `q = p - s ≤ t`
      have ha : f^[p] u₀ = f^[p - s] u₁ := by
        rw [hu₁, ← Function.iterate_add_apply]; congr 1; omega
      have hqe : q = p - s := by
        have : dep u₁ = dep u₀ - s := hu₁ ▸ hT.dep_iter s hu
        omega
      apply hne
      have e1 : f^[t] u₁ = f^[t - (p - s)] (f^[p - s] u₁) := by
        rw [← Function.iterate_add_apply]; congr 1; omega
      have e2 : f^[t] v₀ = f^[t - q] (f^[q] v₀) := by
        rw [← Function.iterate_add_apply]; congr 1; omega
      rw [e1, e2, ← ha, hq, hqe]

/-- The lifted vertex is the other vertex: it is the lowest common ancestor. -/
theorem PTree.isLCA_of_eq {u₀ v₀ s : ℕ} (h : f^[s] u₀ = v₀) : IsLCA f u₀ v₀ v₀ :=
  ⟨⟨s, h⟩, ⟨0, rfl⟩, fun _ _ ha => ha⟩

end PTree

theorem iter_lt_of {n : ℕ} {f : ℕ → ℕ} (hf : ∀ v < n, f v < n) (m : ℕ) {v : ℕ} (hv : v < n) :
    f^[m] v < n := by
  induction m generalizing v with
  | zero => exact hv
  | succ m ih => rw [Function.iterate_succ_apply]; exact ih (hf v hv)

theorem iter_two_pow {f : ℕ → ℕ} {j : ℕ} (hj : 1 ≤ j) (v : ℕ) :
    f^[2 ^ (j - 1)] (f^[2 ^ (j - 1)] v) = f^[2 ^ j] v := by
  rw [← Function.iterate_add_apply]
  congr 1
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]; ring

/-! ### The programs -/

/-- **`L`**: the least `L ≥ 1` with `n ≤ 2 ^ L` (`r271`; `r270 = 2 ^ L`). -/
def lgprog : Stmt :=
  .seq (block [.constN 270 2, .copyN 271 141])
    (.whileLtN 270 161 (block [.addN 270 270 270, .addN 271 271 141]))

/-- **One vertex** `r275 = v` of level `j` of the table: `U_j v := U_{j-1} (U_{j-1} v)`, the
level `j - 1` at `r272`, the level `j` at `r273`. -/
def tinner : Stmt :=
  block [.addN 276 272 275, .loadN 277 276, .addN 276 272 277, .loadN 278 276,
    .addN 276 273 275, .storeN 276 278, .addN 275 275 141]

/-- **One level** `r274 = j` of the table. -/
def touter : Stmt :=
  .seq (.instr (.copyN 275 140))
    (.seq (.whileLtN 275 161 tinner) (block [.copyN 272 273, .addN 273 273 161, .addN 274 274 141]))

/-- **The table of the `2 ^ j`-th ancestors**, levels `1 ≤ j < L` (level `0`, the parents, at
`bU`). -/
def tbuild : Stmt :=
  .seq (block [.copyN 272 254, .addN 273 254 161, .copyN 274 141]) (.whileLtN 274 271 touter)

/-- The table: `f^[2 ^ j] v` at `bU + j n + v`. -/
def Tab (n bU L : ℕ) (f : ℕ → ℕ) (m : ℕ → ℕ) : Prop :=
  ∀ j < L, ∀ v < n, m (bU + j * n + v) = f^[2 ^ j] v

section proofs

variable {W : ℕ} {P : Input} {n bU L : ℕ} {f : ℕ → ℕ}

/-- **The number of levels.** Within `4 log₂ n + 4` steps, `r271 = L` with `1 ≤ L`,
`n ≤ 2 ^ L` and `L ≤ log₂ n + 1`. -/
theorem lgprog_exec (hW : 2 * n + 2 ≤ W) (c : Config) (hc : WordsBounded W c)
    (h141 : c.nreg 141 = 1) (h161 : c.nreg 161 = n) :
    ∃ c' t, Exec P W lgprog c c' t ∧ t ≤ 4 * Nat.log 2 n + 4 ∧ 1 ≤ c'.nreg 271 ∧
      n ≤ 2 ^ c'.nreg 271 ∧ c'.nreg 271 ≤ Nat.log 2 n + 1 ∧
      (∀ r, r ≠ 270 → r ≠ 271 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.output = c.output := by
  let I : Config → Prop := fun c' => WordsBounded W c' ∧ c'.nreg 270 = 2 ^ c'.nreg 271 ∧
    1 ≤ c'.nreg 271 ∧ (c'.nreg 271 = 1 ∨ 2 ^ (c'.nreg 271 - 1) < n) ∧
    (∀ r, r ≠ 270 → r ≠ 271 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.output = c.output
  have hlog : ∀ L, (L = 1 ∨ 2 ^ (L - 1) < n) → 1 ≤ L → L ≤ Nat.log 2 n + 1 := fun L h h1 => by
    rcases h with rfl | h
    · omega
    · have := Nat.le_log_of_pow_le (b := 2) (by omega) h.le; omega
  obtain ⟨c₁, k₁, e₁, hI₁, h271, rfl⟩ : ∃ c₁ k₁, Exec P W (block [.constN 270 2, .copyN 271 141])
      c c₁ k₁ ∧ I c₁ ∧ c₁.nreg 271 = 1 ∧ k₁ = 2 := by
    exec_block
    · omega
    refine ⟨⟨‹_›, by config_simp; rw [h141]; rfl, by config_simp; omega,
      Or.inl (by config_simp; exact h141), fun r a b => by config_simp; rw [upd_other _ _ _ b,
        upd_other _ _ _ a], rfl, rfl⟩, by config_simp; exact h141, rfl⟩
  obtain ⟨c', k', e, hI', hn, hk'⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 270) (b := 161)
    (body := block [.addN 270 270 270, .addN 271 271 141]) I
    (fun c => 4 * (Nat.log 2 n + 1 - c.nreg 271)) (fun c h => h.1)
    (fun c' ⟨hw, h270, h1, hd, hr, hm, ho⟩ hlt => by
      have g161 : c'.nreg 161 = n := (hr 161 (by omega) (by omega)).trans h161
      have g141 : c'.nreg 141 = 1 := (hr 141 (by omega) (by omega)).trans h141
      rw [g161, h270] at hlt
      have hL := Nat.le_log_of_pow_le (b := 2) (by omega) hlt.le
      have hL' : c'.nreg 271 < 2 ^ c'.nreg 271 := Nat.lt_two_pow_self
      have hc := hw
      exec_block
      · config_simp; rw [h270]; omega
      · config_simp; rw [g141]; omega
      refine ⟨⟨‹_›, ?_, by config_simp; rw [g141]; omega, Or.inr ?_, fun r a b => ?_, hm, ho⟩, ?_⟩
      all_goals config_simp
      · rw [g141, h270, pow_succ]; ring
      · rw [g141, Nat.add_sub_cancel]; exact hlt
      · rw [upd_other _ _ _ b, upd_other _ _ _ a]; exact hr r a b
      · rw [g141]; omega) hI₁
  obtain ⟨hw', h270', h1', hd', hr', hm', ho'⟩ := hI'
  have g161 : c'.nreg 161 = n := (hr' 161 (by omega) (by omega)).trans h161
  rw [g161, h270'] at hn
  refine ⟨c', 2 + k', .seq e₁ e, ?_, h1', by omega, hlog _ hd' h1', hr', hm', ho'⟩
  rw [h271] at hk'
  omega

/-- The state of the inner loop of level `j`, from the state `cₒ` at the start of the level. -/
structure TI (cₒ : Config) (j v : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  r275 : c.nreg 275 = v
  le : v ≤ n
  regs : ∀ r, r < 275 ∨ 279 ≤ r → c.nreg r = cₒ.nreg r
  mem : ∀ a, a < bU + j * n ∨ bU + j * n + n ≤ a → c.nmem a = cₒ.nmem a
  out : c.output = cₒ.output
  done : ∀ u < v, c.nmem (bU + j * n + u) = f^[2 ^ j] u

/-- The state of the outer loop at level `j`, from the start `c₀`. -/
structure TO (c₀ : Config) (j : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  r274 : c.nreg 274 = j
  pos : 1 ≤ j
  le : j ≤ L
  r272 : c.nreg 272 = bU + (j - 1) * n
  r273 : c.nreg 273 = bU + j * n
  regs : ∀ r, r < 272 ∨ 279 ≤ r → c.nreg r = c₀.nreg r
  mem : ∀ a, a < bU + n ∨ bU + L * n ≤ a → c.nmem a = c₀.nmem a
  out : c.output = c₀.output
  tab : Tab n bU j f c.nmem

variable (hn : 1 ≤ n) (hf : ∀ v < n, f v < n) (hW : bU + L * n ≤ W)
include hn hf hW

theorem tinner_exec {c₀ cₒ : Config} (h141 : c₀.nreg 141 = 1) {j : ℕ}
    (hO : TO (W := W) (n := n) (bU := bU) (L := L) (f := f) c₀ j cₒ) (hj : j < L) (v : ℕ)
    (c : Config) (hI : TI (W := W) (n := n) (bU := bU) (f := f) cₒ j v c) (hv : v < n) :
    ∃ c' t, Exec P W tinner c c' t ∧ TI (W := W) (n := n) (bU := bU) (f := f) cₒ j (v + 1) c' ∧
      t ≤ 7 := by
  have hc := hI.wb
  have g272 : c.nreg 272 = bU + (j - 1) * n := (hI.regs 272 (by omega)).trans hO.r272
  have g273 : c.nreg 273 = bU + j * n := (hI.regs 273 (by omega)).trans hO.r273
  have g141 : c.nreg 141 = 1 := ((hI.regs 141 (by omega)).trans (hO.regs 141 (by omega))).trans h141
  have hj1 := hO.pos
  have hjn : (j - 1) * n + n = j * n := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hj1]
  have hjL : j * n + n ≤ L * n := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
  have hfv : f^[2 ^ (j - 1)] v < n := iter_lt_of hf _ hv
  have m1 : c.nmem (bU + (j - 1) * n + v) = f^[2 ^ (j - 1)] v := by
    rw [hI.mem _ (Or.inl (by omega))]; exact hO.tab (j - 1) (by omega) v hv
  have m2 : c.nmem (bU + (j - 1) * n + f^[2 ^ (j - 1)] v) = f^[2 ^ j] v := by
    rw [hI.mem _ (Or.inl (by omega)), hO.tab (j - 1) (by omega) _ hfv, iter_two_pow hj1]
  unfold tinner
  exec_block
  all_goals try (config_simp; simp only [g272, g273, g141, hI.r275, m1, m2]; omega)
  refine ⟨⟨‹_›, ?_, by omega, fun r hr => ?_, fun a ha => ?_, hI.out, fun u hu => ?_⟩, le_rfl⟩
  all_goals config_simp
  · rw [g141, hI.r275]
  · simp only [upd_apply]; split_ifs <;> first | omega | exact hI.regs r hr
  · simp only [g272, g273, hI.r275, m1, m2]
    rw [upd_other _ _ _ (by omega)]; exact hI.mem a ha
  · simp only [g272, g273, hI.r275, m1, m2]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
    · rw [upd_other _ _ _ (by omega)]; exact hI.done u hu
    · rw [upd_same]

theorem touter_exec {c₀ : Config} (h140 : c₀.nreg 140 = 0) (h141 : c₀.nreg 141 = 1)
    (h161 : c₀.nreg 161 = n) {j : ℕ} (c : Config)
    (hO : TO (W := W) (n := n) (bU := bU) (L := L) (f := f) c₀ j c) (hj : j < L) :
    ∃ c' t, Exec P W touter c c' t ∧ TO (W := W) (n := n) (bU := bU) (L := L) (f := f) c₀ (j + 1) c' ∧
      t ≤ 9 * n + 6 := by
  have hc := hO.wb
  have hj1 := hO.pos
  have hjn : (j - 1) * n + n = j * n := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hj1]
  have hjL : j * n + n ≤ L * n := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
  have e₁ := Exec.copyN (P := P) hc 275 140
  have hI₁ : TI (W := W) (n := n) (bU := bU) (f := f) c j 0
      { c with nreg := upd c.nreg 275 (c.nreg 140) } := by
    refine ⟨e₁.wb_right, ?_, by omega, fun r hr => ?_, fun a _ => rfl, rfl,
      fun u hu => absurd hu (by omega)⟩
    all_goals config_simp
    · rw [hO.regs 140 (by omega)]; exact h140
    · rw [upd_other _ _ _ (by omega)]
  obtain ⟨c₂, t₂, e₂, hI₂, ht₂⟩ := Exec.forN (P := P) (W := W) (ri := 275) (rN := 161) (N := n)
    (lo := 0) (B := 7) (body := tinner) (TI (W := W) (n := n) (bU := bU) (f := f) c j)
    (fun v c' h => ⟨h.wb, h.r275, by rw [h.regs 161 (by omega), hO.regs 161 (by omega)]; exact h161⟩)
    (fun v c' h hv => tinner_exec hn hf hW h141 hO hj v c' h hv) (by omega) hI₁
  have hc₂ := hI₂.wb
  have g273 : c₂.nreg 273 = bU + j * n := (hI₂.regs 273 (by omega)).trans hO.r273
  have g274 : c₂.nreg 274 = j := (hI₂.regs 274 (by omega)).trans hO.r274
  have g161 : c₂.nreg 161 = n := (hI₂.regs 161 (by omega)).trans ((hO.regs 161 (by omega)).trans h161)
  have g141 : c₂.nreg 141 = 1 := (hI₂.regs 141 (by omega)).trans ((hO.regs 141 (by omega)).trans h141)
  obtain ⟨c₃, t₃, e₃, hO₃, rfl⟩ : ∃ c₃ t₃, Exec P W
      (block [.copyN 272 273, .addN 273 273 161, .addN 274 274 141]) c₂ c₃ t₃ ∧
      TO (W := W) (n := n) (bU := bU) (L := L) (f := f) c₀ (j + 1) c₃ ∧ t₃ = 3 := by
    exec_block
    · config_simp; rw [g273, g161]; omega
    · config_simp; rw [g274, g141]
      have : L ≤ L * n := Nat.le_mul_of_pos_right L hn
      omega
    refine ⟨⟨‹_›, ?_, by omega, by omega, ?_, ?_, fun r hr => ?_, fun a ha => ?_, ?_, ?_⟩, rfl⟩
    all_goals config_simp
    · rw [g274, g141]
    · rw [g273, Nat.add_sub_cancel]
    · rw [g273, g161, add_assoc, ← Nat.succ_mul]
    · simp only [upd_apply]; split_ifs <;> first | omega | (rw [hI₂.regs r (by omega)]; exact hO.regs r hr)
    · rw [hI₂.mem a (by omega)]; exact hO.mem a ha
    · rw [hI₂.out]; exact hO.out
    · intro i hi u hu
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [hI₂.mem _ (Or.inl (by
          have : i * n + n ≤ j * n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
          omega))]
        exact hO.tab i hi u hu
      · exact hI₂.done u hu
  exact ⟨c₃, 1 + (t₂ + 3), .seq e₁ (.seq e₂ e₃), hO₃, by omega⟩

/-- **The table.** From the parents `f` at `bU` (level `0`), `tbuild` fills the levels
`1 ≤ j < L` of the table of the `2 ^ j`-th ancestors, within `(9 n + 8) L + 5` steps. -/
theorem tbuild_exec (hL : 1 ≤ L) (c : Config) (hc : WordsBounded W c) (h140 : c.nreg 140 = 0)
    (h141 : c.nreg 141 = 1) (h161 : c.nreg 161 = n) (h254 : c.nreg 254 = bU)
    (h271 : c.nreg 271 = L) (h0 : ∀ v < n, c.nmem (bU + v) = f v) :
    ∃ c' t, Exec P W tbuild c c' t ∧ t ≤ (9 * n + 8) * L + 5 ∧ Tab n bU L f c'.nmem ∧
      (∀ r, r < 272 ∨ 279 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bU + n ∨ bU + L * n ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  have hnL : n ≤ L * n := Nat.le_mul_of_pos_left n hL
  obtain ⟨c₁, t₁, e₁, hO₁, rfl⟩ : ∃ c₁ t₁, Exec P W
      (block [.copyN 272 254, .addN 273 254 161, .copyN 274 141]) c c₁ t₁ ∧
      TO (W := W) (n := n) (bU := bU) (L := L) (f := f) c 1 c₁ ∧ t₁ = 3 := by
    exec_block
    · config_simp; rw [h254, h161]; omega
    refine ⟨⟨‹_›, ?_, le_rfl, hL, ?_, ?_, fun r hr => ?_, fun a _ => rfl, rfl, ?_⟩, rfl⟩
    all_goals config_simp
    · exact h141
    · rw [h254]; simp
    · rw [h254, h161]; simp
    · simp only [upd_apply]; split_ifs <;> first | omega | rfl
    · intro j hj v hv
      obtain rfl : j = 0 := by omega
      simp only [zero_mul, add_zero, pow_zero, Function.iterate_one]
      exact h0 v hv
  obtain ⟨c', t, e, hO', ht⟩ := Exec.forN (P := P) (W := W) (ri := 274) (rN := 271) (N := L)
    (lo := 1) (B := 9 * n + 6) (body := touter) (TO (W := W) (n := n) (bU := bU) (L := L) (f := f) c)
    (fun j c' h => ⟨h.wb, h.r274, by rw [h.regs 271 (by omega)]; exact h271⟩)
    (fun j c' h hj => touter_exec hn hf hW h140 h141 h161 c' h hj) hL hO₁
  refine ⟨c', 3 + t, .seq e₁ e, ?_, hO'.tab, hO'.regs, hO'.mem, hO'.out⟩
  have : (9 * n + 6 + 2) * (L - 1) ≤ (9 * n + 8) * L := Nat.mul_le_mul_left _ (by omega)
  omega

end proofs

/-! ### The query -/

/-- The depths `r283 = dep u`, `r284 = dep v` of the arguments `u = r280`, `v = r281`. -/
def qload : Stmt := block [.addN 289 253 280, .loadN 283 289, .addN 289 253 281, .loadN 284 289]

/-- Exchange the two arguments and their depths. -/
def qswap : Stmt :=
  block [.copyN 285 280, .copyN 280 281, .copyN 281 285, .copyN 285 283, .copyN 283 284,
    .copyN 284 285]

/-- `r286 = L`, `r287 = bU + L n`. -/
def qinit : Stmt := block [.copyN 286 271, .mulN 287 271 161, .addN 287 287 254]

/-- **One level of the lifting**: `r286 = j` decreases, and `u = r280` moves up by `2 ^ j` unless
it would rise above the depth `r284` of `v`. -/
def lstep : Stmt :=
  .seq (block [.subN 286 286 141, .subN 287 287 161, .addN 289 287 280, .loadN 290 289,
      .addN 289 253 290, .loadN 291 289])
    (.ifLtN 291 284 .skip (.instr (.copyN 280 290)))

/-- **Lift `u` to the depth of `v`.** -/
def lift : Stmt := .seq qinit (.whileLtN 140 286 lstep)

/-- **One level of the joint jump**: both move up by `2 ^ j` if they land on distinct vertices. -/
def jstep : Stmt :=
  .seq (block [.subN 286 286 141, .subN 287 287 161, .addN 289 287 280, .loadN 290 289,
      .addN 289 287 281, .loadN 291 289])
    (.ifLtN 290 291 (block [.copyN 280 290, .copyN 281 291])
      (.ifLtN 291 290 (block [.copyN 280 290, .copyN 281 291]) .skip))

/-- **The joint jump**, then the parent of `u` in `r282`. -/
def jump : Stmt :=
  .seq qinit (.seq (.whileLtN 140 286 jstep) (block [.addN 289 254 280, .loadN 282 289]))

/-- **The lowest common ancestor** of `r280` and `r281`, in `r282`. -/
def lcaq : Stmt :=
  .seq (.seq qload (.ifLtN 283 284 qswap .skip))
    (.seq lift (.ifLtN 280 281 jump (.ifLtN 281 280 jump (.instr (.copyN 282 280)))))

/-- The registers and the memory read by a query, and the facts on the tree. -/
structure QFix (n r₀ bD bU L W : ℕ) (f dep : ℕ → ℕ) (c : Config) : Prop where
  r140 : c.nreg 140 = 0
  r141 : c.nreg 141 = 1
  r161 : c.nreg 161 = n
  r253 : c.nreg 253 = bD
  r254 : c.nreg 254 = bU
  r271 : c.nreg 271 = L
  tree : PTree n r₀ f dep
  tab : Tab n bU L f c.nmem
  mdep : ∀ v < n, c.nmem (bD + v) = dep v
  pow : n ≤ 2 ^ L
  hL : 1 ≤ L
  hU : bU + L * n ≤ W
  hD : bD + n ≤ W

/-- The state of the lifting at level `j`. -/
structure LI (n bU L W : ℕ) (f dep : ℕ → ℕ) (c₀ : Config) (u₁ v₁ j : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : ∀ r, r < 280 ∨ 292 ≤ r → c.nreg r = c₀.nreg r
  mem : c.nmem = c₀.nmem
  out : c.output = c₀.output
  r281 : c.nreg 281 = v₁
  r284 : c.nreg 284 = dep v₁
  r286 : c.nreg 286 = j
  le : j ≤ L
  r287 : c.nreg 287 = bU + j * n
  cur : ∃ s, c.nreg 280 = f^[s] u₁ ∧ dep v₁ ≤ dep (f^[s] u₁) ∧ dep (f^[s] u₁) < dep v₁ + 2 ^ j

/-- The state of the joint jump at level `j`. -/
structure JI (n bU L W : ℕ) (f : ℕ → ℕ) (c₀ : Config) (a₀ b₀ j : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : ∀ r, r < 280 ∨ 292 ≤ r → c.nreg r = c₀.nreg r
  mem : c.nmem = c₀.nmem
  out : c.output = c₀.output
  r286 : c.nreg 286 = j
  le : j ≤ L
  r287 : c.nreg 287 = bU + j * n
  cur : ∃ t, c.nreg 280 = f^[t] a₀ ∧ c.nreg 281 = f^[t] b₀ ∧ f^[t] a₀ ≠ f^[t] b₀ ∧
    f^[2 ^ j] (f^[t] a₀) = f^[2 ^ j] (f^[t] b₀)

section query

variable {W : ℕ} {P : Input} {n r₀ bD bU L : ℕ} {f dep : ℕ → ℕ} {c₀ : Config}
  (hF : QFix n r₀ bD bU L W f dep c₀)
include hF

theorem qinit_exec (c : Config) (hc : WordsBounded W c)
    (hr : ∀ r, r < 280 ∨ 292 ≤ r → c.nreg r = c₀.nreg r) :
    ∃ c' t, Exec P W qinit c c' t ∧ t = 3 ∧ c'.nreg 286 = L ∧ c'.nreg 287 = bU + L * n ∧
      (∀ r, r ≠ 286 → r ≠ 287 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.output = c.output := by
  have g271 := (hr 271 (by omega)).trans hF.r271
  have g161 := (hr 161 (by omega)).trans hF.r161
  have g254 := (hr 254 (by omega)).trans hF.r254
  have hU := hF.hU
  unfold qinit
  exec_block
  · config_simp; rw [g271, g161]; omega
  · config_simp; rw [g271, g161, g254]; omega
  refine ⟨rfl, ?_, ?_, fun r a b => ?_, rfl, rfl⟩
  all_goals config_simp
  · exact g271
  · rw [g271, g161, g254]; ring
  · simp only [upd_apply]; split_ifs <;> first | omega | rfl

set_option maxHeartbeats 1000000 in
theorem lstep_exec {u₁ v₁ j : ℕ} (hu₁ : u₁ < n) (c : Config)
    (hI : LI n bU L W f dep c₀ u₁ v₁ j c) (hj : 0 < j) :
    ∃ c' t, Exec P W lstep c c' t ∧ LI n bU L W f dep c₀ u₁ v₁ (j - 1) c' ∧ t ≤ 9 := by
  have hc := hI.wb
  have hT := hF.tree
  have g141 := (hI.regs 141 (by omega)).trans hF.r141
  have g161 := (hI.regs 161 (by omega)).trans hF.r161
  have g253 := (hI.regs 253 (by omega)).trans hF.r253
  obtain ⟨s, h280, hd1, hd2⟩ := hI.cur
  have hx : f^[s] u₁ < n := hT.iter_lt s hu₁
  have hjn : (j - 1) * n + n = j * n := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hj]
  have hjL : j * n ≤ L * n := Nat.mul_le_mul_right _ hI.le
  have hU := hF.hU
  have hD := hF.hD
  have hp : 2 ^ j = 2 * 2 ^ (j - 1) := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]; ring
  have ha : f^[2 ^ (j - 1)] (f^[s] u₁) < n := hT.iter_lt _ hx
  have mA : c.nmem (bU + j * n - n + f^[s] u₁) = f^[2 ^ (j - 1)] (f^[s] u₁) := by
    rw [hI.mem, show bU + j * n - n + f^[s] u₁ = bU + (j - 1) * n + f^[s] u₁ by omega]
    exact hF.tab (j - 1) (by have := hI.le; omega) _ hx
  have mD : c.nmem (bD + f^[2 ^ (j - 1)] (f^[s] u₁)) = dep (f^[2 ^ (j - 1)] (f^[s] u₁)) := by
    rw [hI.mem]; exact hF.mdep _ ha
  have hda := hT.dep_iter (2 ^ (j - 1)) hx
  unfold lstep
  refine spec_seq ?_
  exec_block
  all_goals try (config_simp; simp only [g141, g161, g253, hI.r286, hI.r287, h280, mA, mD]; omega)
  rename_i hw₁
  config_simp at hw₁
  config_simp
  simp only [g141, g161, g253, hI.r286, hI.r287, h280, mA, mD] at hw₁ ⊢
  by_cases ht : dep (f^[2 ^ (j - 1)] (f^[s] u₁)) < dep v₁
  · refine spec_ifLtN_true (by config_simp; rw [hI.r284]; exact ht) ?_
    refine spec_skip hw₁ ?_
    refine ⟨⟨hw₁, (fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hI.regs r hr), hI.mem, hI.out, ?_, ?_, ?_, by have := hI.le; omega, ?_, s, ?_, hd1, by omega⟩,
      by omega⟩
    all_goals config_simp
    · exact hI.r281
    · exact hI.r284
    · omega
    · exact h280
  · refine spec_ifLtN_false (by config_simp; rw [hI.r284]; exact ht) ?_
    refine spec_instr (Exec.copyN hw₁ 280 290) fun hw₂ => ?_
    refine ⟨⟨hw₂, fun r hr => ?_, hI.mem, hI.out, ?_, ?_, ?_, by have := hI.le; omega, ?_,
      2 ^ (j - 1) + s, ?_, ?_, ?_⟩, by omega⟩
    all_goals config_simp
    · simp only [upd_apply]; split_ifs <;> first | omega | exact hI.regs r hr
    · exact hI.r281
    · exact hI.r284
    · omega
    · rw [Function.iterate_add_apply]
    · rw [Function.iterate_add_apply]; omega
    · rw [Function.iterate_add_apply]; omega

/-- **The lifting.** From `u₁`, `v₁` with `dep v₁ ≤ dep u₁`, `lift` leaves in `r280` an ancestor
of `u₁` at the depth of `v₁`, within `11 L + 5` steps. -/
theorem lift_exec {u₁ v₁ : ℕ} (hu₁ : u₁ < n) (hle : dep v₁ ≤ dep u₁)
    (c : Config) (hc : WordsBounded W c) (hr : ∀ r, r < 280 ∨ 292 ≤ r → c.nreg r = c₀.nreg r)
    (hm : c.nmem = c₀.nmem) (ho : c.output = c₀.output) (h280 : c.nreg 280 = u₁)
    (h281 : c.nreg 281 = v₁) (h284 : c.nreg 284 = dep v₁) :
    ∃ c' t, Exec P W lift c c' t ∧ t ≤ 11 * L + 5 ∧
      (∀ r, r < 280 ∨ 292 ≤ r → c'.nreg r = c₀.nreg r) ∧ c'.nmem = c₀.nmem ∧
      c'.output = c₀.output ∧ c'.nreg 281 = v₁ ∧
      ∃ s, c'.nreg 280 = f^[s] u₁ ∧ dep (f^[s] u₁) = dep v₁ := by
  obtain ⟨c₁, t₁, e₁, rfl, h286, h287, hr₁, hm₁, ho₁⟩ := qinit_exec (P := P) hF c hc hr
  have hT := hF.tree
  have hI₁ : LI n bU L W f dep c₀ u₁ v₁ L c₁ := by
    refine ⟨e₁.wb_right, fun r h => by rw [hr₁ r (by omega) (by omega)]; exact hr r h,
      hm₁.trans hm, ho₁.trans ho, by rw [hr₁ 281 (by omega) (by omega)]; exact h281,
      by rw [hr₁ 284 (by omega) (by omega)]; exact h284, h286, le_rfl, h287, 0, ?_, hle, ?_⟩
    · rw [hr₁ 280 (by omega) (by omega)]; exact h280
    · have := hT.dep_lt u₁ hu₁; have := hF.pow; simp only [Function.iterate_zero, id_eq]; omega
  obtain ⟨c', t, e, ⟨j, hI'⟩, hn, ht⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 140)
    (b := 286) (body := lstep) (fun c => ∃ j, LI n bU L W f dep c₀ u₁ v₁ j c)
    (fun c => 11 * c.nreg 286) (fun c ⟨_, h⟩ => h.wb)
    (fun c ⟨j, h⟩ hlt => by
      have g140 := (h.regs 140 (by omega)).trans hF.r140
      rw [g140, h.r286] at hlt
      obtain ⟨c', t, e, h', ht⟩ := lstep_exec (P := P) hF hu₁ c h hlt
      exact ⟨c', t, e, ⟨_, h'⟩, by rw [h'.r286, h.r286]; omega⟩) ⟨L, hI₁⟩
  have g140 := (hI'.regs 140 (by omega)).trans hF.r140
  rw [g140, hI'.r286] at hn
  obtain ⟨s, h1, h2, h3⟩ := hI'.cur
  refine ⟨c', 3 + t, .seq e₁ e, ?_, hI'.regs, hI'.mem, hI'.out, hI'.r281, s, h1, ?_⟩
  · rw [h286] at ht; omega
  · have : j = 0 := by omega
    subst this; simp at h3; omega

set_option maxHeartbeats 1000000 in
theorem jstep_exec {a₀ b₀ j : ℕ} (ha₀ : a₀ < n) (hb₀ : b₀ < n) (c : Config)
    (hI : JI n bU L W f c₀ a₀ b₀ j c) (hj : 0 < j) :
    ∃ c' t, Exec P W jstep c c' t ∧ JI n bU L W f c₀ a₀ b₀ (j - 1) c' ∧ t ≤ 12 := by
  have hc := hI.wb
  have hT := hF.tree
  have g141 := (hI.regs 141 (by omega)).trans hF.r141
  have g161 := (hI.regs 161 (by omega)).trans hF.r161
  obtain ⟨t, h280, h281, hne, heq⟩ := hI.cur
  have hx : f^[t] a₀ < n := hT.iter_lt t ha₀
  have hy : f^[t] b₀ < n := hT.iter_lt t hb₀
  have hjn : (j - 1) * n + n = j * n := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hj]
  have hjL : j * n ≤ L * n := Nat.mul_le_mul_right _ hI.le
  have hU := hF.hU
  have mA : c.nmem (bU + j * n - n + f^[t] a₀) = f^[2 ^ (j - 1)] (f^[t] a₀) := by
    rw [hI.mem, show bU + j * n - n + f^[t] a₀ = bU + (j - 1) * n + f^[t] a₀ by omega]
    exact hF.tab (j - 1) (by have := hI.le; omega) _ hx
  have mB : c.nmem (bU + j * n - n + f^[t] b₀) = f^[2 ^ (j - 1)] (f^[t] b₀) := by
    rw [hI.mem, show bU + j * n - n + f^[t] b₀ = bU + (j - 1) * n + f^[t] b₀ by omega]
    exact hF.tab (j - 1) (by have := hI.le; omega) _ hy
  unfold jstep
  refine spec_seq ?_
  exec_block
  all_goals try (config_simp; simp only [g141, g161, hI.r286, hI.r287, h280, h281, mA, mB]; omega)
  rename_i hw₁
  config_simp at hw₁
  config_simp
  simp only [g141, g161, hI.r286, hI.r287, h280, h281, mA, mB] at hw₁ ⊢
  set x := f^[2 ^ (j - 1)] (f^[t] a₀) with hxdef
  set y := f^[2 ^ (j - 1)] (f^[t] b₀) with hydef
  -- moving both up
  have hmove : x ≠ y → ∀ c' : Config, WordsBounded W c' →
      (∀ r, r < 280 ∨ 292 ≤ r → c'.nreg r = c₀.nreg r) → c'.nmem = c.nmem →
      c'.output = c.output → c'.nreg 286 = j - 1 → c'.nreg 287 = bU + (j - 1) * n →
      c'.nreg 280 = x → c'.nreg 281 = y → JI n bU L W f c₀ a₀ b₀ (j - 1) c' := by
    intro hxy c' hw' hr' hm' ho' g286 g287 g280 g281
    refine ⟨hw', hr', hm'.trans hI.mem, ho'.trans hI.out, g286, by have := hI.le; omega, g287,
      2 ^ (j - 1) + t, ?_, ?_, ?_, ?_⟩
    · rw [g280, Function.iterate_add_apply]
    · rw [g281, Function.iterate_add_apply]
    · rw [Function.iterate_add_apply, Function.iterate_add_apply]; exact hxy
    · rw [Function.iterate_add_apply, Function.iterate_add_apply, iter_two_pow hj,
        iter_two_pow hj]
      exact heq
  rcases Nat.lt_trichotomy x y with hlt | heq' | hgt
  · refine spec_ifLtN_true (by config_simp; exact hlt) ?_
    exec_block
    refine ⟨hmove (by omega) _ ‹_› (fun r hr => ?_) rfl rfl ?_ ?_ ?_ ?_, by omega⟩
    all_goals config_simp
    · simp only [upd_apply]; split_ifs <;> first | omega | exact hI.regs r hr
    · omega
  · refine spec_ifLtN_false (by config_simp; omega) ?_
    refine spec_ifLtN_false (by config_simp; omega) ?_
    refine spec_skip hw₁ ?_
    refine ⟨⟨hw₁, (fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hI.regs r hr), hI.mem, hI.out, ?_, by have := hI.le; omega, ?_, t, ?_, ?_, hne, ?_⟩,
      by omega⟩
    all_goals config_simp
    · omega
    · exact h280
    · exact h281
    · exact heq'
  · refine spec_ifLtN_false (by config_simp; omega) ?_
    refine spec_ifLtN_true (by config_simp; exact hgt) ?_
    exec_block
    refine ⟨hmove (by omega) _ ‹_› (fun r hr => ?_) rfl rfl ?_ ?_ ?_ ?_, by omega⟩
    all_goals config_simp
    · simp only [upd_apply]; split_ifs <;> first | omega | exact hI.regs r hr
    · omega

/-- **The joint jump.** From distinct `a₀`, `b₀` at the same depth, `jump` finds the last `t` at
which their ancestors `f^[t] a₀`, `f^[t] b₀` differ and leaves `f^[t + 1] a₀` in `r282`, within
`14 L + 7` steps. -/
theorem jump_exec {a₀ b₀ : ℕ} (ha₀ : a₀ < n) (hb₀ : b₀ < n) (hne : a₀ ≠ b₀)
    (hd : dep a₀ = dep b₀) (c : Config) (hc : WordsBounded W c)
    (hr : ∀ r, r < 280 ∨ 292 ≤ r → c.nreg r = c₀.nreg r) (hm : c.nmem = c₀.nmem)
    (ho : c.output = c₀.output) (h280 : c.nreg 280 = a₀) (h281 : c.nreg 281 = b₀) :
    ∃ c' t, Exec P W jump c c' t ∧ t ≤ 14 * L + 7 ∧
      (∀ r, r < 280 ∨ 292 ≤ r → c'.nreg r = c₀.nreg r) ∧ c'.nmem = c₀.nmem ∧
      c'.output = c₀.output ∧ ∃ t', f^[t'] a₀ ≠ f^[t'] b₀ ∧ f^[t' + 1] a₀ = f^[t' + 1] b₀ ∧
        c'.nreg 282 = f^[t' + 1] a₀ := by
  obtain ⟨c₁, t₁, e₁, rfl, h286, h287, hr₁, hm₁, ho₁⟩ := qinit_exec (P := P) hF c hc hr
  have hT := hF.tree
  have hI₁ : JI n bU L W f c₀ a₀ b₀ L c₁ := by
    refine ⟨e₁.wb_right, fun r h => by rw [hr₁ r (by omega) (by omega)]; exact hr r h,
      hm₁.trans hm, ho₁.trans ho, h286, le_rfl, h287, 0, ?_, ?_, hne, ?_⟩
    · rw [hr₁ 280 (by omega) (by omega)]; exact h280
    · rw [hr₁ 281 (by omega) (by omega)]; exact h281
    · have h1 := hT.dep_lt a₀ ha₀
      have h2 := hF.pow
      simp only [Function.iterate_zero, id_eq]
      rw [hT.iter_of_le ha₀ (by omega), hT.iter_of_le hb₀ (by omega)]
  obtain ⟨c₂, t₂, e₂, ⟨j, hI₂⟩, hn, ht₂⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 140)
    (b := 286) (body := jstep) (fun c => ∃ j, JI n bU L W f c₀ a₀ b₀ j c)
    (fun c => 14 * c.nreg 286) (fun c ⟨_, h⟩ => h.wb)
    (fun c ⟨j, h⟩ hlt => by
      have g140 := (h.regs 140 (by omega)).trans hF.r140
      rw [g140, h.r286] at hlt
      obtain ⟨c', t, e, h', ht⟩ := jstep_exec (P := P) hF ha₀ hb₀ c h hlt
      exact ⟨c', t, e, ⟨_, h'⟩, by rw [h'.r286, h.r286]; omega⟩) ⟨L, hI₁⟩
  have g140 := (hI₂.regs 140 (by omega)).trans hF.r140
  rw [g140, hI₂.r286] at hn
  obtain rfl : j = 0 := by omega
  obtain ⟨t, g280, g281, gne, geq⟩ := hI₂.cur
  have hc₂ := hI₂.wb
  have g254 := (hI₂.regs 254 (by omega)).trans hF.r254
  have hx : f^[t] a₀ < n := hT.iter_lt t ha₀
  have hnL : n ≤ L * n := Nat.le_mul_of_pos_left n hF.hL
  have hU := hF.hU
  have mx : c₂.nmem (bU + f^[t] a₀) = f^[t + 1] a₀ := by
    have := hF.tab 0 hF.hL _ hx
    rw [hI₂.mem]
    simp only [zero_mul, add_zero, pow_zero, Function.iterate_one] at this
    rw [this, Function.iterate_succ_apply']
  obtain ⟨c₃, t₃, e₃, h₃, rfl⟩ : ∃ c₃ t₃, Exec P W (block [.addN 289 254 280, .loadN 282 289])
      c₂ c₃ t₃ ∧ ((∀ r, r < 280 ∨ 292 ≤ r → c₃.nreg r = c₀.nreg r) ∧ c₃.nmem = c₀.nmem ∧
        c₃.output = c₀.output ∧ c₃.nreg 282 = f^[t + 1] a₀) ∧ t₃ = 2 := by
    exec_block
    · config_simp; rw [g254, g280]; omega
    refine ⟨⟨fun r hr => ?_, hI₂.mem, hI₂.out, ?_⟩, rfl⟩
    all_goals config_simp
    · simp only [upd_apply]; split_ifs <;> first | omega | exact hI₂.regs r hr
    · rw [g254, g280, mx]
  refine ⟨c₃, 3 + (t₂ + 2), .seq e₁ (.seq e₂ e₃), ?_, h₃.1, h₃.2.1, h₃.2.2.1, t, gne, ?_,
    h₃.2.2.2⟩
  · rw [h286] at ht₂; omega
  · simp only [pow_zero, Function.iterate_one] at geq
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', geq]

/-- **A lowest-common-ancestor query.** For vertices `u = r280`, `v = r281` of a numeric tree
whose table of `2 ^ j`-th ancestors (`j < L`, `n ≤ 2 ^ L`) and depths are in memory, `lcaq`
leaves their lowest common ancestor in `r282`, within `25 L + 26` steps, without writing to
memory. -/
theorem lcaq_exec (hc₀ : WordsBounded W c₀) {u v : ℕ} (hu : u < n) (hv : v < n)
    (h280 : c₀.nreg 280 = u) (h281 : c₀.nreg 281 = v) :
    ∃ c' t, Exec P W lcaq c₀ c' t ∧ t ≤ 25 * L + 26 ∧ IsLCA f u v (c'.nreg 282) ∧
      c'.nreg 282 < n ∧ (∀ r, r < 280 ∨ 292 ≤ r → c'.nreg r = c₀.nreg r) ∧
      c'.nmem = c₀.nmem ∧ c'.output = c₀.output := by
  have hT := hF.tree
  have hD := hF.hD
  have mu : c₀.nmem (bD + u) = dep u := hF.mdep u hu
  have mv : c₀.nmem (bD + v) = dep v := hF.mdep v hv
  -- the depths, and the deeper vertex first
  obtain ⟨c₂, t₂, e₂, ht₂, hw₂, hr₂, hm₂, ho₂, u₁, v₁, g280, g281, g284, hle, huv⟩ :
      ∃ c₂ t₂, Exec P W (.seq qload (.ifLtN 283 284 qswap .skip)) c₀ c₂ t₂ ∧ t₂ ≤ 11 ∧
        WordsBounded W c₂ ∧ (∀ r, r < 280 ∨ 292 ≤ r → c₂.nreg r = c₀.nreg r) ∧
        c₂.nmem = c₀.nmem ∧ c₂.output = c₀.output ∧ ∃ u₁ v₁, c₂.nreg 280 = u₁ ∧
        c₂.nreg 281 = v₁ ∧ c₂.nreg 284 = dep v₁ ∧ dep v₁ ≤ dep u₁ ∧
        ((u₁ = u ∧ v₁ = v) ∨ (u₁ = v ∧ v₁ = u)) := by
    refine spec_seq ?_
    unfold qload
    exec_block
    · config_simp; rw [hF.r253, h280]; omega
    · config_simp; rw [hF.r253, h281]; omega
    config_simp
    rw [hF.r253, h280, h281, mu, mv]
    rename_i hw₁
    config_simp at hw₁
    rw [hF.r253, h280, h281, mu, mv] at hw₁
    by_cases hlt : dep u < dep v
    · refine spec_ifLtN_true (by config_simp; exact hlt) ?_
      unfold qswap
      exec_block
      refine ⟨by omega, ‹_›, fun r hr => ?_, rfl, rfl, v, u, ?_, ?_, ?_, hlt.le, Or.inr ⟨rfl, rfl⟩⟩
      all_goals config_simp
      · simp only [upd_apply]; split_ifs <;> first | omega | rfl
      · exact h281
      · exact h280
    · refine spec_ifLtN_false (by config_simp; exact hlt) ?_
      refine spec_skip hw₁ ?_
      refine ⟨by omega, hw₁, fun r hr => ?_, rfl, rfl, u, v, ?_, ?_, ?_, by omega,
        Or.inl ⟨rfl, rfl⟩⟩
      all_goals config_simp
      · simp only [upd_apply]; split_ifs <;> first | omega | rfl
      · exact h280
      · exact h281
  have hu₁ : u₁ < n := by rcases huv with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
  have hv₁ : v₁ < n := by rcases huv with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
  -- the lifting
  obtain ⟨c₃, t₃, e₃, ht₃, hr₃, hm₃, ho₃, g281', s, g280', hds⟩ := lift_exec (P := P) hF hu₁
    hle c₂ hw₂ hr₂ hm₂ ho₂ g280 g281 g284
  have hw₃ := e₃.wb_right
  have ha₀ : f^[s] u₁ < n := hT.iter_lt s hu₁
  -- the lowest common ancestor of `u₁`, `v₁`
  have fin : ∀ l, IsLCA f u₁ v₁ l → IsLCA f u v l := fun l h => by
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    · exact h.symm
  have hlt_n : ∀ l, IsLCA f u v l → l < n := fun l h => by
    obtain ⟨m, rfl⟩ := h.1; exact hT.iter_lt m hu
  have hjump : f^[s] u₁ ≠ v₁ → ∃ c' t, Exec P W jump c₃ c' t ∧ t ≤ 14 * L + 7 ∧
      IsLCA f u v (c'.nreg 282) ∧ (∀ r, r < 280 ∨ 292 ≤ r → c'.nreg r = c₀.nreg r) ∧
      c'.nmem = c₀.nmem ∧ c'.output = c₀.output := by
    intro hne
    obtain ⟨c', t, e, ht, hr', hm', ho', t', gne, geq, g282⟩ := jump_exec (P := P) hF ha₀ hv₁ hne
      hds c₃ hw₃ hr₃ hm₃ ho₃ g280' g281'
    refine ⟨c', t, e, ht, ?_, hr', hm', ho'⟩
    rw [g282]
    exact fin _ (hT.isLCA_of_lift hu₁ hv₁ hds gne geq)
  rcases Nat.lt_trichotomy (f^[s] u₁) v₁ with hlt | heq | hgt
  · obtain ⟨c', t, e, ht, hl, hr', hm', ho'⟩ := hjump (by omega)
    exact ⟨c', t₂ + (t₃ + (t + 1)), .seq e₂ (.seq e₃ (.ifLtN_true (by rw [g280', g281']; exact hlt)
      e)), by omega, hl, hlt_n _ hl, hr', hm', ho'⟩
  · have e₄ := Exec.copyN (P := P) hw₃ 282 280
    have hl : IsLCA f u v (c₃.nreg 280) := by
      rw [g280', heq]; exact fin _ (hT.isLCA_of_eq heq)
    refine ⟨_, t₂ + (t₃ + (1 + 2 + 2)), .seq e₂ (.seq e₃ (.ifLtN_false (by omega)
      (.ifLtN_false (by omega) e₄))), by omega, ?_, ?_, fun r hr => ?_, hm₃, ho₃⟩
    · config_simp; exact hl
    · config_simp; exact hlt_n _ hl
    · config_simp; rw [upd_other _ _ _ (by omega)]; exact hr₃ r hr
  · obtain ⟨c', t, e, ht, hl, hr', hm', ho'⟩ := hjump (by omega)
    exact ⟨c', t₂ + (t₃ + (t + 1 + 2)), .seq e₂ (.seq e₃ (.ifLtN_false (by omega)
      (.ifLtN_true (by rw [g280', g281']; exact hgt) e))), by omega, hl, hlt_n _ hl, hr', hm', ho'⟩

end query

/-! ### The bridge to spanning trees -/

section Bridge

open Map

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}
  {n : ℕ} (vi : Q ≃ Fin n) (T : M.SpTree) {f dep : ℕ → ℕ}
  (hf : ∀ x, f (vi x) = vi (T.parent x))
include hf

omit [Fintype D] [DecidableEq D] [Fintype Q] in
theorem iter_tree (m : ℕ) (x : Q) : f^[m] (vi x) = vi (T.parent^[m] x) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, hf, ih, ← Function.iterate_succ_apply]

omit [Fintype D] [DecidableEq D] [Fintype Q] in
/-- Numeric ancestors are the ancestors in the tree. -/
theorem isAnc_tree (a x : Q) : IsAnc f (vi a) (vi x) ↔ a ∈ T.anc x := by
  rw [T.mem_anc_iff, IsAnc]
  refine exists_congr fun m => ?_
  rw [iter_tree vi T hf]
  exact ⟨fun h => vi.injective (Fin.ext h), fun h => by rw [h]⟩

omit [Fintype D] in
/-- **The numeric tree of a spanning tree**: the parents and the depths `#(anc v) - 1` read
through a numbering of the vertices. -/
theorem ptree_tree (hdep : ∀ x, dep (vi x) = #(T.anc x) - 1) : PTree n (vi T.root) f dep := by
  refine ⟨(vi _).2, fun u hu => ?_, by rw [hf, T.parent_root], by rw [hdep, T.anc_root]; simp,
    fun u hu hr => ?_, fun u hu => ?_⟩
  · obtain ⟨x, rfl⟩ := exists_vi vi hu; rw [hf]; exact (vi _).2
  · obtain ⟨x, rfl⟩ := exists_vi vi hu
    have h : x ≠ T.root := fun h' => hr (by rw [h'])
    rw [hf, hdep, hdep, T.anc_of_ne h,
      card_insert_of_notMem (SpTree.notMem_anc_parent (T := T) h)]
    have := card_pos.2 ⟨_, T.mem_anc_self (T.parent x)⟩
    omega
  · obtain ⟨x, rfl⟩ := exists_vi vi hu
    rw [hdep]
    have := card_anc_le vi T x
    have := card_pos.2 ⟨_, T.mem_anc_self x⟩
    omega

omit [Fintype D] [DecidableEq D] [Fintype Q] in
/-- **A numeric lowest common ancestor is the deepest common ancestor**: its ancestors are the
common ancestors. -/
theorem isLCA_tree {x y : Q} {l : ℕ} (h : IsLCA f (vi x) (vi y) l) :
    ∃ z, l = vi z ∧ T.anc x ∩ T.anc y = T.anc z := by
  obtain ⟨m, hm⟩ := h.1
  rw [iter_tree vi T hf] at hm
  refine ⟨_, hm.symm, ?_⟩
  have hzx : T.parent^[m] x ∈ T.anc x := T.iterate_parent_mem_anc m x
  have hzy : T.parent^[m] x ∈ T.anc y := by
    rw [← isAnc_tree vi T hf, hm]; exact h.2.1
  ext a
  rw [mem_inter]
  constructor
  · rintro ⟨ha, hb⟩
    rw [← isAnc_tree vi T hf, hm]
    exact h.2.2 _ ((isAnc_tree vi T hf a x).2 ha) ((isAnc_tree vi T hf a y).2 hb)
  · intro ha
    exact ⟨T.anc_subset_anc hzx ha, T.anc_subset_anc hzy ha⟩

omit [Fintype D] [Fintype Q] in
/-- **For the two ends of a dart**, the numeric lowest common ancestor is (the number of)
`lca T δ`. -/
theorem isLCA_lca (δ : D) {l : ℕ} (h : IsLCA f (vi (M.vert δ)) (vi (M.vert (M.α δ))) l) :
    l = vi (SpTree.lca T δ) := by
  obtain ⟨z, rfl, hz⟩ := isLCA_tree vi T hf h
  rw [SpTree.anc_inter_anc (T := T) δ] at hz
  have h1 : z ∈ T.anc (SpTree.lca T δ) := by rw [hz]; exact T.mem_anc_self z
  have h2 : SpTree.lca T δ ∈ T.anc z := by rw [← hz]; exact T.mem_anc_self _
  rw [T.eq_of_mem_anc_of_mem_anc h1 h2]

/-- **The query for a dart.** With the table and the depths of a spanning tree `T` in memory
(`QFix`, the parents `f` those of `T`), the query on the numbers of the two ends of `δ` returns
the number of `lca T δ`, within `25 L + 26` steps. -/
theorem lcaq_lca {W bD bU L : ℕ} {P' : Input} {c₀ : Config}
    (hF : QFix n (vi T.root) bD bU L W f dep c₀) (hc₀ : WordsBounded W c₀) (δ : D)
    (h280 : c₀.nreg 280 = vi (M.vert δ)) (h281 : c₀.nreg 281 = vi (M.vert (M.α δ))) :
    ∃ c' t, Exec P' W lcaq c₀ c' t ∧ t ≤ 25 * L + 26 ∧ c'.nreg 282 = vi (SpTree.lca T δ) ∧
      (∀ r, r < 280 ∨ 292 ≤ r → c'.nreg r = c₀.nreg r) ∧ c'.nmem = c₀.nmem ∧
      c'.output = c₀.output := by
  obtain ⟨c', t, e, ht, hl, -, hr, hm, ho⟩ := lcaq_exec (P := P') hF hc₀ (vi _).2 (vi _).2
    h280 h281
  exact ⟨c', t, e, ht, isLCA_lca vi T hf δ hl, hr, hm, ho⟩

end Bridge

end MillerProg

end PlanarSeparator
