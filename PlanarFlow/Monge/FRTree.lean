module

public import PlanarFlow.Monge.FRDijkstra
public import PlanarFlow.Dijkstra.Heap

/-!
# FR-Dijkstra on the machine: the half blocks and the tournament trees

The machine version of FR-Dijkstra splits the arcs of the dense distance graph (on the corners
`0, …, b - 1`, `PlanarFlow.Monge.InBlock`) into *half blocks*: for every level `s = 2 ^ t < b`
and every `k` with `k s < b`, the half block `(t, k)` holds the arcs from the sources
`sib k * s + σ` (`σ < hbNc b s k`) to the targets `k s + ρ` (`ρ < s`, clamped to `b - 1` by
`cl`). Its matrix `hbF` (row `ρ` a target, column `σ` a source, entry the length reduced by the
price of the target) is *anti-Monge* (`AntiM`): `F ρ σ' + F ρ' σ ≤ F ρ σ + F ρ' σ'` for
`ρ < ρ'`, `σ < σ'`, by the crossing inequality of the face (`antiM_hbF`). Hence a smaller source
not worse at a row is not worse at the later rows, and a larger one at the earlier rows
(`antiM_after`, `antiM_before`): the facts behind the bipartite Monge heaps
(`PlanarFlow.Monge.FR.OwnOK`).

The heap of the vertices, the heap of the half blocks and the two tournaments over the rows of a
half block (`PlanarFlow.Monge.FR.tUp_exec`) are tournament trees of *winners* (`WinOK`): every
internal node holds the better of the winners of its children (`better`), so the root holds a
present leaf of least key (`win_root`); `WinOK.set` repairs the tree above a changed leaf. The
node of height `j` over the row `ρ` of a tree with `s` leaves is `nd s j ρ` (`Valid`, `nd_order`:
the rows of the left child come first).

`iteT`, `iteF`: rewriting a conditional by its condition.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace FR

open Heap

/-! ### Conditionals -/

lemma iteT {α : Sort*} {p : Prop} [Decidable p] {a b : α} (h : p) :
    (if p then a else b) = a := by simp [h]

lemma iteF {α : Sort*} {p : Prop} [Decidable p] {a b : α} (h : ¬ p) :
    (if p then a else b) = b := by simp [h]

/-! ### Nodes -/

/-- The node of height `j` over the row `ρ`, in a tree with `s` leaves. -/
def nd (s j ρ : ℕ) : ℕ := (s + ρ) / 2 ^ j

/-- `v` is a node of height `j` of the tree with `s` leaves. -/
def Valid (s j v : ℕ) : Prop := 1 ≤ v ∧ s ≤ v * 2 ^ j ∧ v * 2 ^ j < 2 * s ∧ 2 ^ j ∣ s

lemma nd_zero (s ρ : ℕ) : nd s 0 ρ = s + ρ := by simp [nd]

lemma nd_succ (s j ρ : ℕ) : nd s (j + 1) ρ = nd s j ρ / 2 := by
  unfold nd; rw [pow_succ, Nat.div_div_eq_div_mul]

lemma nd_child {s j ρ v : ℕ} : nd s (j + 1) ρ = v ↔ nd s j ρ = 2 * v ∨ nd s j ρ = 2 * v + 1 := by
  rw [nd_succ]; omega

lemma div_eq_iff' {x k v : ℕ} (hk : 0 < k) : x / k = v ↔ v * k ≤ x ∧ x < (v + 1) * k := by
  constructor
  · rintro rfl
    refine ⟨Nat.div_mul_le_self x k, ?_⟩
    rw [Nat.add_mul, Nat.one_mul]
    have h1 := Nat.div_add_mod x k
    have h2 := Nat.mod_lt x hk
    rw [Nat.mul_comm] at h1
    omega
  · rintro ⟨h1, h2⟩
    exact le_antisymm (Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hk).2 h2))
      ((Nat.le_div_iff_mul_le hk).2 h1)

/-- The rows below a node. -/
lemma nd_eq_iff {s j ρ v : ℕ} : nd s j ρ = v ↔ v * 2 ^ j ≤ s + ρ ∧ s + ρ < (v + 1) * 2 ^ j :=
  div_eq_iff' (Nat.two_pow_pos j)

lemma valid_child {s j v : ℕ} (h : Valid s (j + 1) v) :
    Valid s j (2 * v) ∧ Valid s j (2 * v + 1) := by
  unfold Valid at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hp : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
  rw [hp] at h2 h3 h4
  have h4' : 2 ^ j ∣ s := dvd_trans (Dvd.intro_left 2 rfl) h4
  refine ⟨⟨by omega, ?_, ?_, h4'⟩, ⟨by omega, ?_, ?_, h4'⟩⟩ <;>
  obtain ⟨q, hq⟩ := h4 <;>
  generalize 2 ^ j = P at * <;>
  have hP : 0 < P := (by
    rcases Nat.eq_zero_or_pos P with h | h
    · subst h; simp at h2; omega
    · exact h) <;>
  have hlt : v < 2 * q := (by
    by_contra hc
    have : 2 * q * (2 * P) ≤ v * (2 * P) := Nat.mul_le_mul_right _ (by omega)
    rw [hq] at h3; nlinarith) <;>
  nlinarith

lemma valid_lt {s j v : ℕ} (h : Valid s (j + 1) v) : v < s := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have : v * 2 ≤ v * 2 ^ (j + 1) := Nat.mul_le_mul_left _ (by
    have := Nat.one_le_two_pow (n := j); rw [pow_succ]; omega)
  omega

lemma valid_zero {s v : ℕ} : Valid s 0 v ↔ 1 ≤ v ∧ s ≤ v ∧ v < 2 * s := by
  simp [Valid]

/-- The node of height `j` over a row `< s` (when `2 ^ j ∣ s`). -/
lemma valid_nd {s j ρ : ℕ} (hs : 1 ≤ s) (hj : 2 ^ j ∣ s) (hρ : ρ < s) : Valid s j (nd s j ρ) := by
  obtain ⟨q, hq⟩ := hj
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h, Nat.mul_zero] at hq; omega
    · exact h
  have e : nd s j ρ = q + ρ / 2 ^ j := by
    unfold nd; rw [hq, Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos j),
      Nat.add_comm]
  have h1 := Nat.div_mul_le_self ρ (2 ^ j)
  have h2 := Nat.div_mul_le_self (s + ρ) (2 ^ j)
  refine ⟨Nat.le_trans hq1 (by rw [e]; exact Nat.le_add_right _ _), ?_, ?_, ⟨q, hq⟩⟩
  · rw [e, Nat.add_mul, hq, Nat.mul_comm (2 ^ j) q]; omega
  · unfold nd at *; omega

/-- The rows below the left child come before the rows below the right child. -/
lemma nd_order {s j ρ ρ' v : ℕ} (h : nd s j ρ = 2 * v) (h' : nd s j ρ' = 2 * v + 1) : ρ < ρ' := by
  rw [nd_eq_iff] at h h'
  omega

/-- The root. -/
lemma nd_root {T ρ : ℕ} (hρ : ρ < 2 ^ T) : nd (2 ^ T) T ρ = 1 := by
  rw [nd_eq_iff]; omega

lemma valid_root (T : ℕ) : Valid (2 ^ T) T 1 :=
  ⟨le_rfl, by omega, by have := Nat.two_pow_pos T; omega, dvd_rfl⟩

lemma valid_unique {s j j' v : ℕ} (h : Valid s j v) (h' : Valid s j' v) : j = j' := by
  obtain ⟨a1, a2, a3, -⟩ := h
  obtain ⟨b1, b2, b3, -⟩ := h'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have : v * 2 ^ j * 2 ≤ v * 2 ^ j' := by
      rw [Nat.mul_assoc, ← pow_succ]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hlt)
    omega
  · have : v * 2 ^ j' * 2 ≤ v * 2 ^ j := by
      rw [Nat.mul_assoc, ← pow_succ]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hlt)
    omega

/-! ### Anti-Monge matrices -/

/-- The anti-Monge inequality on the rows `< s` and the columns `< nc`. -/
def AntiM (s nc : ℕ) (F : ℕ → ℕ → ℝ) : Prop :=
  ∀ ρ ρ' σ σ', ρ < ρ' → ρ' < s → σ < σ' → σ' < nc → F ρ σ' + F ρ' σ ≤ F ρ σ + F ρ' σ'

lemma AntiM.add_col {s nc : ℕ} {F : ℕ → ℕ → ℝ} (h : AntiM s nc F) (e : ℕ → ℝ) :
    AntiM s nc (fun ρ σ => e σ + F ρ σ) := by
  intro ρ ρ' σ σ' h1 h2 h3 h4
  have := h ρ ρ' σ σ' h1 h2 h3 h4
  simp only; linarith

/-- **Anti-Monge, after**: a smaller source not worse at the row `m` is not worse at the rows
after `m`. -/
lemma antiM_after {s nc : ℕ} {F : ℕ → ℕ → ℝ} (h : AntiM s nc F) {σ σ' m ρ : ℕ} (hσ : σ < σ')
    (hσ' : σ' < nc) (hm : m ≤ ρ) (hρ : ρ < s) (hle : F m σ ≤ F m σ') : F ρ σ ≤ F ρ σ' := by
  rcases Nat.eq_or_lt_of_le hm with rfl | hlt
  · exact hle
  · have := h m ρ σ σ' hlt hρ hσ hσ'
    linarith

/-- **Anti-Monge, before**: a larger source not worse at the row `m` is not worse at the rows
before `m`. -/
lemma antiM_before {s nc : ℕ} {F : ℕ → ℕ → ℝ} (h : AntiM s nc F) {σ σ' m ρ : ℕ} (hσ : σ < σ')
    (hσ' : σ' < nc) (hm : ρ ≤ m) (hms : m < s) (hle : F m σ' ≤ F m σ) : F ρ σ' ≤ F ρ σ := by
  rcases Nat.eq_or_lt_of_le hm with rfl | hlt
  · exact hle
  · have := h ρ m σ σ' hlt hms hσ hσ'
    linarith

/-! ### The half blocks -/

/-- The partner of the half `k` of a level: `k + 1` for `k` even, `k - 1` for `k` odd. -/
def sib (k : ℕ) : ℕ := if k % 2 = 0 then k + 1 else k - 1

/-- A target clamped to `b - 1`. -/
def cl (b y : ℕ) : ℕ := min y (b - 1)

/-- The number of sources of the half block `k` of the level `s`. -/
def hbNc (b s k : ℕ) : ℕ := min s (b - sib k * s)

/-- The matrix of the half block `k` of the level `s`: the rows are the targets `k s + ρ` (clamped
to `b - 1`), the columns the sources `sib k * s + σ`, the entries the lengths reduced at the
target by the price `p`. -/
def hbF (b : ℕ) (D : ℕ → ℕ → ℤ) (p : ℕ → ℤ) (s k ρ σ : ℕ) : ℝ :=
  ((D (sib k * s + σ) (cl b (k * s + ρ)) - p (cl b (k * s + ρ)) : ℤ) : ℝ)

lemma sib_mul (k s : ℕ) : sib k * s = if k % 2 = 0 then k * s + s else k * s - s := by
  unfold sib; split_ifs
  · ring
  · rw [Nat.sub_one_mul]

/-- **The matrix of a half block is anti-Monge**, by the crossing inequality of the face. -/
theorem antiM_hbF {b : ℕ} {D : ℕ → ℕ → ℤ} (hD : Crossing b D) (p : ℕ → ℤ) {s k : ℕ}
    (hk : k * s < b) : AntiM s (hbNc b s k) (hbF b D p s k) := by
  intro ρ ρ' σ σ' h1 h2 h3 h4
  unfold hbNc at h4
  have hsm := sib_mul k s
  have f1 : sib k * s + σ < sib k * s + σ' := by omega
  have f2 : sib k * s + σ' < b := by omega
  have f3 : cl b (k * s + ρ') < b := by unfold cl; omega
  have f4 : cl b (k * s + ρ) ≤ cl b (k * s + ρ') := by unfold cl; omega
  have hsep : sib k * s + σ' < cl b (k * s + ρ) ∨ cl b (k * s + ρ') < sib k * s + σ := by
    unfold cl
    split_ifs at hsm with hpar
    · right; omega
    · left
      have : s ≤ k * s := Nat.le_mul_of_pos_left s (by omega)
      omega
  unfold hbF
  generalize sib k * s + σ = i at *
  generalize sib k * s + σ' = i' at *
  generalize cl b (k * s + ρ) = j at *
  generalize cl b (k * s + ρ') = j' at *
  rcases Nat.eq_or_lt_of_le f4 with e | hlt
  · subst e; push_cast; linarith
  · have := hD i i' j j' f1 hlt f2 f3 hsep
    have h' : ((D i j' + D i' j : ℤ) : ℝ) ≤ ((D i j + D i' j' : ℤ) : ℝ) := by exact_mod_cast this
    push_cast at h' ⊢
    linarith

/-! ### The tournament tree of winners -/

/-- The better of two leaves: the first if it is present and the second is absent or of larger
key, the second otherwise. -/
noncomputable def better (pr : ℕ → ℕ) (key : ℕ → ℝ) (a b : ℕ) : ℕ :=
  if pr a = 1 ∧ (pr b ≠ 1 ∨ key a < key b) then a else b

/-- The tournament tree of winners over the leaves `0, …, n - 1` (node `n + x` for the leaf
`x`), correct except at the ancestors of `J`. -/
structure WinOK (n : ℕ) (pr : ℕ → ℕ) (key : ℕ → ℝ) (wn : ℕ → ℕ) (J : ℕ) : Prop where
  leaf : ∀ x < n, wn (n + x) = x
  under : ∀ i, 1 ≤ i → i < 2 * n → wn i < n ∧ Anc i (n + wn i)
  eq : ∀ i, 1 ≤ i → i < n → ¬ Anc i J → wn i = better pr key (wn (2 * i)) (wn (2 * i + 1))

lemma anc_half {i y : ℕ} (h : Anc i y) (hne : i ≠ y) : Anc i (y / 2) := by
  obtain ⟨k, hk⟩ := h
  rcases k with _ | k
  · simp at hk; exact absurd hk.symm hne
  · exact ⟨k, by rw [pow_succ', ← Nat.div_div_eq_div_mul] at hk; exact hk⟩

lemma anc_of_child {i y : ℕ} (h : Anc (2 * i) y ∨ Anc (2 * i + 1) y) : Anc i y := by
  rcases h with ⟨k, hk⟩ | ⟨k, hk⟩ <;>
  exact ⟨k + 1, by rw [pow_succ, ← Nat.div_div_eq_div_mul, hk]; omega⟩

lemma anc_child {i y : ℕ} (h : Anc i y) (hne : i ≠ y) : Anc (2 * i) y ∨ Anc (2 * i + 1) y := by
  obtain ⟨k, hk⟩ := h
  rcases k with _ | k
  · simp at hk; exact absurd hk.symm hne
  · rw [pow_succ, ← Nat.div_div_eq_div_mul] at hk
    rcases Nat.even_or_odd (y / 2 ^ k) with ⟨a, ha⟩ | ⟨a, ha⟩
    · left; exact ⟨k, by omega⟩
    · right; exact ⟨k, by omega⟩

lemma anc_one {y : ℕ} (hy : 1 ≤ y) : Anc 1 y := by
  refine ⟨Nat.log 2 y, ?_⟩
  have h1 := Nat.pow_log_le_self 2 (show y ≠ 0 by omega)
  have h2 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) y
  rw [pow_succ] at h2
  rw [div_eq_iff' (Nat.two_pow_pos _)]
  omega

variable {n : ℕ} {pr : ℕ → ℕ} {key : ℕ → ℝ} {wn : ℕ → ℕ}

lemma better_eq_left {a b : ℕ} (h : pr a = 1 ∧ (pr b ≠ 1 ∨ key a < key b)) :
    better pr key a b = a := by unfold better; rw [ite_eq_left_iff]; intro h'; exact absurd h h'

lemma better_eq_right {a b : ℕ} (h : ¬ (pr a = 1 ∧ (pr b ≠ 1 ∨ key a < key b))) :
    better pr key a b = b := by unfold better; rw [ite_eq_right_iff]; intro h'; exact absurd h' h

lemma better_mem (a b : ℕ) : better pr key a b = a ∨ better pr key a b = b := by
  unfold better; split_ifs <;> simp

/-- **The root holds a present leaf of least key.** -/
theorem win_root (h : WinOK n pr key wn 0) (hn : 1 ≤ n) :
    wn 1 < n ∧ ∀ x < n, pr x = 1 → pr (wn 1) = 1 ∧ key (wn 1) ≤ key x := by
  have gen : ∀ l, 1 ≤ l → l < 2 * n → ∀ x < n, Anc l (n + x) → pr x = 1 →
      pr (wn l) = 1 ∧ key (wn l) ≤ key x := by
    intro l
    induction hm : 2 * n - l using Nat.strong_induction_on generalizing l with
    | _ m ih =>
      intro hl1 hl2 x hx ha hpx
      rcases Nat.lt_or_ge l n with hln | hln
      · have hne : l ≠ n + x := by omega
        have hW := h.eq l hl1 hln (not_anc_zero hl1)
        have i0 := fun hA =>
          ih (2 * n - 2 * l) (by omega) (2 * l) rfl (by omega) (by omega) x hx hA hpx
        have i1 := fun hA =>
          ih (2 * n - (2 * l + 1)) (by omega) (2 * l + 1) rfl (by omega) (by omega) x hx hA hpx
        by_cases hc : pr (wn (2 * l)) = 1 ∧
          (pr (wn (2 * l + 1)) ≠ 1 ∨ key (wn (2 * l)) < key (wn (2 * l + 1)))
        · rw [hW, better_eq_left hc]
          rcases anc_child ha hne with hA | hA
          · exact i0 hA
          · obtain ⟨a1, a2⟩ := i1 hA
            rcases hc.2 with hc2 | hc2
            · exact absurd a1 hc2
            · exact ⟨hc.1, hc2.le.trans a2⟩
        · rw [hW, better_eq_right hc]
          rcases anc_child ha hne with hA | hA
          · obtain ⟨a1, a2⟩ := i0 hA
            have : pr (wn (2 * l + 1)) = 1 ∧ key (wn (2 * l + 1)) ≤ key (wn (2 * l)) := by
              by_contra hc'
              apply hc
              refine ⟨a1, ?_⟩
              by_cases hp : pr (wn (2 * l + 1)) = 1
              · exact Or.inr (not_le.1 fun hle => hc' ⟨hp, hle⟩)
              · exact Or.inl hp
            exact ⟨this.1, this.2.trans a2⟩
          · exact i1 hA
      · -- a leaf
        obtain ⟨k, hk⟩ := ha
        rcases k with _ | k
        · simp at hk
          rw [← hk, h.leaf x hx]; exact ⟨hpx, le_rfl⟩
        · exfalso
          have : (n + x) / 2 ^ (k + 1) ≤ (n + x) / 2 := Nat.div_le_div_left
            (by have := Nat.one_le_two_pow (n := k); rw [pow_succ]; omega) (by norm_num)
          omega
  refine ⟨(h.under 1 le_rfl (by omega)).1, fun x hx hpx => gen 1 le_rfl (by omega) x hx
    (anc_one (by omega)) hpx⟩

/-- **Changing a leaf** breaks the tree only at the ancestors of its parent. -/
theorem WinOK.set {pr' : ℕ → ℕ} {key' : ℕ → ℝ} (h : WinOK n pr key wn 0) {x : ℕ}
    (hpr : ∀ y, y ≠ x → pr' y = pr y) (hkey : ∀ y, y ≠ x → key' y = key y) :
    WinOK n pr' key' wn ((n + x) / 2) := by
  refine ⟨h.leaf, h.under, fun i hi1 hi2 hA => ?_⟩
  have hne : ∀ c, (c = 2 * i ∨ c = 2 * i + 1) → wn c ≠ x := by
    rintro c hc e
    have hu := (h.under c (by omega) (by omega)).2
    rw [e] at hu
    exact hA (anc_half (anc_of_child (by rcases hc with rfl | rfl; exacts [Or.inl hu, Or.inr hu]))
      (by omega))
  rw [h.eq i hi1 hi2 (not_anc_zero hi1)]
  unfold better
  rw [hpr _ (hne _ (Or.inl rfl)), hpr _ (hne _ (Or.inr rfl)), hkey _ (hne _ (Or.inl rfl)),
    hkey _ (hne _ (Or.inr rfl))]

/-- **Recomputing a node** moves the exception to its parent. -/
theorem WinOK.step {J : ℕ} (h : WinOK n pr key wn J) (hJ1 : 1 ≤ J) (hJ : J < n) :
    WinOK n pr key (Function.update wn J (better pr key (wn (2 * J)) (wn (2 * J + 1))))
      (J / 2) := by
  have hc0 : 2 * J ≠ J := by omega
  have hc1 : 2 * J + 1 ≠ J := by omega
  refine ⟨fun x hx => ?_, fun i hi1 hi2 => ?_, fun i hi1 hi2 hA => ?_⟩
  · rw [Function.update_of_ne (by omega)]; exact h.leaf x hx
  · by_cases hiJ : i = J
    · subst hiJ
      rw [Function.update_self]
      rcases better_mem (pr := pr) (key := key) (wn (2 * i)) (wn (2 * i + 1)) with e | e <;> rw [e]
      · obtain ⟨a, b⟩ := h.under (2 * i) (by omega) (by omega)
        exact ⟨a, anc_of_child (Or.inl b)⟩
      · obtain ⟨a, b⟩ := h.under (2 * i + 1) (by omega) (by omega)
        exact ⟨a, anc_of_child (Or.inr b)⟩
    · rw [Function.update_of_ne hiJ]; exact h.under i hi1 hi2
  · by_cases hiJ : i = J
    · subst hiJ
      rw [Function.update_self, Function.update_of_ne hc0, Function.update_of_ne hc1]
    · have hA' : ¬ Anc i J := fun h' => hA (anc_half h' hiJ)
      have e0 : 2 * i ≠ J := fun e => hA ⟨0, by simp; omega⟩
      have e1 : 2 * i + 1 ≠ J := fun e => hA ⟨0, by simp; omega⟩
      rw [Function.update_of_ne hiJ, Function.update_of_ne e0, Function.update_of_ne e1]
      exact h.eq i hi1 hi2 hA'

end FR

end Monge

end PlanarFlow
