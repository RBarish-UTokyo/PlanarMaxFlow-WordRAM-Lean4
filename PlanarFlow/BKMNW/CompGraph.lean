module

public import PlanarFlow.BKMNW.ExistCert

/-!
# The components off a hole as the components of a graph of degree three

`PlanarFlow.BKMNW.comp M N Hs Y x` (the darts reached from `x` in the piece map on the darts `N`
by steps to the reverse dart, or around a vertex off `Y`) is the component of a graph on the
indices `0, …, n-1` of an enumeration of `N` in which every index has three neighbour slots:
the index of the reverse dart (or itself if the reverse dart is not in `N`), the previous and the
next index of a dart with its tail off `Y` in the same class (or itself). No sorting is needed:
the previous indices come from one scan with a table of the last index seen per class.

* `lastF`, `nextF` (the last index before `j` of a class, the first one after `i` before `j`),
  their specifications; the slots `cgS1`, `cgS2`; the graph `cgAdj n rv key yf`;
* `cgS2_cgS1`, `cgS1_cgS2`, **`cgAdj_symm`**, **`cgAdj_conn`** (indices of a class off `Y` are
  connected), `cgAdj_cases`;
* **`mem_comp_iff_cgAdj`**: for an enumeration `e` of `N`, `rv`, `key`, `yf` describing the
  reverse darts, the classes of the tails and the tails in `Y` (`Y` closed under the holes),
  `e j ∈ comp M N Hs Y (e i) ↔ ReflTransGen (cgAdj n rv key yf) i j`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Relation

lemma cgIteT {α : Sort*} {p : Prop} [Decidable p] {a b : α} (h : p) :
    (if p then a else b) = a := by simp [h]

lemma cgIteF {α : Sort*} {p : Prop} [Decidable p] {a b : α} (h : ¬ p) :
    (if p then a else b) = b := by simp [h]

/-! ### The slots -/

section Slots

variable (key : ℕ → ℕ) (yf : ℕ → Bool)

/-- `1 +` the last index `< j` off `Y` of the class `k`, or `0`. -/
def lastF (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => if yf j = false ∧ key j = k then j + 1 else lastF k j

/-- `1 +` the first index in `(i, j)` off `Y` of the class of `i`, or `0`. -/
def nextF (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => if nextF i j = 0 ∧ i < j ∧ yf j = false ∧ key j = key i then j + 1 else nextF i j

/-- The previous index of the class (the index itself if none or in `Y`). -/
def cgS1 (i : ℕ) : ℕ := if yf i = false ∧ 0 < lastF key yf (key i) i then lastF key yf (key i) i - 1 else i

/-- The next index of the class below `n` (the index itself if none or in `Y`). -/
def cgS2 (n i : ℕ) : ℕ := if yf i = false ∧ 0 < nextF key yf i n then nextF key yf i n - 1 else i

/-- The graph: the reverse slot and the two class slots. -/
def cgAdj (n : ℕ) (rv : ℕ → ℕ) (i v : ℕ) : Prop :=
  i < n ∧ (v = rv i ∨ v = cgS1 key yf i ∨ v = cgS2 key yf n i)

variable {key yf}

lemma lastF_pos {k : ℕ} : ∀ {j i : ℕ}, lastF key yf k j = i + 1 → i < j ∧ yf i = false ∧
    key i = k ∧ ∀ i', i < i' → i' < j → ¬ (yf i' = false ∧ key i' = k)
  | 0, i, h => by simp [lastF] at h
  | j + 1, i, h => by
    unfold lastF at h
    by_cases hc : yf j = false ∧ key j = k
    · rw [cgIteT hc] at h
      obtain rfl : j = i := by omega
      exact ⟨by omega, hc.1, hc.2, fun i' h1 h2 => absurd h2 (by omega)⟩
    · rw [cgIteF hc] at h
      obtain ⟨a, b, d, f⟩ := lastF_pos h
      refine ⟨by omega, b, d, fun i' h1 h2 => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
      · exact f i' h1 h2
      · exact hc

lemma lastF_zero {k : ℕ} : ∀ {j : ℕ}, lastF key yf k j = 0 → ∀ i < j, ¬ (yf i = false ∧ key i = k)
  | 0, _, i, hi => absurd hi (by omega)
  | j + 1, h, i, hi => by
    unfold lastF at h
    by_cases hc : yf j = false ∧ key j = k
    · rw [cgIteT hc] at h; omega
    · rw [cgIteF hc] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact lastF_zero h i hi
      · exact hc

lemma nextF_zero {i : ℕ} : ∀ {j : ℕ}, nextF key yf i j = 0 → ∀ i', i < i' → i' < j →
    ¬ (yf i' = false ∧ key i' = key i)
  | 0, _, i', _, h2 => absurd h2 (by omega)
  | j + 1, h, i', h1, h2 => by
    unfold nextF at h
    by_cases hc : nextF key yf i j = 0 ∧ i < j ∧ yf j = false ∧ key j = key i
    · rw [cgIteT hc] at h; omega
    · rw [cgIteF hc] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
      · exact nextF_zero h i' h1 h2
      · intro hg; exact hc ⟨h, h1, hg⟩

lemma nextF_pos {i : ℕ} : ∀ {j i' : ℕ}, nextF key yf i j = i' + 1 → i < i' ∧ i' < j ∧
    yf i' = false ∧ key i' = key i ∧ ∀ i'', i < i'' → i'' < i' → ¬ (yf i'' = false ∧ key i'' = key i)
  | 0, i', h => by simp [nextF] at h
  | j + 1, i', h => by
    unfold nextF at h
    by_cases hc : nextF key yf i j = 0 ∧ i < j ∧ yf j = false ∧ key j = key i
    · rw [cgIteT hc] at h
      obtain rfl : j = i' := by omega
      refine ⟨hc.2.1, by omega, hc.2.2.1, hc.2.2.2, fun i'' h1 h2 => ?_⟩
      exact nextF_zero hc.1 i'' h1 h2
    · rw [cgIteF hc] at h
      obtain ⟨a, b, d, f, g⟩ := nextF_pos h
      exact ⟨a, by omega, d, f, g⟩

lemma cgS1_le (i : ℕ) : cgS1 key yf i ≤ i := by
  unfold cgS1; split_ifs with h
  · obtain ⟨p, hp⟩ : ∃ p, lastF key yf (key i) i = p + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h.2).symm⟩
    have := (lastF_pos hp).1; omega
  · exact le_rfl

lemma cgS1_ne {i : ℕ} (h : cgS1 key yf i ≠ i) : cgS1 key yf i < i ∧ yf i = false ∧
    yf (cgS1 key yf i) = false ∧ key (cgS1 key yf i) = key i ∧
    ∀ i', cgS1 key yf i < i' → i' < i → ¬ (yf i' = false ∧ key i' = key i) := by
  unfold cgS1 at h ⊢
  by_cases hc : yf i = false ∧ 0 < lastF key yf (key i) i
  · rw [cgIteT hc] at h ⊢
    obtain ⟨p, hp⟩ : ∃ p, lastF key yf (key i) i = p + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hc.2).symm⟩
    obtain ⟨a, b, d, f⟩ := lastF_pos hp
    rw [hp, Nat.add_sub_cancel]
    exact ⟨a, hc.1, b, d, f⟩
  · rw [cgIteF hc] at h; exact absurd rfl h

lemma cgS1_eq_self {i : ℕ} (h : cgS1 key yf i = i) (hy : yf i = false) :
    ∀ i' < i, ¬ (yf i' = false ∧ key i' = key i) := by
  unfold cgS1 at h
  by_cases hc : yf i = false ∧ 0 < lastF key yf (key i) i
  · rw [cgIteT hc] at h
    obtain ⟨p, hp⟩ : ∃ p, lastF key yf (key i) i = p + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hc.2).symm⟩
    have := (lastF_pos hp).1
    rw [hp] at h; omega
  · have h0 : lastF key yf (key i) i = 0 := by
      by_contra h0; exact hc ⟨hy, Nat.pos_of_ne_zero h0⟩
    exact lastF_zero h0

lemma cgS2_ne {n i : ℕ} (h : cgS2 key yf n i ≠ i) : i < cgS2 key yf n i ∧ cgS2 key yf n i < n ∧
    yf i = false ∧ yf (cgS2 key yf n i) = false ∧ key (cgS2 key yf n i) = key i ∧
    ∀ i', i < i' → i' < cgS2 key yf n i → ¬ (yf i' = false ∧ key i' = key i) := by
  unfold cgS2 at h ⊢
  by_cases hc : yf i = false ∧ 0 < nextF key yf i n
  · rw [cgIteT hc] at h ⊢
    obtain ⟨q, hq⟩ : ∃ q, nextF key yf i n = q + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hc.2).symm⟩
    obtain ⟨a, b, d, f, g⟩ := nextF_pos hq
    rw [hq, Nat.add_sub_cancel]
    exact ⟨a, b, hc.1, d, f, g⟩
  · rw [cgIteF hc] at h; exact absurd rfl h

lemma cgS2_eq_self {n i : ℕ} (h : cgS2 key yf n i = i) (hy : yf i = false) :
    ∀ i', i < i' → i' < n → ¬ (yf i' = false ∧ key i' = key i) := by
  unfold cgS2 at h
  by_cases hc : yf i = false ∧ 0 < nextF key yf i n
  · rw [cgIteT hc] at h
    obtain ⟨q, hq⟩ : ∃ q, nextF key yf i n = q + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hc.2).symm⟩
    have := (nextF_pos hq).1
    rw [hq] at h; omega
  · have h0 : nextF key yf i n = 0 := by
      by_contra h0; exact hc ⟨hy, Nat.pos_of_ne_zero h0⟩
    exact nextF_zero h0

lemma cgS2_le {n i : ℕ} (hi : i < n) : cgS2 key yf n i < n := by
  by_cases h : cgS2 key yf n i = i
  · rw [h]; exact hi
  · exact (cgS2_ne h).2.1

/-- The next of the previous index is the index. -/
lemma cgS2_cgS1 {n i : ℕ} (hi : i < n) (h : cgS1 key yf i ≠ i) :
    cgS2 key yf n (cgS1 key yf i) = i := by
  obtain ⟨a, b, d, f, g⟩ := cgS1_ne h
  set p := cgS1 key yf i
  by_cases hq : cgS2 key yf n p = p
  · have h' := cgS2_eq_self hq d i a hi
    rw [f] at h'
    exact absurd ⟨b, rfl⟩ h'
  · obtain ⟨a', b', d', f', g', k'⟩ := cgS2_ne hq
    rw [f] at g' k'
    rcases lt_trichotomy (cgS2 key yf n p) i with hl | he | hl
    · exact absurd ⟨f', g'⟩ (g _ a' hl)
    · exact he
    · exact absurd ⟨b, rfl⟩ (k' i a hl)

/-- The previous of the next index is the index. -/
lemma cgS1_cgS2 {n i : ℕ} (h : cgS2 key yf n i ≠ i) :
    cgS1 key yf (cgS2 key yf n i) = i := by
  obtain ⟨a, b, d, f, g, k⟩ := cgS2_ne h
  set q := cgS2 key yf n i
  by_cases hp : cgS1 key yf q = q
  · exact absurd ⟨d, g.symm⟩ (cgS1_eq_self hp f i a)
  · obtain ⟨a', b', d', f', g'⟩ := cgS1_ne hp
    rw [g] at f' g'
    rcases lt_trichotomy (cgS1 key yf q) i with hl | he | hl
    · exact absurd ⟨d, rfl⟩ (g' i hl a)
    · exact he
    · exact absurd ⟨d', f'⟩ (k _ hl a')

/-- The reverse slot: an involution of the indices. -/
def RvOK (n : ℕ) (rv : ℕ → ℕ) : Prop := ∀ i < n, rv i < n ∧ rv (rv i) = i

lemma cgAdj_lt {n : ℕ} {rv : ℕ → ℕ} (hrv : RvOK n rv) {i v : ℕ} (h : cgAdj key yf n rv i v) :
    v < n := by
  obtain ⟨hi, h | h | h⟩ := h
  · rw [h]; exact (hrv i hi).1
  · rw [h]; exact lt_of_le_of_lt (cgS1_le i) hi
  · rw [h]; exact cgS2_le hi

/-- **The graph is symmetric.** -/
lemma cgAdj_symm {n : ℕ} {rv : ℕ → ℕ} (hrv : RvOK n rv) {i v : ℕ}
    (h : cgAdj key yf n rv i v) : cgAdj key yf n rv v i := by
  have hv := cgAdj_lt hrv h
  obtain ⟨hi, h | h | h⟩ := h
  · subst h; exact ⟨hv, Or.inl (hrv i hi).2.symm⟩
  · by_cases he : cgS1 key yf i = i
    · rw [h, he]; exact ⟨hi, Or.inr (Or.inl he.symm)⟩
    · rw [h]; exact ⟨lt_of_le_of_lt (cgS1_le i) hi, Or.inr (Or.inr (cgS2_cgS1 hi he).symm)⟩
  · by_cases he : cgS2 key yf n i = i
    · rw [h, he]; exact ⟨hi, Or.inr (Or.inr he.symm)⟩
    · rw [h]; exact ⟨cgS2_le hi, Or.inr (Or.inl (cgS1_cgS2 he).symm)⟩

lemma cg_rtg_symm {r : ℕ → ℕ → Prop} (hs : ∀ u v, r u v → r v u) {u v : ℕ}
    (h : ReflTransGen r u v) : ReflTransGen r v u := by
  induction h with
  | refl => exact .refl
  | tail _ h2 ih => exact ReflTransGen.head (hs _ _ h2) ih

/-- **Indices of a class off `Y` are connected.** -/
lemma cgAdj_conn {n : ℕ} {rv : ℕ → ℕ} {k : ℕ} :
    ∀ i' i, i ≤ i' → i' < n → yf i = false → key i = k → yf i' = false → key i' = k →
      ReflTransGen (cgAdj key yf n rv) i i' := by
  intro i'
  induction i' using Nat.strong_induction_on with
  | _ i' ih =>
    intro i hii hi' hy hk hy' hk'
    rcases Nat.lt_or_eq_of_le hii with hlt | rfl
    · have hne : cgS1 key yf i' ≠ i' := fun he =>
        cgS1_eq_self he hy' i hlt ⟨hy, by rw [hk, hk']⟩
      obtain ⟨a, b, d, f, g⟩ := cgS1_ne hne
      have hpi : i ≤ cgS1 key yf i' := by
        by_contra hc
        exact g i (by omega) hlt ⟨hy, by rw [hk, hk']⟩
      have h1 := ih _ a i hpi (by omega) hy hk d (by rw [f, hk'])
      exact h1.tail ⟨by omega, Or.inr (Or.inr (cgS2_cgS1 hi' hne).symm)⟩
    · exact .refl

lemma cgAdj_conn' {n : ℕ} {rv : ℕ → ℕ} (hrv : RvOK n rv) {i i' : ℕ} (hi : i < n) (hi' : i' < n)
    (hy : yf i = false) (hy' : yf i' = false) (hk : key i = key i') :
    ReflTransGen (cgAdj key yf n rv) i i' := by
  rcases le_total i i' with h | h
  · exact cgAdj_conn i' i h hi' hy rfl hy' hk.symm
  · exact cg_rtg_symm (fun _ _ => cgAdj_symm hrv) (cgAdj_conn i i' h hi hy' rfl hy hk)

/-- The neighbours: the reverse slot, the index itself, or an index of the same class off `Y`. -/
lemma cgAdj_cases {n : ℕ} {rv : ℕ → ℕ} {i v : ℕ} (h : cgAdj key yf n rv i v) :
    v = rv i ∨ v = i ∨ (yf i = false ∧ yf v = false ∧ key v = key i) := by
  obtain ⟨hi, h | h | h⟩ := h
  · exact Or.inl h
  · by_cases he : cgS1 key yf i = i
    · exact Or.inr (Or.inl (h.trans he))
    · obtain ⟨_, b, d, f, _⟩ := cgS1_ne he
      subst h; exact Or.inr (Or.inr ⟨b, d, f⟩)
  · by_cases he : cgS2 key yf n i = i
    · exact Or.inr (Or.inl (h.trans he))
    · obtain ⟨_, _, b, d, f, _⟩ := cgS2_ne he
      subst h; exact Or.inr (Or.inr ⟨b, d, f⟩)

/-! ### One step of the scan -/

lemma lastF_succ (k j : ℕ) : lastF key yf k (j + 1) =
    if yf j = false ∧ key j = k then j + 1 else lastF key yf k j := rfl

lemma nextF_zero_le {i : ℕ} : ∀ j, j ≤ i + 1 → nextF key yf i j = 0
  | 0, _ => rfl
  | j + 1, h => by
    unfold nextF
    rw [nextF_zero_le j (by omega), cgIteF (by omega)]

lemma cgS2_self_succ (j : ℕ) : cgS2 key yf (j + 1) j = j := by
  unfold cgS2; rw [nextF_zero_le (j + 1) le_rfl, cgIteF (by omega)]

lemma nextF_succ_of_not {i j : ℕ}
    (h : ¬ (nextF key yf i j = 0 ∧ i < j ∧ yf j = false ∧ key j = key i)) :
    nextF key yf i (j + 1) = nextF key yf i j := by
  show (if _ then _ else _) = _; rw [cgIteF h]

lemma cgS2_succ_of_in {j : ℕ} (hy : yf j = true) (i : ℕ) :
    cgS2 key yf (j + 1) i = cgS2 key yf j i := by
  unfold cgS2
  rw [nextF_succ_of_not (fun h => by rw [hy] at h; exact Bool.noConfusion h.2.2.1)]

/-- At an index off `Y` with no earlier index of its class: no next index changes. -/
lemma cgS2_succ_of_zero {j : ℕ} (_hy : yf j = false) (h0 : lastF key yf (key j) j = 0) {i : ℕ}
    (hi : i < j) : cgS2 key yf (j + 1) i = cgS2 key yf j i := by
  by_cases hyi : yf i = false
  · unfold cgS2
    rw [nextF_succ_of_not (fun h => lastF_zero h0 i hi ⟨hyi, h.2.2.2.symm⟩)]
  · unfold cgS2
    have : ¬ (yf i = false) := hyi
    rw [cgIteF (fun h => this h.1), cgIteF (fun h => this h.1)]

/-- At an index off `Y` with the last earlier index `p` of its class: the next of `p` becomes
`j`, no other next index changes. -/
lemma cgS2_succ_of_pos {j p : ℕ} (hy : yf j = false) (hp : lastF key yf (key j) j = p + 1) :
    cgS2 key yf (j + 1) p = j ∧
      ∀ i < j, i ≠ p → cgS2 key yf (j + 1) i = cgS2 key yf j i := by
  obtain ⟨a, b, d, f⟩ := lastF_pos hp
  have hn0 : nextF key yf p j = 0 := by
    by_contra hc
    obtain ⟨q, hq⟩ : ∃ q, nextF key yf p j = q + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hc)).symm⟩
    obtain ⟨a', b', d', f', _⟩ := nextF_pos hq
    exact f q a' b' ⟨d', by rw [f', d]⟩
  refine ⟨?_, fun i hi hip => ?_⟩
  · unfold cgS2
    have h1 : nextF key yf p (j + 1) = j + 1 := by
      show (if _ then _ else _) = _
      rw [cgIteT ⟨hn0, a, hy, d.symm⟩]
    rw [h1, cgIteT ⟨b, by omega⟩]; rfl
  · by_cases hyi : yf i = false
    · unfold cgS2
      rw [nextF_succ_of_not (fun h => ?_)]
      obtain ⟨h1, h2, h3, h4⟩ := h
      -- `i` is a good index of the class with no good index in `(i, j)`: it is the last one
      rcases lt_trichotomy i p with hl | he | hl
      · exact nextF_zero h1 p hl a ⟨b, by rw [d, h4]⟩
      · exact hip he
      · exact f i hl hi ⟨hyi, by rw [← h4]⟩
    · unfold cgS2
      have : ¬ (yf i = false) := hyi
      rw [cgIteF (fun h => this h.1), cgIteF (fun h => this h.1)]

lemma cgS1_of_in {j : ℕ} (hy : yf j = true) : cgS1 key yf j = j := by
  unfold cgS1; rw [cgIteF (fun h => by rw [hy] at h; exact Bool.noConfusion h.1)]

lemma cgS1_of_zero {j : ℕ} (h0 : lastF key yf (key j) j = 0) : cgS1 key yf j = j := by
  unfold cgS1; rw [cgIteF (fun h => by omega)]

lemma cgS1_of_pos {j p : ℕ} (hy : yf j = false) (hp : lastF key yf (key j) j = p + 1) :
    cgS1 key yf j = p := by
  unfold cgS1; rw [cgIteT ⟨hy, by omega⟩, hp]; rfl

end Slots

/-! ### The components off a hole -/

section Bridge

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

variable (M) in
/-- An enumeration `e` of the darts `N` by the indices `< n`, with the reverse slot `rv`, the
class numbers `key` of the tails and the flags `yf` of the tails in `Y`. -/
structure CgEnum (N : Finset D) (Hs : List (Finset V)) (Y : Finset V) (n : ℕ) (e : ℕ → D)
    (rv key : ℕ → ℕ) (yf : ℕ → Bool) : Prop where
  mem : ∀ i < n, e i ∈ N
  surj : ∀ d ∈ N, ∃ i < n, e i = d
  inj : ∀ i < n, ∀ j < n, e i = e j → i = j
  rvlt : ∀ i < n, rv i < n
  rvin : ∀ i < n, M.rev (e i) ∈ N → e (rv i) = M.rev (e i)
  rvout : ∀ i < n, M.rev (e i) ∉ N → rv i = i
  key : ∀ i < n, ∀ j < n, (key i = key j ↔ HRel Hs (M.tail (e i)) (M.tail (e j)))
  yf : ∀ i < n, (yf i = true ↔ M.tail (e i) ∈ Y)

lemma CgEnum.rvOK {N : Finset D} {Hs : List (Finset V)} {Y : Finset V} {n : ℕ} {e : ℕ → D}
    {rv key : ℕ → ℕ} {yf : ℕ → Bool} (hE : CgEnum M N Hs Y n e rv key yf) : RvOK n rv := by
  intro i hi
  refine ⟨hE.rvlt i hi, ?_⟩
  by_cases hr : M.rev (e i) ∈ N
  · have h1 := hE.rvin i hi hr
    have h2 : M.rev (e (rv i)) ∈ N := by rw [h1, M.rev_rev]; exact hE.mem i hi
    have h3 := hE.rvin _ (hE.rvlt i hi) h2
    rw [h1, M.rev_rev] at h3
    exact hE.inj _ (hE.rvlt _ (hE.rvlt i hi)) _ hi h3
  · rw [hE.rvout i hi hr, hE.rvout i hi hr]

/-- **The components off `Y` are the components of the graph `cgAdj`.** -/
theorem mem_comp_iff_cgAdj {N : Finset D} {Hs : List (Finset V)} {Y : Finset V} {n : ℕ}
    {e : ℕ → D} {rv key : ℕ → ℕ} {yf : ℕ → Bool} (hY : HClosed Hs Y)
    (hE : CgEnum M N Hs Y n e rv key yf) {i j : ℕ} (hi : i < n) (hj : j < n) :
    e j ∈ comp M N Hs Y (e i) ↔ ReflTransGen (cgAdj key yf n rv) i j := by
  have hrv := hE.rvOK
  constructor
  · intro h
    have key' : ∀ b, ReflTransGen (AStep M N Hs Y) (e i) b →
        ∃ jb < n, e jb = b ∧ ReflTransGen (cgAdj key yf n rv) i jb := by
      intro b hb
      induction hb with
      | refl => exact ⟨i, hi, rfl, .refl⟩
      | @tail b c _ hst ih =>
        obtain ⟨jb, hjb, rfl, hr⟩ := ih
        obtain ⟨jc, hjc, rfl⟩ := hE.surj c hst.1
        refine ⟨jc, hjc, rfl, hr.trans ?_⟩
        rcases hst.2 with h1 | ⟨h1, h2⟩
        · have hin : M.rev (e jb) ∈ N := h1 ▸ hst.1
          have := hE.rvin jb hjb hin
          rw [← h1] at this
          have hj' := hE.inj _ (hE.rvlt jb hjb) _ hjc this
          exact .single ⟨hjb, Or.inl hj'.symm⟩
        · have hyb : yf jb = false := by
            by_contra hc
            exact h2 ((hE.yf jb hjb).1 (by simpa using hc))
          have hyc : yf jc = false := by
            by_contra hc
            have hcY := (hE.yf jc hjc).1 (by simpa using hc)
            exact h2 (hY _ hcY _ (hRel_symm h1))
          exact cgAdj_conn' hrv hjb hjc hyb hyc ((hE.key jb hjb jc hjc).2 h1)
    obtain ⟨jb, hjb, he, hr⟩ := key' _ (mem_comp.1 h).2
    rwa [hE.inj _ hjb _ hj he] at hr
  · intro h
    have key' : ∀ b, ReflTransGen (cgAdj key yf n rv) i b →
        b < n ∧ ReflTransGen (AStep M N Hs Y) (e i) (e b) := by
      intro b hb
      induction hb with
      | refl => exact ⟨hi, .refl⟩
      | @tail b c _ hst ih =>
        obtain ⟨hb, hr⟩ := ih
        have hc := cgAdj_lt hrv hst
        refine ⟨hc, ?_⟩
        rcases cgAdj_cases hst with h1 | h1 | ⟨h1, h2, h3⟩
        · by_cases hin : M.rev (e b) ∈ N
          · refine hr.tail ⟨hE.mem c hc, Or.inl ?_⟩
            rw [h1, hE.rvin b hb hin]
          · rw [h1, hE.rvout b hb hin]; exact hr
        · rw [h1]; exact hr
        · refine hr.tail ⟨hE.mem c hc, Or.inr ⟨(hE.key b hb c hc).1 h3.symm, fun hY' => ?_⟩⟩
          have := (hE.yf b hb).2 hY'
          rw [h1] at this; exact Bool.false_ne_true this
    exact mem_comp.2 ⟨hE.mem j hj, (key' j h).2⟩

end Bridge

end BKMNW

end PlanarFlow
