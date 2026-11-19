module

public import PlanarFlow.NegSSSP.KEncConcrete

/-!
# The numberings of the one-face instance of a side, from prefix counts

The plain arrays read by `fencNatNL_Dk_exec` are indexed by numberings `σ₀ : DQ ≃ Fin #DQ`,
`νv₀ : VQ ≃ Fin #VQ`, `τ₀ : FQ ≃ Fin #FQ` of the darts, vertices and faces of the one-face
instance. For the instance `sideFD` of a side (the disc `discMap (kst N K) Z`), the machine
numbers them by **prefix counts** (`sdCnt fl y = Σ_{y' < y} fl y'`) of 0/1 flags over the codes of
the stellar subdivision:

* `sdCnt`, `sdCnt_lt`, `sdCnt_surj`, **`sd_equiv`**: a map `t : α → β` onto `β` whose fibres are
  those of a code `f : α → [0, n)`, the flags `fl` marking the codes hit, gives
  `e : β ≃ Fin #β` with `e (t a) = sdCnt fl (f a)` and `#β = sdCnt fl n`.
* `sdEq`, `sdOr` (branch-free equality test and disjunction on natural words, as the machine
  computes them), `sdEq_eq`, `sdOr_eq`.
* **`sd_face_iff`**: two darts of the disc `discMap M Z` (bounded by the simple cycle `C`) lie on
  the same face of the disc iff they lie on the same face of `M` in `Z`, or both on faces off `Z`
  (the outer face of the disc is the cycle).
* `sd_face_mem`: the face of a dart of the stellar subdivision is in `Z` iff the mark of its code
  divided by three is set (`stFn_face`).
* `sd_old_iff`: a dart of the stellar subdivision is old iff its code is divisible by three.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv Orbit CombMap Relation PlanarSeparator PlanarSeparator.Map
  PlanarSeparator.StDart BKMNW

universe u v w

/-! ### Prefix counts -/

/-- **The prefix count** of the flags `fl` below `n`. -/
def sdCnt (fl : ℕ → ℕ) (n : ℕ) : ℕ := ∑ y ∈ range n, fl y

@[simp] lemma sdCnt_zero (fl : ℕ → ℕ) : sdCnt fl 0 = 0 := by simp [sdCnt]

lemma sdCnt_succ (fl : ℕ → ℕ) (n : ℕ) : sdCnt fl (n + 1) = sdCnt fl n + fl n := by
  simp [sdCnt, sum_range_succ]

lemma sdCnt_mono (fl : ℕ → ℕ) {a b : ℕ} (h : a ≤ b) : sdCnt fl a ≤ sdCnt fl b := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [sdCnt_succ]; omega

lemma sdCnt_lt (fl : ℕ → ℕ) {a b : ℕ} (h : a < b) (ha : fl a = 1) : sdCnt fl a < sdCnt fl b := by
  have := sdCnt_mono fl (show a + 1 ≤ b from h)
  rw [sdCnt_succ] at this
  omega

lemma sdCnt_le {fl : ℕ → ℕ} {n : ℕ} (hfl : ∀ y < n, fl y ≤ 1) : sdCnt fl n ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sdCnt_succ]
    have := ih (fun y hy => hfl y (by omega))
    have := hfl n (by omega)
    omega

lemma sdCnt_congr {fl fl' : ℕ → ℕ} {n : ℕ} (h : ∀ y < n, fl y = fl' y) :
    sdCnt fl n = sdCnt fl' n :=
  sum_congr rfl fun y hy => h y (mem_range.1 hy)

lemma sdCnt_surj (fl : ℕ → ℕ) {n j : ℕ} (hfl : ∀ y < n, fl y ≤ 1) (hj : j < sdCnt fl n) :
    ∃ y < n, fl y = 1 ∧ sdCnt fl y = j := by
  induction n with
  | zero => simp at hj
  | succ n ih =>
    rw [sdCnt_succ] at hj
    by_cases h : j < sdCnt fl n
    · obtain ⟨y, hy, h1, h2⟩ := ih (fun y hy => hfl y (by omega)) h
      exact ⟨y, by omega, h1, h2⟩
    · have := hfl n (by omega)
      exact ⟨n, by omega, by omega, by omega⟩

/-- **Numbering by prefix counts.** A map `t : α → β` onto `β`, whose fibres are those of a code
`f : α → [0, n)`, with the flags `fl` (`0`/`1`) marking exactly the codes hit, gives a numbering
`e : β ≃ Fin #β` with `e (t a) = sdCnt fl (f a)`, and `#β = sdCnt fl n`. -/
theorem sd_equiv {α β : Type*} [Fintype β] (t : α → β) (ht : Surjective t) (f : α → ℕ)
    {n : ℕ} {fl : ℕ → ℕ} (hf : ∀ a b, t a = t b ↔ f a = f b) (hlt : ∀ a, f a < n)
    (hfl : ∀ y < n, fl y ≤ 1) (hp : ∀ y < n, fl y = 1 ↔ ∃ a, f a = y) :
    ∃ e : β ≃ Fin (Fintype.card β), Fintype.card β = sdCnt fl n ∧
      ∀ a, (e (t a) : ℕ) = sdCnt fl (f a) := by
  classical
  have hfa : ∀ a, fl (f a) = 1 := fun a => (hp _ (hlt a)).2 ⟨a, rfl⟩
  let g : β → Fin (sdCnt fl n) := fun b =>
    ⟨sdCnt fl (f (surjInv ht b)), sdCnt_lt fl (hlt _) (hfa _)⟩
  have hg : ∀ a, (g (t a) : ℕ) = sdCnt fl (f a) := by
    intro a
    show sdCnt fl (f (surjInv ht (t a))) = _
    rw [(hf _ _).1 (surjInv_eq ht (t a))]
  have hinj : Injective g := by
    intro b b' h
    have h' : sdCnt fl (f (surjInv ht b)) = sdCnt fl (f (surjInv ht b')) := congrArg Fin.val h
    have : f (surjInv ht b) = f (surjInv ht b') := by
      rcases lt_trichotomy (f (surjInv ht b)) (f (surjInv ht b')) with h1 | h1 | h1
      · exact absurd h' (ne_of_lt (sdCnt_lt fl h1 (hfa _)))
      · exact h1
      · exact absurd h'.symm (ne_of_lt (sdCnt_lt fl h1 (hfa _)))
    rw [← surjInv_eq ht b, ← surjInv_eq ht b']
    exact (hf _ _).2 this
  have hsurj : Surjective g := by
    intro j
    obtain ⟨y, hy, h1, h2⟩ := sdCnt_surj fl hfl j.2
    obtain ⟨a, rfl⟩ := (hp y hy).1 h1
    exact ⟨t a, Fin.ext ((hg a).trans h2)⟩
  have hcard : Fintype.card β = sdCnt fl n := by
    rw [Fintype.card_of_bijective ⟨hinj, hsurj⟩, Fintype.card_fin]
  refine ⟨(Equiv.ofBijective g ⟨hinj, hsurj⟩).trans (finCongr hcard.symm), hcard, fun a => ?_⟩
  rw [Equiv.trans_apply, finCongr_apply, Fin.val_cast]
  exact hg a

/-! ### Branch-free tests on natural words -/

lemma sd_ifP {α : Sort*} {p : Prop} [Decidable p] (h : p) {a b : α} :
    (if p then a else b) = a := by simp [h]

lemma sd_ifN {α : Sort*} {p : Prop} [Decidable p] (h : ¬ p) {a b : α} :
    (if p then a else b) = b := by simp [h]

/-- `1` if `a = b`, `0` otherwise, as the machine computes it. -/
def sdEq (a b : ℕ) : ℕ := 1 - ((a - b) + (b - a))

lemma sdEq_eq (a b : ℕ) : sdEq a b = if a = b then 1 else 0 := by
  unfold sdEq; split_ifs <;> omega

lemma sdEq_le (a b : ℕ) : sdEq a b ≤ 1 := by unfold sdEq; omega

/-- The disjunction of two flags. -/
def sdOr (a b : ℕ) : ℕ := a + b - a * b

lemma sdOr_eq (p q : Prop) [Decidable p] [Decidable q] :
    sdOr (if p then 1 else 0) (if q then 1 else 0) = if p ∨ q then 1 else 0 := by
  unfold sdOr; by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-! ### The faces of the disc -/

section DiscFace

variable {X P : Type*} [Fintype X] [DecidableEq X] [Fintype P] [DecidableEq P] {M : Map X P}
variable {C : M.SCycle} {Z : Finset M.Face}

lemma sd_pi_apply (x : X) :
    (dσ M Z * revPerm (combOfSep M)) x = dσ M Z (M.α x) := rfl

lemma sd_pow_in {a : X} (ha : M.face a ∈ Z) (n : ℕ) :
    ((dσ M Z * revPerm (combOfSep M)) ^ n) a = (M.φ ^ n) a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih, sd_pi_apply, pow_succ', Perm.mul_apply (M.φ),
      dσ_of_face (by rwa [face_φ_pow])]

lemma sd_pow_out {a : X} (h1 : M.face a ∉ Z) (h2 : M.face (M.α a) ∈ Z) (n : ℕ) :
    M.face (((dσ M Z * revPerm (combOfSep M)) ^ n) a) ∉ Z ∧
      M.face (M.α (((dσ M Z * revPerm (combOfSep M)) ^ n) a)) ∈ Z := by
  induction n with
  | zero => exact ⟨h1, h2⟩
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, sd_pi_apply]
    exact ⟨(dσ_outer ih.1 ih.2).1, (dσ_outer ih.1 ih.2).2.1⟩

/-- A dart of the disc on a face off `Z` is a dart of the oriented cycle `discCyc C Z`. -/
lemma sd_out_cyc (hl : ∀ d, M.vert (M.α d) ≠ M.vert d)
    (hbd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d) {a : X}
    (ha : a ∈ discDarts M Z) (h1 : M.face a ∉ Z) : ∃ i < C.k, (discCyc C Z).d i = a := by
  have h2 : M.face (M.α a) ∈ Z := by
    rcases mem_discDarts.1 ha with h | h
    · exact absurd h h1
    · exact h
  have hm : C.Mem a := by
    by_contra hn
    exact h1 (((hbd a).2 hn).2 h2)
  obtain ⟨i, hi, h | h⟩ := (discCyc_mem C Z a).2 hm
  · exact ⟨i, by rwa [discCyc_k] at hi, h.symm⟩
  · obtain ⟨hout, -⟩ := discCyc_spec hl hbd
    have := (hout i (by rwa [discCyc_k] at hi)).2
    rw [← h] at this
    exact absurd this h1

/-- **The faces of the disc**: two darts of the disc are on the same face of the disc iff they
are on the same face of `M` in `Z`, or both on faces off `Z` (then both on the cycle). -/
theorem sd_face_iff (hl : ∀ d, M.vert (M.α d) ≠ M.vert d)
    (hbd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d)
    (a b : SDart (discDarts M Z)) :
    (discMap M Z).face a = (discMap M Z).face b ↔
      (M.face a.1 ∈ Z ∧ M.face a.1 = M.face b.1) ∨ (M.face a.1 ∉ Z ∧ M.face b.1 ∉ Z) := by
  have e0 : (discMap M Z).face a = (discMap M Z).face b ↔
      (dσ M Z * revPerm (combOfSep M)).SameCycle a.1 b.1 := by
    rw [discMap, subMap_face, subMap_face, sVert_eq_iff]
  rw [e0]
  by_cases ha : M.face a.1 ∈ Z
  · have : (dσ M Z * revPerm (combOfSep M)).SameCycle a.1 b.1 ↔ M.face a.1 = M.face b.1 := by
      rw [M.face_eq_face_iff]
      constructor
      · intro h
        obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
        rw [sd_pow_in ha] at hn
        exact ⟨n, by rw [zpow_natCast]; exact hn⟩
      · intro h
        obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
        rw [← sd_pow_in ha] at hn
        exact ⟨n, by rw [zpow_natCast]; exact hn⟩
    rw [this]
    constructor
    · intro h; exact Or.inl ⟨ha, h⟩
    · rintro (h | h)
      · exact h.2
      · exact absurd ha h.1
  · have h2 : M.face (M.α a.1) ∈ Z := by
      rcases mem_discDarts.1 a.2 with h | h
      · exact absurd h ha
      · exact h
    constructor
    · intro h
      obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
      rw [← hn]
      exact Or.inr ⟨ha, (sd_pow_out ha h2 n).1⟩
    · rintro (h | ⟨-, hb⟩)
      · exact absurd h.1 ha
      · obtain ⟨i, hi, ei⟩ := sd_out_cyc hl hbd a.2 ha
        obtain ⟨j, hj, ej⟩ := sd_out_cyc hl hbd b.2 hb
        have hc := discFace_cycle hl hbd 0
        have ga : discFace hbd 0 i = a := Subtype.ext (by
          rw [discFace_val, zero_add, Nat.mod_eq_of_lt hi, ei])
        have gb : discFace hbd 0 j = b := Subtype.ext (by
          rw [discFace_val, zero_add, Nat.mod_eq_of_lt hj, ej])
        rw [← e0, ← ga, ← gb, hc.face i hi, hc.face j hj]

end DiscFace

/-! ### Codes of the stellar subdivision -/

section Codes

variable {X Q : Type*} [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q] {M : Map X Q}
  {m : ℕ}

/-- **The face of a dart of the stellar subdivision from its code**: it is the triangle of the
old dart numbered by the code divided by three. -/
lemma sd_face_old (c : X ≃ Fin m) (x : StDart X) :
    M.stellar.face x = M.stellar.face (old (c.symm ⟨M.stCode c x / 3, by
      have := (M.stCode c x).2; omega⟩)) := by
  apply (M.stFn c).injective
  apply Fin.ext
  rw [stFn_face, stFn_face]
  simp only [stCode_val, stNum, Equiv.apply_symm_apply]
  omega

/-- The code of an old dart. -/
lemma sd_code_old (c : X ≃ Fin m) (d : X) : (M.stCode c (old d) : ℕ) = 3 * c d := rfl

/-- **A dart of the stellar subdivision is old iff its code is divisible by three.** -/
lemma sd_old_iff (c : X ≃ Fin m) (x : StDart X) :
    (M.stCode c x : ℕ) % 3 = 0 ↔ ∃ d, x = old d := by
  constructor
  · intro h
    cases x with
    | old d => exact ⟨d, rfl⟩
    | up e => simp only [stCode_val, stNum] at h; omega
    | down d => simp only [stCode_val, stNum] at h; omega
  · rintro ⟨d, rfl⟩
    simp only [stCode_val, stNum]; omega

end Codes

end NegSSSP

end PlanarFlow
