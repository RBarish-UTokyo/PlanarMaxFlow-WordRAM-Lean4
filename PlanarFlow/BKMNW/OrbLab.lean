module

public import WordRAM

/-!
# Orbit labels of a permutation array on the machine

For a function `f : ℕ → ℕ` mapping `[0, m)` injectively into itself (a permutation of `[0, m)`,
e.g. the face permutation of a map given by its index arrays), the **orbit label** `olab f i` is
the least element of the forward orbit `{f^[t] i}` of `i`. On `[0, m)` it is constant on the
cycles of `f` and injective on the set of cycles, so it is an identifier of the cycle (e.g. of the
face of a dart), below `m`.

* pure part: `olab`, `olab_le`, `olab_mem`, `olab_min`, `iter_lt`, `iter_period`, `iter_back`,
  **`olab_iter`** (`olab f (f^[t] i) = olab f i` on `[0, m)`), `olab_lt`, `olab_olab`,
  **`olab_eq_iff`** (two points of `[0, m)` have the same label iff they lie on the same cycle);
* **`olProg`**: for `i = 0 … m - 1`, if `LAB[i] = 0`, walk the cycle of `i` writing `i + 1`
  (`PHI` at `r7350`, `LAB` at `r7351`, `m` in `r7352`, scratch registers `7400 … 7405`);
* **`olProg_exec`**: from `LAB` all zero, within `20 m + 4` steps, `LAB[x] = olab f x + 1` for
  every `x < m` (`f x = PHI[x]`), all other memory, the reals and the output kept, the registers
  outside `7400 … 7405` kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace OrbLab

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### Orbit labels -/

/-- **The orbit label**: the least element of the forward orbit of `i` under `f`. -/
noncomputable def olab (f : ℕ → ℕ) (i : ℕ) : ℕ := by
  classical exact Nat.find (⟨i, 0, rfl⟩ : ∃ j, ∃ t, f^[t] i = j)

variable {f : ℕ → ℕ} {m : ℕ}

theorem olab_mem (f : ℕ → ℕ) (i : ℕ) : ∃ t, f^[t] i = olab f i := by
  classical
  unfold olab
  exact Nat.find_spec (⟨i, 0, rfl⟩ : ∃ j, ∃ t, f^[t] i = j)

theorem olab_min (f : ℕ → ℕ) (i t : ℕ) : olab f i ≤ f^[t] i := by
  classical
  unfold olab
  exact Nat.find_min' _ ⟨t, rfl⟩

theorem olab_le (f : ℕ → ℕ) (i : ℕ) : olab f i ≤ i := olab_min f i 0

/-- The hypotheses: `f` maps `[0, m)` injectively into itself. -/
structure PermOn (f : ℕ → ℕ) (m : ℕ) : Prop where
  lt : ∀ x < m, f x < m
  inj : ∀ x < m, ∀ y < m, f x = f y → x = y

theorem iter_lt (h : PermOn f m) {i : ℕ} (hi : i < m) : ∀ t, f^[t] i < m
  | 0 => hi
  | t + 1 => by rw [Function.iterate_succ_apply']; exact h.lt _ (iter_lt h hi t)

theorem iter_inj (h : PermOn f m) {x y : ℕ} (hx : x < m) (hy : y < m) :
    ∀ t, f^[t] x = f^[t] y → x = y
  | 0, e => e
  | t + 1, e => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at e
      exact iter_inj h hx hy t (h.inj _ (iter_lt h hx t) _ (iter_lt h hy t) e)

/-- **Every point of `[0, m)` is periodic.** -/
theorem iter_period (h : PermOn f m) {i : ℕ} (hi : i < m) : ∃ p, 0 < p ∧ f^[p] i = i := by
  classical
  obtain ⟨a, ha, b, hb, hab, e⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := range (m + 1)) (t := range m) (f := fun t => f^[t] i) (by simp)
    (fun t _ => by simp only [coe_range, Set.mem_Iio]; exact iter_lt h hi t)
  simp only [coe_range, Set.mem_Iio, mem_range] at ha hb
  rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
  · refine ⟨b - a, by omega, ?_⟩
    have e' : f^[a] (f^[b - a] i) = f^[a] i := by
      rw [← Function.iterate_add_apply, show a + (b - a) = b by omega]; exact e.symm
    exact iter_inj h (iter_lt h hi _) hi a e'
  · refine ⟨a - b, by omega, ?_⟩
    have e' : f^[b] (f^[a - b] i) = f^[b] i := by
      rw [← Function.iterate_add_apply, show b + (a - b) = a by omega]; exact e
    exact iter_inj h (iter_lt h hi _) hi b e'

theorem iter_mul_period {i p : ℕ} (hp : f^[p] i = i) : ∀ q, f^[p * q] i = i
  | 0 => by simp
  | q + 1 => by rw [Nat.mul_succ, Function.iterate_add_apply, hp, iter_mul_period hp q]

/-- **The way back**: from every point of the orbit of `i` (in `[0, m)`) one returns to `i`. -/
theorem iter_back (h : PermOn f m) {i : ℕ} (hi : i < m) (t : ℕ) : ∃ u, f^[u] (f^[t] i) = i := by
  obtain ⟨p, hp, e⟩ := iter_period h hi
  refine ⟨p * t - t, ?_⟩
  rw [← Function.iterate_add_apply, show p * t - t + t = p * t by
    have : t ≤ p * t := Nat.le_mul_of_pos_left t hp
    omega]
  exact iter_mul_period e t

/-- **The label is constant along the orbit.** -/
theorem olab_iter (h : PermOn f m) {i : ℕ} (hi : i < m) (t : ℕ) :
    olab f (f^[t] i) = olab f i := by
  apply le_antisymm
  · obtain ⟨u, hu⟩ := iter_back h hi t
    obtain ⟨a, ha⟩ := olab_mem f i
    calc olab f (f^[t] i) ≤ f^[a + u] (f^[t] i) := olab_min _ _ _
      _ = olab f i := by rw [Function.iterate_add_apply, hu, ha]
  · obtain ⟨a, ha⟩ := olab_mem f (f^[t] i)
    calc olab f i ≤ f^[a + t] i := olab_min _ _ _
      _ = olab f (f^[t] i) := by rw [Function.iterate_add_apply, ha]

theorem olab_lt (h : PermOn f m) {i : ℕ} (hi : i < m) : olab f i < m :=
  lt_of_le_of_lt (olab_le f i) hi

theorem olab_olab (h : PermOn f m) {i : ℕ} (hi : i < m) : olab f (olab f i) = olab f i := by
  obtain ⟨t, ht⟩ := olab_mem f i
  rw [← ht, olab_iter h hi t]
  exact ht.symm

/-- **Two points have the same label iff they lie on the same cycle.** -/
theorem olab_eq_iff (h : PermOn f m) {i j : ℕ} (hi : i < m) (hj : j < m) :
    olab f i = olab f j ↔ ∃ t, f^[t] i = j := by
  constructor
  · intro e
    obtain ⟨a, ha⟩ := olab_mem f i
    obtain ⟨b, hb⟩ := olab_mem f j
    obtain ⟨u, hu⟩ := iter_back h hj b
    refine ⟨u + a, ?_⟩
    rw [Function.iterate_add_apply, ha, e, ← hb, hu]
  · rintro ⟨t, rfl⟩
    exact (olab_iter h hi t).symm

/-- On an eventually repeating walk, every point of the orbit is reached before the repeat. -/
theorem iter_lt_of_rep {i s t : ℕ} (hst : s < t) (e : f^[t] i = f^[s] i) :
    ∀ n, ∃ n' < t, f^[n] i = f^[n'] i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < t
    · exact ⟨n, hn, rfl⟩
    · obtain ⟨n', hn', e'⟩ := ih (n - t + s) (by omega)
      have key : f^[n] i = f^[n - t + s] i := by
        have h1 : f^[n] i = f^[n - t] (f^[t] i) := by
          rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
        rw [h1, e, ← Function.iterate_add_apply]
      exact ⟨n', hn', key.trans e'⟩

/-! ### The program -/

/-- `LAB[j] := lab`, `j := PHI[j]`, `x := LAB[j]`. -/
def olStep : Stmt := block [.addN 7402 7351 7405, .storeN 7402 7404, .addN 7402 7350 7405,
  .loadN 7405 7402, .addN 7402 7351 7405, .loadN 7403 7402]

/-- `lab := i + 1`, `j := i`, `x := 0`. -/
def olSet : Stmt := block [.addN 7404 7400 7401, .copyN 7405 7400, .constN 7403 0]

/-- Walk the cycle of `i`: `lab := i + 1`, `j := i`, `x := 0`, then step while `x = 0`. -/
def olWalk : Stmt := .seq olSet (.whileLtN 7403 7401 olStep)

/-- `x := LAB[i]`. -/
def olRd : Stmt := block [.addN 7402 7351 7400, .loadN 7403 7402]

/-- `i := i + 1`. -/
def olInc : Stmt := block [.addN 7400 7400 7401]

/-- One point `i`: walk its cycle if it is not labelled; `i := i + 1`. -/
def olBody : Stmt := .seq olRd (.seq (.ifLtN 7403 7401 olWalk .skip) olInc)

/-- `i := 0`, `ONE := 1`. -/
def olInit : Stmt := block [.constN 7400 0, .constN 7401 1]

/-- **The orbit labelling** of the permutation array `PHI = r7350` into `LAB = r7351`
(`m = r7352`). -/
def olProg : Stmt := .seq olInit (.whileLtN 7400 7352 olBody)

/-! ### The runs -/

/-- The loop rule with the potential left over. -/
theorem whileLtN_potL {P : Input} {W : ℕ} {a b : ℕ} {body : Stmt} (I : Config → Prop)
    (Φ : Config → ℕ) (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ Φ c' + k + 2 ≤ Φ c)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W (.whileLtN a b body) c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k + Φ c' ≤ Φ c + 2 := by
  induction hn : Φ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    by_cases ht : c.nreg a < c.nreg b
    · obtain ⟨c₁, k₁, hb, hI₁, hΦ⟩ := hbody c hc ht
      obtain ⟨c', k₂, hl, hI', ht', hk₂⟩ := ih (Φ c₁) (by omega) hI₁ rfl
      exact ⟨c', k₁ + 2 + k₂, .whileLtN_true ht hb hl, hI', ht', by omega⟩
    · exact ⟨c, 2, .whileLtN_false ht (hI c hc), hc, ht, by omega⟩

/-- The number of unlabelled points. -/
noncomputable def zeros (mem : ℕ → ℕ) (Lb m : ℕ) : ℕ :=
  ∑ x ∈ range m, if mem (Lb + x) = 0 then 1 else 0

theorem zeros_upd {mem : ℕ → ℕ} {Lb m y v : ℕ} (hy : y < m) (h0 : mem (Lb + y) = 0)
    (hv : v ≠ 0) : zeros (upd mem (Lb + y) v) Lb m + 1 = zeros mem Lb m := by
  unfold zeros
  rw [← Finset.add_sum_erase (range m) _ (mem_range.2 hy),
    ← Finset.add_sum_erase (range m) (fun x => if mem (Lb + x) = 0 then 1 else 0)
      (mem_range.2 hy)]
  have e : ∀ x ∈ (range m).erase y, (if upd mem (Lb + y) v (Lb + x) = 0 then 1 else 0) =
      (if mem (Lb + x) = 0 then 1 else 0) := fun x hx => by
    have hxy : x ≠ y := (mem_erase.1 hx).1
    have : Lb + x ≠ Lb + y := by omega
    simp only [upd_apply, this, ↓reduceIte]
  rw [Finset.sum_congr rfl e]
  simp only [upd_apply, ↓reduceIte, hv, h0]
  omega

theorem zeros_le (mem : ℕ → ℕ) (Lb m : ℕ) : zeros mem Lb m ≤ m := by
  unfold zeros
  calc (∑ x ∈ range m, if mem (Lb + x) = 0 then 1 else 0) ≤ ∑ x ∈ range m, 1 :=
        Finset.sum_le_sum fun x _ => by split_ifs <;> omega
    _ = m := by simp

theorem zeros_all {mem : ℕ → ℕ} {Lb m : ℕ} (h : ∀ x < m, mem (Lb + x) = 0) :
    zeros mem Lb m = m := by
  unfold zeros
  have e : ∀ x ∈ range m, (if mem (Lb + x) = 0 then 1 else 0) = 1 := fun x hx => by
    simp only [h x (mem_range.1 hx), ↓reduceIte]
  rw [Finset.sum_congr rfl e]
  simp

variable {P : Input} {W : ℕ}

theorem olStep_exec (c : Config) (hc : WordsBounded W c) {Pb Lb j v : ℕ}
    (r50 : c.nreg 7350 = Pb) (r51 : c.nreg 7351 = Lb) (r04 : c.nreg 7404 = v)
    (r05 : c.nreg 7405 = j) (hdis : Lb + j ≠ Pb + j) (w1 : Lb + j ≤ W) (w2 : Pb + j ≤ W)
    (w3 : Lb + c.nmem (Pb + j) ≤ W) :
    ∃ c' t, Exec P W olStep c c' t ∧ t = 6 ∧ c'.nmem = upd c.nmem (Lb + j) v ∧
      c'.nreg 7405 = c.nmem (Pb + j) ∧
      c'.nreg 7403 = upd c.nmem (Lb + j) v (Lb + c.nmem (Pb + j)) ∧
      (∀ r, r ≠ 7402 → r ≠ 7403 → r ≠ 7405 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hp : upd c.nmem (Lb + j) v (Pb + j) = c.nmem (Pb + j) := by
    simp only [upd_apply, Ne.symm hdis, ↓reduceIte]
  unfold olStep
  exec_block
  all_goals try ((try config_simp); (try simp only [r50, r51, r04, r05, hp]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r50, r51, r04, r05, hp])
  simp only [upd_apply]; split_ifs <;> omega

theorem olRd_exec (c : Config) (hc : WordsBounded W c) {Lb i : ℕ} (r51 : c.nreg 7351 = Lb)
    (r00 : c.nreg 7400 = i) (hW : Lb + i ≤ W) :
    ∃ c' k, Exec P W olRd c c' k ∧ k = 2 ∧ c'.nreg 7403 = c.nmem (Lb + i) ∧
      (∀ r, r ≠ 7402 → r ≠ 7403 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold olRd
  exec_block
  all_goals try ((try config_simp); (try simp only [r51, r00]); omega)
  refine ⟨rfl, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r51, r00])
  simp only [upd_apply]; split_ifs <;> omega

theorem olSet_exec (c : Config) (hc : WordsBounded W c) {i : ℕ} (r00 : c.nreg 7400 = i)
    (r01 : c.nreg 7401 = 1) (hW : i + 1 ≤ W) :
    ∃ c' k, Exec P W olSet c c' k ∧ k = 3 ∧ c'.nreg 7404 = i + 1 ∧ c'.nreg 7405 = i ∧
      c'.nreg 7403 = 0 ∧ (∀ r, r ≠ 7403 → r ≠ 7404 → r ≠ 7405 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold olSet
  exec_block
  all_goals try ((try config_simp); (try simp only [r00, r01]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r00, r01])
  simp only [upd_apply]; split_ifs <;> omega

theorem olInc_exec (c : Config) (hc : WordsBounded W c) {i : ℕ} (r00 : c.nreg 7400 = i)
    (r01 : c.nreg 7401 = 1) (hW : i + 1 ≤ W) :
    ∃ c' k, Exec P W olInc c c' k ∧ k = 1 ∧ c'.nreg 7400 = i + 1 ∧
      (∀ r, r ≠ 7400 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold olInc
  exec_block
  all_goals try ((try config_simp); (try simp only [r00, r01]); omega)
  refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r00, r01])
  simp only [upd_apply]; split_ifs <;> omega

theorem olInit_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W olInit c c' k ∧ k = 2 ∧ c'.nreg 7400 = 0 ∧ c'.nreg 7401 = 1 ∧
      (∀ r, r ≠ 7400 → r ≠ 7401 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold olInit
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

/-- The labels before the point `i`: `olab f x + 1` if `olab f x < i`, else `0`. -/
noncomputable def labV (f : ℕ → ℕ) (i x : ℕ) : ℕ := if olab f x < i then olab f x + 1 else 0

/-- The invariant of the walk of the cycle of `i` after `t` steps. -/
def WalkInv (f : ℕ → ℕ) (m Pb Lb i : ℕ) (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ c.nreg 7350 = Pb ∧ c.nreg 7351 = Lb ∧ c.nreg 7404 = i + 1 ∧
  ∃ t, c.nreg 7405 = f^[t] i ∧ c.nreg 7403 = c.nmem (Lb + f^[t] i) ∧
    (∀ x < m, c.nmem (Lb + x) =
      if olab f x < i then olab f x + 1 else if ∃ s < t, f^[s] i = x then i + 1 else 0) ∧
    (∀ a, (a < Lb ∨ Lb + m ≤ a) → c.nmem a = c₀.nmem a) ∧
    (∀ r, r ≠ 7402 → r ≠ 7403 → r ≠ 7405 → c.nreg r = c₀.nreg r) ∧ c.rreg = c₀.rreg ∧
    c.rmem = c₀.rmem ∧ c.output = c₀.output

/-- **The walk of the cycle of `i`** (`olab f i = i`, the cycle unlabelled): every point of the
cycle gets the label `i + 1`; the potential `8 · zeros` pays the steps. -/
theorem walk_loop (hp : PermOn f m) {Pb Lb i : ℕ} (hi : i < m) (hli : olab f i = i)
    (hPL : Pb + m ≤ Lb) (hW : Lb + m ≤ W) {c₀ : Config} (h1 : c₀.nreg 7401 = 1)
    (hf : ∀ x < m, c₀.nmem (Pb + x) = f x) {c : Config}
    (hc : WalkInv (W := W) f m Pb Lb i c₀ c) :
    ∃ c' k, Exec P W (.whileLtN 7403 7401 olStep) c c' k ∧
      k + 8 * zeros c'.nmem Lb m ≤ 8 * zeros c.nmem Lb m + 2 ∧
      (∀ x < m, c'.nmem (Lb + x) = labV f (i + 1) x) ∧
      (∀ a, (a < Lb ∨ Lb + m ≤ a) → c'.nmem a = c₀.nmem a) ∧
      (∀ r, r ≠ 7402 → r ≠ 7403 → r ≠ 7405 → c'.nreg r = c₀.nreg r) ∧ c'.rreg = c₀.rreg ∧
      c'.rmem = c₀.rmem ∧ c'.output = c₀.output := by
  obtain ⟨c', k, ex, hI, hstop, hk⟩ := whileLtN_potL (P := P) (W := W) (a := 7403) (b := 7401)
    (body := olStep) (WalkInv (W := W) f m Pb Lb i c₀)
    (fun c => 8 * zeros c.nmem Lb m) (fun c h => h.1)
    (fun c ⟨hw, r50, r51, r04, t, r05, r03, hL, hM, hR, hrr, hrm, ho⟩ hlt => by
      have hj : f^[t] i < m := iter_lt hp hi t
      have hPj : c.nmem (Pb + f^[t] i) = f^[t + 1] i := by
        rw [hM _ (Or.inl (by omega)), hf _ hj, Function.iterate_succ_apply']
      have hj1 : f^[t + 1] i < m := iter_lt hp hi (t + 1)
      obtain ⟨c₁, k₁, e₁, hk₁, m₁, s05, s03, sR, srr, srm, so⟩ :=
        olStep_exec (P := P) c hw r50 r51 r04 r05 (by omega) (by omega) (by omega)
          (by rw [hPj]; omega)
      have h0 : c.nmem (Lb + f^[t] i) = 0 := by
        have h01 : c.nreg 7401 = 1 := by rw [hR 7401 (by omega) (by omega) (by omega), h1]
        rw [r03, h01] at hlt; omega
      have hlj : olab f (f^[t] i) = i := by rw [olab_iter hp hi t, hli]
      refine ⟨c₁, k₁, e₁, ⟨e₁.wb_right, by rw [sR _ (by omega) (by omega) (by omega), r50],
        by rw [sR _ (by omega) (by omega) (by omega), r51],
        by rw [sR _ (by omega) (by omega) (by omega), r04], t + 1, by rw [s05, hPj],
        by rw [s03, hPj, m₁], fun x hx => ?_, fun a ha => ?_, fun r h1 h2 h3 => ?_,
        by rw [srr, hrr], by rw [srm, hrm], by rw [so, ho]⟩, ?_⟩
      · rw [m₁]
        by_cases hxj : x = f^[t] i
        · subst hxj
          have hn : ¬ olab f (f^[t] i) < i := by omega
          have hex : ∃ s < t + 1, f^[s] i = f^[t] i := ⟨t, by omega, rfl⟩
          simp only [upd_apply, ↓reduceIte, hn, hex]
        · have hne : Lb + x ≠ Lb + f^[t] i := by omega
          simp only [upd_apply, hne, ↓reduceIte]
          rw [hL x hx]
          have hiff : (∃ s < t + 1, f^[s] i = x) ↔ (∃ s < t, f^[s] i = x) := by
            constructor
            · rintro ⟨s, hs, e⟩
              rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
              · exact ⟨s, hs, e⟩
              · exact absurd e.symm hxj
            · rintro ⟨s, hs, e⟩; exact ⟨s, by omega, e⟩
          simp only [hiff]
      · rw [m₁, upd_apply]
        have : a ≠ Lb + f^[t] i := by omega
        simp only [this, ↓reduceIte]; exact hM a ha
      · rw [sR r h1 h2 h3, hR r h1 h2 h3]
      · have := zeros_upd (mem := c.nmem) (Lb := Lb) (v := i + 1) hj h0 (by omega)
        rw [m₁]; omega)
    hc
  obtain ⟨hw, r50, r51, r04, t, r05, r03, hL, hM, hR, hrr, hrm, ho⟩ := hI
  have h1' : c'.nreg 7401 = 1 := by rw [hR 7401 (by omega) (by omega) (by omega), h1]
  have hne : c'.nmem (Lb + f^[t] i) ≠ 0 := by
    have : ¬ c'.nreg 7403 < c'.nreg 7401 := hstop
    rw [r03, h1'] at this; omega
  have hj := iter_lt hp hi t
  have hlj : olab f (f^[t] i) = i := by rw [olab_iter hp hi t, hli]
  obtain ⟨s, hs, es⟩ : ∃ s < t, f^[s] i = f^[t] i := by
    by_contra hno
    have := hL _ hj
    have hn : ¬ olab f (f^[t] i) < i := by omega
    simp only [hn, hno, ↓reduceIte] at this
    exact hne this
  refine ⟨c', k, ex, hk, fun x hx => ?_, hM, hR, hrr, hrm, ho⟩
  rw [hL x hx]
  unfold labV
  by_cases h1x : olab f x < i
  · have : olab f x < i + 1 := by omega
    simp only [h1x, this, ↓reduceIte]
  · by_cases h2x : olab f x = i
    · obtain ⟨u, hu⟩ : ∃ u, f^[u] i = x := (olab_eq_iff hp hi hx).1 (by rw [hli, h2x])
      obtain ⟨u', hu', e'⟩ := iter_lt_of_rep hs es.symm u
      have hex : ∃ s < t, f^[s] i = x := ⟨u', hu', by rw [← e', hu]⟩
      have : olab f x < i + 1 := by omega
      simp only [h1x, this, ↓reduceIte, hex]
      omega
    · have hno : ¬ ∃ s < t, f^[s] i = x := by
        rintro ⟨s, -, rfl⟩
        exact h2x (by rw [olab_iter hp hi s, hli])
      have : ¬ olab f x < i + 1 := by omega
      simp only [h1x, this, ↓reduceIte, hno]

/-- **One point `i` of the outer loop**: the labels before `i` become the labels before
`i + 1`. -/
theorem olBody_exec (hp : PermOn f m) {Pb Lb i : ℕ} (hi : i < m) (hPL : Pb + m ≤ Lb)
    (hW : Lb + m ≤ W) (c : Config) (hc : WordsBounded W c) (r50 : c.nreg 7350 = Pb)
    (r51 : c.nreg 7351 = Lb) (r00 : c.nreg 7400 = i) (r01 : c.nreg 7401 = 1)
    (hf : ∀ x < m, c.nmem (Pb + x) = f x) (hL : ∀ x < m, c.nmem (Lb + x) = labV f i x) :
    ∃ c' k, Exec P W olBody c c' k ∧
      k + 8 * zeros c'.nmem Lb m + 2 ≤ 8 * zeros c.nmem Lb m + 12 ∧ c'.nreg 7400 = i + 1 ∧
      c'.nreg 7401 = 1 ∧ (∀ x < m, c'.nmem (Lb + x) = labV f (i + 1) x) ∧
      (∀ a, (a < Lb ∨ Lb + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 7400 ∨ 7405 < r) → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  -- `x := LAB[i]`
  obtain ⟨c₁, k₁, e₁, hk₁, a03, aR, am, ar, arm, ao⟩ :=
    olRd_exec (P := P) c hc r51 r00 (by omega)
  -- the test and the walk
  obtain ⟨c₂, k₂, e₂, hk₂, b00, b01, bL, bM, bR, brr, brm, bo⟩ : ∃ c₂ k₂, Exec P W
      (.ifLtN 7403 7401 olWalk .skip) c₁ c₂ k₂ ∧
      k₂ + 8 * zeros c₂.nmem Lb m ≤ 8 * zeros c.nmem Lb m + 6 ∧ c₂.nreg 7400 = i ∧
      c₂.nreg 7401 = 1 ∧
      (∀ x < m, c₂.nmem (Lb + x) = labV f (i + 1) x) ∧
      (∀ a, (a < Lb ∨ Lb + m ≤ a) → c₂.nmem a = c.nmem a) ∧
      (∀ r, (r < 7400 ∨ 7405 < r) → c₂.nreg r = c.nreg r) ∧ c₂.rreg = c.rreg ∧
      c₂.rmem = c.rmem ∧ c₂.output = c.output := by
    have h1 : c₁.nreg 7401 = 1 := by rw [aR _ (by omega) (by omega), r01]
    by_cases h0 : c.nmem (Lb + i) = 0
    · -- the cycle of `i` is unlabelled: `i` is its least point
      have hli : olab f i = i := by
        have := hL i hi
        rw [h0] at this
        unfold labV at this
        have := olab_le f i
        split_ifs at * <;> omega
      refine spec_ifLtN_true (by rw [a03, h1, h0]; omega) ?_
      have r00' : c₁.nreg 7400 = i := by rw [aR _ (by omega) (by omega), r00]
      obtain ⟨c₃, k₃, e₃, hk₃, d04, d05, d03, dR, dm, dr, drm, do'⟩ :=
        olSet_exec (P := P) c₁ e₁.wb_right r00' h1 (by omega)
      have hWI : WalkInv (W := W) f m Pb Lb i c₃ c₃ := by
        refine ⟨e₃.wb_right, by rw [dR _ (by omega) (by omega) (by omega),
          aR _ (by omega) (by omega), r50], by rw [dR _ (by omega) (by omega) (by omega),
          aR _ (by omega) (by omega), r51], d04, 0, by rw [d05]; rfl,
          by rw [d03, dm, am]; simp only [Function.iterate_zero, id_eq]; exact h0.symm,
          fun x hx => ?_, fun _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl, rfl⟩
        rw [dm, am, hL x hx]
        unfold labV
        simp only [Nat.not_lt_zero, false_and, exists_false, ↓reduceIte]
      obtain ⟨c₄, k₄, e₄, hk₄, hL₄, hM₄, hR₄, hrr₄, hrm₄, ho₄⟩ :=
        walk_loop (P := P) hp hi hli hPL hW (by rw [dR _ (by omega) (by omega) (by omega), h1])
          (fun x hx => by rw [dm, am]; exact hf x hx) hWI
      have hz₃ : zeros c₃.nmem Lb m = zeros c.nmem Lb m := by rw [dm, am]
      refine ⟨c₄, k₃ + k₄, .seq e₃ e₄, ?_, ?_, ?_, hL₄, fun a ha => ?_, fun r hr => ?_, ?_, ?_,
        ?_⟩
      · rw [hz₃] at hk₄; omega
      · rw [hR₄ _ (by omega) (by omega) (by omega), dR _ (by omega) (by omega) (by omega),
          aR _ (by omega) (by omega), r00]
      · rw [hR₄ _ (by omega) (by omega) (by omega), dR _ (by omega) (by omega) (by omega), h1]
      · rw [hM₄ a ha, dm, am]
      · rw [hR₄ _ (by omega) (by omega) (by omega), dR _ (by omega) (by omega) (by omega),
          aR _ (by omega) (by omega)]
      · rw [hrr₄, dr, ar]
      · rw [hrm₄, drm, arm]
      · rw [ho₄, do', ao]
    · -- `i` is labelled: no point has the label `i`
      have hlt : olab f i < i := by
        have := hL i hi
        unfold labV at this
        split_ifs at this with hh
        · exact hh
        · exact absurd this h0
      refine spec_ifLtN_false (by rw [a03, h1]; omega) ?_
      refine spec_skip e₁.wb_right ⟨by rw [am]; omega, by rw [aR _ (by omega) (by omega), r00],
        h1, fun x hx => ?_, fun a _ => by rw [am], fun r hr => aR r (by omega) (by omega), ar, arm,
        ao⟩
      rw [am, hL x hx]
      unfold labV
      have hne : olab f x ≠ i := fun e => by
        have := olab_olab hp hx
        rw [e] at this
        omega
      by_cases hx1 : olab f x < i
      · have : olab f x < i + 1 := by omega
        simp only [hx1, this, ↓reduceIte]
      · have : ¬ olab f x < i + 1 := by omega
        simp only [hx1, this, ↓reduceIte]
  -- `i := i + 1`
  obtain ⟨c₃, k₃, e₃, hk₃, f00, fR, fm, fr, frm, fo⟩ :=
    olInc_exec (P := P) c₂ e₂.wb_right b00 b01 (by omega)
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), ?_, f00, by rw [fR _ (by omega), b01],
    fun x hx => by rw [fm]; exact bL x hx,
    fun a ha => by rw [fm]; exact bM a ha, fun r hr => by rw [fR r (by omega), bR r hr],
    by rw [fr, brr], by rw [frm, brm], by rw [fo, bo]⟩
  rw [fm]; omega

/-- **The orbit labelling** (see the module docstring): from `LAB` all zero, `olProg` writes
`LAB[x] = olab f x + 1` for every `x < m` within `20 m + 4` steps. -/
theorem olProg_exec (hp : PermOn f m) {Pb Lb : ℕ} (hPL : Pb + m ≤ Lb) (hW : Lb + m ≤ W)
    (hW1 : 1 ≤ W) (c : Config) (hc : WordsBounded W c) (r50 : c.nreg 7350 = Pb) (r51 : c.nreg 7351 = Lb)
    (r52 : c.nreg 7352 = m) (hf : ∀ x < m, c.nmem (Pb + x) = f x)
    (hz : ∀ x < m, c.nmem (Lb + x) = 0) :
    ∃ c' k, Exec P W olProg c c' k ∧ k ≤ 20 * m + 4 ∧
      (∀ x < m, c'.nmem (Lb + x) = olab f x + 1) ∧
      (∀ a, (a < Lb ∨ Lb + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 7400 ∨ 7405 < r) → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a00, a01, aR, am, ar, arm, ao⟩ := olInit_exec (P := P) c hc hW1
  let I : Config → Prop := fun d => WordsBounded W d ∧ d.nreg 7401 = 1 ∧ d.nreg 7400 ≤ m ∧
    (∀ x < m, d.nmem (Lb + x) = labV f (d.nreg 7400) x) ∧
    (∀ a, (a < Lb ∨ Lb + m ≤ a) → d.nmem a = c.nmem a) ∧
    (∀ r, (r < 7400 ∨ 7405 < r) → d.nreg r = c.nreg r) ∧ d.rreg = c.rreg ∧ d.rmem = c.rmem ∧
    d.output = c.output
  have hI₁ : I c₁ := by
    refine ⟨e₁.wb_right, a01, by omega, fun x hx => ?_, fun a _ => by rw [am],
      fun r hr => aR r (by omega) (by omega), ar, arm, ao⟩
    rw [am, hz x hx, a00]
    unfold labV
    simp only [Nat.not_lt_zero, ↓reduceIte]
  obtain ⟨c', k, ex, ⟨hw, h01, hle, hL, hM, hR, hrr, hrm, ho⟩, hstop, hk⟩ :=
    whileLtN_potL (P := P) (W := W) (a := 7400) (b := 7352) (body := olBody) I
    (fun d => 12 * (m - d.nreg 7400) + 8 * zeros d.nmem Lb m) (fun d h => h.1)
    (fun d ⟨hw, h01, hle, hL, hM, hR, hrr, hrm, ho⟩ hlt => by
      have h52 : d.nreg 7352 = m := by rw [hR _ (by omega), r52]
      rw [h52] at hlt
      obtain ⟨d', k, ex, hk, e00, e01, hL', hM', hR', hrr', hrm', ho'⟩ :=
        olBody_exec (P := P) hp hlt hPL hW d hw (by rw [hR _ (by omega), r50])
          (by rw [hR _ (by omega), r51]) rfl h01
          (fun x hx => by rw [hM _ (Or.inl (by omega)), hf x hx]) hL
      refine ⟨d', k, ex, ⟨ex.wb_right, e01, by omega,
        by rw [e00]; exact hL', fun a ha => by rw [hM' a ha, hM a ha],
        fun r hr => by rw [hR' r hr, hR r hr], by rw [hrr', hrr], by rw [hrm', hrm],
        by rw [ho', ho]⟩, ?_⟩
      beta_reduce
      rw [e00]
      omega)
    hI₁
  have h52 : c'.nreg 7352 = m := by rw [hR _ (by omega), r52]
  have hm : c'.nreg 7400 = m := by rw [h52] at hstop; omega
  have hz₁ : zeros c₁.nmem Lb m = m := zeros_all fun x hx => by rw [am]; exact hz x hx
  refine ⟨c', k₁ + k, .seq e₁ ex, ?_, fun x hx => ?_, hM, hR, hrr, hrm, ho⟩
  · rw [a00, hz₁] at hk; omega
  · rw [hL x hx, hm]
    unfold labV
    simp only [olab_lt hp hx, ↓reduceIte]

end OrbLab

end BKMNW

end PlanarFlow
