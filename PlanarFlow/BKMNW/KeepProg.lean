module

public import PlanarFlow.BKMNW.ChoiceProg

/-!
# The prune update of `scertD` on the machine: the kept component and the pruned indices

At a prune level of `scertD` (`scStep`) the darts `N` are replaced by the heavy component
`K = comp N g (e z)` and the record keeps the pruned darts `N \ K` (the input `hSN` of
`prProg_pruneI`). With the labels of the components off `g` (`LAB[i] = LAB[j] ↔ e j ∈ comp N g
(e i)` for `e i ∈ N`) one branch-free scan writes the new flags `NF2[i] = [NF[i] ≠ 0 ∧ LAB[i] = LZ]`
(`LZ = LAB[z]`) and appends every `i` with `NF[i] ≠ 0 ∧ LAB[i] ≠ LZ` to `IX` (the write at the
current end is unconditional, the count grows by the test).

* `kpK`, `kpP` (the two tests), `kpC` (the count), `kpL` (the appended indices), `kpBody`
  (17 instrs), **`kpScan`** (registers `4820 = n`, `4821 = NFb`, `4822 = LABb`, `4823 = LZ`,
  `4824 = NF2b`, `4825 = IXb`; written `4826 … 4832`, the count in `4828`), `kpBody_exec`,
  **`kpScan_exec`** (`19 n + 5` steps);
* **`kpScan_comp`**: `kpK … ≠ 0 ↔ e i ∈ comp M N Hs g (e z)`, the appended indices are `< n`
  and `(kpL …).toFinset.image e = N \ comp M N Hs g (e z)` (the input `hSN` of
  `prProg_pruneI`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Relation WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The tests and the appended list -/

/-- The kept test `[nf ≠ 0 ∧ l = LZ]`. -/
def kpK (nf l LZ : ℕ) : ℕ := (1 - (l - LZ + (LZ - l)) / (l - LZ + (LZ - l))) * (nf / nf)

/-- The pruned test `[nf ≠ 0 ∧ l ≠ LZ]`. -/
def kpP (nf l LZ : ℕ) : ℕ := (l - LZ + (LZ - l)) / (l - LZ + (LZ - l)) * (nf / nf)

lemma kpK_eq (nf l LZ : ℕ) : kpK nf l LZ = if nf ≠ 0 ∧ l = LZ then 1 else 0 := by
  unfold kpK; rw [ne_sgn, sgn_eq]; split_ifs <;> omega

lemma kpP_eq (nf l LZ : ℕ) : kpP nf l LZ = if nf ≠ 0 ∧ l ≠ LZ then 1 else 0 := by
  unfold kpP; rw [ne_sgn, sgn_eq]; split_ifs <;> omega

lemma kpP_le (nf l LZ : ℕ) : kpP nf l LZ ≤ 1 := by rw [kpP_eq]; split_ifs <;> omega

/-- The count of the indices `< i` with test `1`. -/
def kpC (p : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => kpC p i + p i

/-- The indices `< i` with test `1`, in order. -/
def kpL (p : ℕ → ℕ) (i : ℕ) : List ℕ := (List.range i).filter fun j => p j = 1

lemma kpL_succ (p : ℕ → ℕ) (i : ℕ) :
    kpL p (i + 1) = kpL p i ++ if p i = 1 then [i] else [] := by
  unfold kpL
  rw [List.range_succ, List.filter_append]
  congr 1
  simp only [List.filter_cons, List.filter_nil]
  split_ifs <;> simp_all

lemma kpC_eq {p : ℕ → ℕ} (hp : ∀ i, p i ≤ 1) (i : ℕ) : kpC p i = (kpL p i).length := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [kpC, kpL_succ, List.length_append, ih]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hp i) with h | h <;> simp [h]

lemma kpC_le {p : ℕ → ℕ} (hp : ∀ i, p i ≤ 1) (i : ℕ) : kpC p i ≤ i := by
  rw [kpC_eq hp]; exact (List.length_filter_le _ _).trans (by simp)

/-! ### The program -/

/-- One index (`4826 = 1`, `4827 = i`, `4828 = cnt`, scratch `4829 … 4832`). -/
def kpBody : Stmt :=
  block [.addN 4829 4821 4827, .loadN 4829 4829, .divN 4829 4829 4829,
    .addN 4830 4822 4827, .loadN 4830 4830,
    .subN 4831 4830 4823, .subN 4832 4823 4830, .addN 4831 4831 4832, .divN 4831 4831 4831,
    .subN 4832 4826 4831, .mulN 4832 4832 4829,
    .addN 4830 4824 4827, .storeN 4830 4832,
    .mulN 4831 4831 4829,
    .addN 4830 4825 4828, .storeN 4830 4827,
    .addN 4828 4828 4831, .addN 4827 4827 4826]

/-- **The prune update.** -/
def kpScan : Stmt :=
  .seq (block [.constN 4826 1, .constN 4827 0, .constN 4828 0]) (.whileLtN 4827 4820 kpBody)

section Exec

variable {P : Input} {W : ℕ}

theorem kpBody_exec (c : Config) (hc : WordsBounded W c) {NFb LABb LZ NF2b IXb i cnt nf l : ℕ}
    (r1 : c.nreg 4821 = NFb) (r2 : c.nreg 4822 = LABb) (r3 : c.nreg 4823 = LZ)
    (r4 : c.nreg 4824 = NF2b) (r5 : c.nreg 4825 = IXb) (r6 : c.nreg 4826 = 1)
    (r7 : c.nreg 4827 = i) (r8 : c.nreg 4828 = cnt) (hnf : c.nmem (NFb + i) = nf)
    (hl : c.nmem (LABb + i) = l) (hcnt : cnt ≤ i)
    (w1 : NFb + i ≤ W) (w2 : LABb + i ≤ W) (w3 : l + LZ ≤ W) (w4 : NF2b + i ≤ W)
    (w5 : IXb + cnt ≤ W) (w6 : i + 1 ≤ W) :
    ∃ c' t, Exec P W kpBody c c' t ∧ t = 18 ∧ c'.nreg 4827 = i + 1 ∧
      c'.nreg 4828 = cnt + kpP nf l LZ ∧
      c'.nmem = upd (upd c.nmem (NF2b + i) (kpK nf l LZ)) (IXb + cnt) i ∧
      (∀ x, (x < 4827 ∨ 4832 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hk : (1 - (l - LZ + (LZ - l)) / (l - LZ + (LZ - l))) * (nf / nf) = kpK nf l LZ := rfl
  have hp : (l - LZ + (LZ - l)) / (l - LZ + (LZ - l)) * (nf / nf) = kpP nf l LZ := rfl
  have hp1 := kpP_le nf l LZ
  have hk1 : kpK nf l LZ ≤ 1 := by rw [kpK_eq]; split_ifs <;> omega
  unfold kpBody
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r3, r4, r5, r6, r7, r8, hnf, hl, hk, hp]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r6, r7]
  · config_simp; simp only [r1, r2, r3, r4, r5, r6, r7, r8, hnf, hl, hk, hp]
  · config_simp; simp only [r1, r2, r3, r4, r5, r6, r7, r8, hnf, hl, hk, hp]
  · obtain ⟨a1, a2, a3, a4, a5, a6⟩ : x ≠ 4827 ∧ x ≠ 4828 ∧ x ≠ 4829 ∧ x ≠ 4830 ∧
        x ≠ 4831 ∧ x ≠ 4832 := by omega
    simp only [Config.nreg_mk, upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3,
      upd_other _ _ _ a4, upd_other _ _ _ a5, upd_other _ _ _ a6]

/-- **The prune update on the machine**: with the flags `NF`, the labels `LAB` (`LAB[i] + LZ ≤
W`) below `NF2` (`n` words) and `IX` (`n + 1` words), within `20 n + 5` steps
`NF2[i] = kpK NF[i] LAB[i] LZ` and `IX[k] = (kpL p n)[k]`, the count `r4828 = |kpL p n|`
(`p i = kpP NF[i] LAB[i] LZ`); memory outside `NF2` and `IX`, registers outside `4826 … 4832`,
reals and output kept. -/
theorem kpScan_exec (c : Config) (hc : WordsBounded W c) {n NFb LABb LZ NF2b IXb : ℕ}
    (r0 : c.nreg 4820 = n) (r1 : c.nreg 4821 = NFb) (r2 : c.nreg 4822 = LABb)
    (r3 : c.nreg 4823 = LZ) (r4 : c.nreg 4824 = NF2b) (r5 : c.nreg 4825 = IXb)
    (lay : NFb + n ≤ NF2b ∧ LABb + n ≤ NF2b ∧ NF2b + n ≤ IXb ∧ IXb + n + 1 ≤ W)
    (hlab : ∀ j < n, c.nmem (LABb + j) + LZ ≤ W) :
    ∃ c' t, Exec P W kpScan c c' t ∧ t ≤ 20 * n + 5 ∧
      c'.nreg 4828 = (kpL (fun j => kpP (c.nmem (NFb + j)) (c.nmem (LABb + j)) LZ) n).length ∧
      (∀ i < n, c'.nmem (NF2b + i) = kpK (c.nmem (NFb + i)) (c.nmem (LABb + i)) LZ) ∧
      (∀ k (hk : k < (kpL (fun j => kpP (c.nmem (NFb + j)) (c.nmem (LABb + j)) LZ) n).length),
        c'.nmem (IXb + k) = (kpL (fun j => kpP (c.nmem (NFb + j)) (c.nmem (LABb + j)) LZ) n)[k]) ∧
      (∀ a, (a < NF2b ∨ IXb + n + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4826 ∨ 4832 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4⟩ := lay
  unfold kpScan
  obtain ⟨c₁, k₁, e₁, hk₁, g6, g7, g8, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 4826 1, .constN 4827 0, .constN 4828 0]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 4826 = 1 ∧ c₁.nreg 4827 = 0 ∧ c₁.nreg 4828 = 0 ∧
      (∀ x, (x < 4826 ∨ 4828 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; done)
    obtain ⟨a1, a2, a3⟩ : x ≠ 4826 ∧ x ≠ 4827 ∧ x ≠ 4828 := by omega
    simp only [Config.nreg_mk, upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3]
  have hw₁ := e₁.wb_right
  have q : ∀ x, (x < 4826 ∨ 4828 < x) → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  set pp : ℕ → ℕ := fun j => kpP (m₀ (NFb + j)) (m₀ (LABb + j)) LZ with hpp
  have hp : ∀ i, pp i ≤ 1 := fun i => kpP_le _ _ _
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 4827 ∨ 4832 < x) → c'.nreg x = c₁.nreg x) ∧
    c'.nreg 4828 = (kpL pp i).length ∧
    (∀ j < i, c'.nmem (NF2b + j) = kpK (m₀ (NFb + j)) (m₀ (LABb + j)) LZ) ∧
    (∀ k (hk : k < (kpL pp i).length), c'.nmem (IXb + k) = (kpL pp i)[k]) ∧
    (∀ a, ¬ (NF2b ≤ a ∧ a < NF2b + i) → ¬ (IXb ≤ a ∧ a < IXb + i) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h27, j1, j2, j3, j4, j5, j6, j7, j8⟩ := tgRange (P := P)
    (a := 4827) (b := 4820) (body := kpBody) J (B := 18) c₁ hw₁ g7
    (by rw [q _ (by omega), r0]) (Nat.zero_le n)
    ⟨fun _ _ => rfl, by rw [g8]; rfl, fun j hj => absurd hj (by omega),
      fun k hk => absurd hk (by simp [kpL]), fun a _ _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h27 h20 ⟨j1, j2, j3, j4, j5, j6, j7, j8⟩ => by
      have f : ∀ x, (x < 4827 ∨ 4832 < x) → c'.nreg x = c₁.nreg x := j1
      have hlen : (kpL pp i).length ≤ i := by rw [← kpC_eq hp]; exact kpC_le hp i
      have e1 : c'.nmem (NFb + i) = m₀ (NFb + i) := j5 _ (by omega) (by omega)
      have e2 : c'.nmem (LABb + i) = m₀ (LABb + i) := j5 _ (by omega) (by omega)
      obtain ⟨c'', t, ex, ht, h27', h28', hm', hn', hr', hrm', ho'⟩ :=
        kpBody_exec (P := P) c' hw (by rw [f _ (by omega), q _ (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega), r2]) (by rw [f _ (by omega), q _ (by omega), r3])
        (by rw [f _ (by omega), q _ (by omega), r4]) (by rw [f _ (by omega), q _ (by omega), r5])
        (by rw [f _ (by omega), g6]) h27 j2 e1 e2 hlen (by omega) (by omega) (hlab i hhi)
        (by omega) (by omega) (by omega)
      have hL := kpL_succ pp i
      refine ⟨c'', t, ex, ht.le, h27', by rw [hn' _ (by omega)]; exact h20,
        fun x hx => by rw [hn' x hx, f x hx], ?_, fun j hj => ?_, fun k hk => ?_,
        fun a ha hb => ?_, by rw [hr', j6], by rw [hrm', j7], by rw [ho', j8]⟩
      · rw [h28', hL, List.length_append]
        show (kpL pp i).length + pp i = _
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hp i) with h | h <;> simp [h]
      · rw [hm']
        rw [upd_other _ _ _ (by omega)]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j3 j hj
        · rw [upd_same]
      · rw [hm']
        simp only [hL] at hk ⊢
        by_cases hkl : k < (kpL pp i).length
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), j4 k hkl,
            List.getElem_append_left hkl]
        · have hpi : pp i = 1 := by
            by_contra h0
            have : pp i = 0 := by have := hp i; omega
            simp [this] at hk; omega
          have hk' : k = (kpL pp i).length := by simp [hpi] at hk; omega
          subst hk'
          rw [upd_same, List.getElem_append_right (le_refl _)]
          simp [hpi]
      · rw [hm', upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
        exact j5 a (by omega) (by omega))
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3, j4, fun a ha => j5 a (by omega) (by omega),
    fun x hx => by rw [j1 x (by omega), q x (by omega)], by rw [j6, gr₁], by rw [j7, grm₁],
    by rw [j8, go₁]⟩

end Exec

/-! ### The kept component and the pruned darts -/

section Sem

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

lemma image_getElem_range (L : List ℕ) :
    ((range L.length).attach.image fun k => L[k.1]'(mem_range.1 k.2)) = L.toFinset := by
  ext x
  simp only [mem_image, mem_attach, true_and, List.mem_toFinset, Subtype.exists, mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact List.getElem_mem hk
  · intro hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    exact ⟨k, hk, rfl⟩

/-- **The prune update computes the kept component and the pruned darts**: for labels exact on
the components off `g` (for darts of `N`), flags `nf i ≠ 0 ↔ e i ∈ N` and the heavy index `z`
(`e z ∈ N`), the kept flag `kpK (nf i) (lab i) (lab z)` marks `comp M N Hs g (e z)` and the
appended indices `kpL` are those of `N \ comp M N Hs g (e z)`. -/
theorem kpScan_comp {e : ℕ → D} {n : ℕ} {Hs : List (Finset V)} {N : Finset D} {g : Finset V}
    (hsurjN : ∀ d ∈ N, ∃ i < n, e i = d) {lab nf : ℕ → ℕ} {z : ℕ} (hz : z < n) (hzN : e z ∈ N)
    (hlab : ∀ i < n, ∀ j < n, e i ∈ N → (lab i = lab j ↔ e j ∈ comp M N Hs g (e i)))
    (hnf : ∀ i < n, (nf i ≠ 0 ↔ e i ∈ N)) :
    (∀ i < n, (kpK (nf i) (lab i) (lab z) ≠ 0 ↔ e i ∈ comp M N Hs g (e z))) ∧
    (∀ k (hk : k < (kpL (fun j => kpP (nf j) (lab j) (lab z)) n).length),
      (kpL (fun j => kpP (nf j) (lab j) (lab z)) n)[k] < n) ∧
    ((kpL (fun j => kpP (nf j) (lab j) (lab z)) n).toFinset.image e =
      N \ comp M N Hs g (e z)) := by
  refine ⟨fun i hi => ?_, fun k hk => ?_, ?_⟩
  · rw [kpK_eq]
    have e1 := hlab z hz i hi hzN
    have e2 := hnf i hi
    split_ifs with h
    · exact ⟨fun _ => e1.1 h.2.symm, fun _ => one_ne_zero⟩
    · refine ⟨fun h' => absurd rfl h', fun h' => absurd ⟨e2.2 (mem_comp.1 h').1,
        (e1.2 h').symm⟩ h⟩
  · have := List.getElem_mem hk
    unfold kpL at this
    exact List.mem_range.1 (List.mem_filter.1 this).1
  · ext d
    simp only [mem_image, List.mem_toFinset, kpL, List.mem_filter, List.mem_range,
      decide_eq_true_eq, mem_sdiff]
    constructor
    · rintro ⟨i, ⟨hi, hp⟩, rfl⟩
      rw [kpP_eq] at hp
      split_ifs at hp with h
      · have hN := (hnf i hi).1 h.1
        exact ⟨hN, fun hc => h.2 ((hlab z hz i hi hzN).2 hc).symm⟩
    · rintro ⟨hN, hnc⟩
      obtain ⟨i, hi, rfl⟩ := hsurjN _ hN
      refine ⟨i, ⟨hi, ?_⟩, rfl⟩
      have hc : nf i ≠ 0 ∧ lab i ≠ lab z :=
        ⟨(hnf i hi).2 hN, fun h => hnc ((hlab z hz i hi hzN).1 h.symm)⟩
      rw [kpP_eq]; simp only [hc, ne_eq, not_false_eq_true, and_self, ↓reduceIte]

end Sem

end BKMNW

end PlanarFlow
