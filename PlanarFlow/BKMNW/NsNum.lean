module

public import PlanarFlow.BKMNW.NsTab
public import Mathlib.Data.List.GetD

/-!
# The canonical numbering of the closure on the machine

From the keep flags `KEEP` (`0`/`1`) and the reverses `RV` of `m` darts, two linear loops write
the list `fL = cL ++ rL` of the closure (`cL` the kept indices in increasing order, `rL` the
reverses not kept of the kept indices, in the order of these) into `CD` and the inverse map
`POS[j] = position + 1` (`0` off the list), **`LRep`**. Branchless bodies: `CD[h] := x` always
(the cell after the list is scratch, hence `CD` has `m + 1` cells), `POS[x] := POS[x] + (h+1)·f`,
`h := h + f`.

* `cLG`, `rLG` (the lists), `LRep`, **`LRep.append`**, `LRep.keep`;
* `nm1`/`nmL1` (the kept indices) with **`nmL1_exec`** (`12 m + 5`), `nm2`/`nmL2` (the reverses)
  with **`nmL2_exec`** (`19 m' + 3`), **`nmProg_exec`**: `nmL1 ; m' := h ; nmL2`.

Registers: `7500 = m`, `7501 = RVb`, `7514 = KPb`, `7516 = POb`, `7517 = CDb`; written `7522 = 1`,
`7526 = h`, `7527 = m'`, `7530`, scratch `7531 … 7539`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace NsStep

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The lists -/

/-- The kept indices below `i`. -/
def cLG (kp : ℕ → ℕ) (i : ℕ) : List ℕ := (List.range i).filter fun j => decide (kp j = 1)

/-- The reverses not kept of the first `t` elements of `L`. -/
def rLG (kp rv : ℕ → ℕ) (L : List ℕ) (t : ℕ) : List ℕ :=
  ((L.take t).filter fun x => decide (kp (rv x) = 0)).map rv

/-- **The list `L` in `CD` with its inverse in `POS`.** -/
def LRep (L : List ℕ) (mem : ℕ → ℕ) (CDb POb m : ℕ) : Prop :=
  (∀ t < L.length, mem (CDb + t) = L.getD t 0) ∧
    ∀ j < m, mem (POb + j) = if j ∈ L then L.idxOf j + 1 else 0

lemma length_le_of_nodup {L : List ℕ} {m : ℕ} (hn : L.Nodup) (hl : ∀ x ∈ L, x < m) :
    L.length ≤ m := by
  rw [← List.toFinset_card_of_nodup hn]
  calc L.toFinset.card ≤ (range m).card :=
        card_le_card fun x hx => mem_range.2 (hl x (List.mem_toFinset.1 hx))
    _ = m := card_range m

/-- **Appending one element.** -/
lemma LRep.append {L : List ℕ} {mem : ℕ → ℕ} {CDb POb m v : ℕ} (h : LRep L mem CDb POb m)
    (hv : v < m) (hn : v ∉ L) (hd : POb + m ≤ CDb) :
    LRep (L ++ [v]) (upd (upd mem (CDb + L.length) v) (POb + v) (L.length + 1)) CDb POb m := by
  refine ⟨fun t ht => ?_, fun j hj => ?_⟩
  · rw [upd_other _ _ _ (by omega)]
    rw [List.length_append, List.length_singleton] at ht
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · rw [upd_other _ _ _ (by omega), h.1 t ht, List.getD_append _ _ _ _ ht]
    · rw [upd_same, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]; rfl
  · by_cases e : j = v
    · subst e
      rw [upd_same, iteT (List.mem_append_right _ (List.mem_singleton_self _)),
        List.idxOf_append_of_notMem hn]
      simp
    · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), h.2 j hj]
      have : j ∈ L ++ [v] ↔ j ∈ L := by simp [e]
      by_cases hj' : j ∈ L
      · rw [iteT hj', iteT (this.2 hj'), List.idxOf_append_of_mem hj']
      · rw [iteF hj', iteF (fun h' => hj' (this.1 h'))]

/-- Writing after the list, or the value already there. -/
lemma LRep.keep {L : List ℕ} {mem : ℕ → ℕ} {CDb POb m v w : ℕ} (h : LRep L mem CDb POb m)
    (hv : v < m) (hw : mem (POb + v) = w) (hd : POb + m ≤ CDb) :
    LRep L (upd (upd mem (CDb + L.length) v) (POb + v) w) CDb POb m := by
  refine ⟨fun t ht => ?_, fun j hj => ?_⟩
  · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), h.1 t ht]
  · by_cases e : j = v
    · subst e; rw [upd_same, ← hw, h.2 j hj]
    · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), h.2 j hj]

lemma cLG_succ (kp : ℕ → ℕ) (i : ℕ) :
    cLG kp (i + 1) = if kp i = 1 then cLG kp i ++ [i] else cLG kp i := by
  unfold cLG
  rw [List.range_succ, List.filter_append]
  by_cases h : kp i = 1 <;> simp [h]

lemma lt_of_mem_cLG {kp : ℕ → ℕ} {i x : ℕ} (h : x ∈ cLG kp i) : x < i := by
  unfold cLG at h; rw [List.mem_filter, List.mem_range] at h; exact h.1

lemma mem_cLG {kp : ℕ → ℕ} {i x : ℕ} : x ∈ cLG kp i ↔ x < i ∧ kp x = 1 := by
  unfold cLG; simp

lemma cLG_nodup (kp : ℕ → ℕ) (i : ℕ) : (cLG kp i).Nodup := List.nodup_range.filter _

lemma length_cLG_le (kp : ℕ → ℕ) (i : ℕ) : (cLG kp i).length ≤ i :=
  length_le_of_nodup (cLG_nodup kp i) fun _ hx => lt_of_mem_cLG hx

lemma rLG_succ (kp rv : ℕ → ℕ) (L : List ℕ) {t : ℕ} (ht : t < L.length) :
    rLG kp rv L (t + 1) = if kp (rv (L.getD t 0)) = 0 then rLG kp rv L t ++ [rv (L.getD t 0)]
      else rLG kp rv L t := by
  unfold rLG
  rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some, List.filter_append,
    List.getD_eq_getElem _ _ ht]
  by_cases h : kp (rv L[t]) = 0 <;> simp [h]

/-- The kept list with the reverses: its elements are below `m` and distinct. -/
lemma fLG_nodup {kp rv : ℕ → ℕ} {m t : ℕ} (hrv : ∀ j < m, rv j < m)
    (hrr : ∀ j < m, rv (rv j) = j) :
    (cLG kp m ++ rLG kp rv (cLG kp m) t).Nodup := by
  rw [List.nodup_append]
  refine ⟨cLG_nodup kp m, ?_, fun a ha b hb e => ?_⟩
  · unfold rLG
    refine List.Nodup.map_on (fun x hx y hy e => ?_) (((cLG_nodup kp m).sublist
      (List.take_sublist _ _)).filter _)
    have hx' := lt_of_mem_cLG (List.mem_of_mem_take (List.mem_of_mem_filter hx))
    have hy' := lt_of_mem_cLG (List.mem_of_mem_take (List.mem_of_mem_filter hy))
    rw [← hrr x hx', e, hrr y hy']
  · unfold rLG at hb
    rw [List.mem_map] at hb
    obtain ⟨y, hy, rfl⟩ := hb
    rw [List.mem_filter] at hy
    have h1 := (mem_cLG.1 ha).2
    subst e
    have := of_decide_eq_true hy.2
    omega

lemma lt_of_mem_fLG {kp rv : ℕ → ℕ} {m t x : ℕ} (hrv : ∀ j < m, rv j < m)
    (h : x ∈ cLG kp m ++ rLG kp rv (cLG kp m) t) : x < m := by
  rcases List.mem_append.1 h with h | h
  · exact lt_of_mem_cLG h
  · unfold rLG at h
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
    exact hrv y (lt_of_mem_cLG (List.mem_of_mem_take (List.mem_of_mem_filter hy)))

/-! ### The kept indices -/

/-- One index of the first loop. -/
def nm1 : Stmt := block [
  .addN 7531 7514 7530, .loadN 7532 7531,
  .addN 7533 7517 7526, .storeN 7533 7530,
  .addN 7534 7526 7522, .mulN 7534 7534 7532,
  .addN 7535 7516 7530, .storeN 7535 7534,
  .addN 7526 7526 7532,
  .addN 7530 7530 7522]

/-- The first loop. -/
def nmL1 : Stmt :=
  .seq (block [.constN 7522 1, .constN 7526 0, .constN 7530 0]) (.whileLtN 7530 7500 nm1)

/-- One index of the second loop. -/
def nm2 : Stmt := block [
  .addN 7531 7517 7530, .loadN 7532 7531,
  .addN 7531 7501 7532, .loadN 7533 7531,
  .addN 7531 7514 7533, .loadN 7534 7531,
  .subN 7535 7522 7534,
  .addN 7536 7517 7526, .storeN 7536 7533,
  .addN 7537 7516 7533, .loadN 7538 7537,
  .addN 7539 7526 7522, .mulN 7539 7539 7535, .addN 7538 7538 7539, .storeN 7537 7538,
  .addN 7526 7526 7535,
  .addN 7530 7530 7522]

/-- The second loop. -/
def nmL2 : Stmt := .seq (block [.constN 7530 0]) (.whileLtN 7530 7527 nm2)

/-- **The numbering**: the kept indices, `m' := h`, the reverses. -/
def nmProg : Stmt := .seq nmL1 (.seq (block [.copyN 7527 7526]) nmL2)

variable {P : Input} {W : ℕ}

theorem nm1_exec (c : Config) (hc : WordsBounded W c) {KPb POb CDb i h f : ℕ}
    (r14 : c.nreg 7514 = KPb) (r16 : c.nreg 7516 = POb) (r17 : c.nreg 7517 = CDb)
    (r22 : c.nreg 7522 = 1) (r26 : c.nreg 7526 = h) (r30 : c.nreg 7530 = i)
    (hf : c.nmem (KPb + i) = f) (hf1 : f ≤ 1)
    (w1 : KPb + i ≤ W) (w2 : CDb + h ≤ W) (w3 : POb + i ≤ W) (w4 : h + 1 ≤ W) (w5 : i + 1 ≤ W) :
    ∃ c' k, Exec P W nm1 c c' k ∧ k = 10 ∧ c'.nreg 7530 = i + 1 ∧ c'.nreg 7526 = h + f ∧
      c'.nmem = upd (upd c.nmem (CDb + h) i) (POb + i) ((h + 1) * f) ∧
      (∀ x, (x < 7526 ∨ (7526 < x ∧ x < 7530) ∨ 7539 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hm : (h + 1) * f ≤ h + 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hf1 with rfl | rfl <;> simp
  unfold nm1
  exec_block
  all_goals try (config_simp; simp only [r14, r16, r17, r22, r26, r30, hf]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r22, r30]
  · config_simp; simp only [r22, r26, r30, r14, hf]
  · config_simp; simp only [r14, r16, r17, r22, r26, r30, hf]
  · config_simp; simp (disch := omega) only [Machine.upd_other]

theorem nm2_exec (c : Config) (hc : WordsBounded W c) {RVb KPb POb CDb t h x r kr po : ℕ}
    (r01 : c.nreg 7501 = RVb) (r14 : c.nreg 7514 = KPb) (r16 : c.nreg 7516 = POb)
    (r17 : c.nreg 7517 = CDb) (r22 : c.nreg 7522 = 1) (r26 : c.nreg 7526 = h)
    (r30 : c.nreg 7530 = t)
    (hx : c.nmem (CDb + t) = x) (hr : c.nmem (RVb + x) = r) (hk : c.nmem (KPb + r) = kr)
    (hpo : c.nmem (POb + r) = po) (hne : CDb + h ≠ POb + r)
    (w1 : CDb + t ≤ W) (w2 : RVb + x ≤ W) (w3 : KPb + r ≤ W) (w4 : CDb + h ≤ W)
    (w5 : POb + r ≤ W) (w6 : po + (h + 1) * (1 - kr) ≤ W) (w7 : h + 1 ≤ W) (w8 : t + 1 ≤ W) :
    ∃ c' k, Exec P W nm2 c c' k ∧ k = 17 ∧ c'.nreg 7530 = t + 1 ∧
      c'.nreg 7526 = h + (1 - kr) ∧
      c'.nmem = upd (upd c.nmem (CDb + h) r) (POb + r) (po + (h + 1) * (1 - kr)) ∧
      (∀ x, (x < 7526 ∨ (7526 < x ∧ x < 7530) ∨ 7539 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hm : (h + 1) * (1 - kr) ≤ h + 1 := by
    rcases Nat.eq_zero_or_pos (1 - kr) with e | e
    · rw [e]; simp
    · have : 1 - kr = 1 := by omega
      rw [this]; simp
  have hpo2 : upd c.nmem (CDb + h) r (POb + r) = po := by rw [upd_other _ _ _ (Ne.symm hne), hpo]
  unfold nm2
  exec_block
  all_goals try (config_simp; simp only [r01, r14, r16, r17, r22, r26, r30, hx, hr, hk, hpo, hpo2]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r22, r30]
  · config_simp; simp only [r01, r14, r22, r26, r17, r30, hx, hr, hk]
  · config_simp; simp only [r01, r14, r16, r17, r22, r26, r30, hx, hr, hk, hpo, hpo2]
  · config_simp; simp (disch := omega) only [Machine.upd_other]

/-- **The kept indices**: from `POS` zero, within `12 m + 5` steps `LRep (cLG kp m)` and
`r7526` its length. -/
theorem nmL1_exec (c : Config) (hc : WordsBounded W c) {m KPb POb CDb : ℕ} {kp : ℕ → ℕ}
    (r00 : c.nreg 7500 = m) (r14 : c.nreg 7514 = KPb) (r16 : c.nreg 7516 = POb)
    (r17 : c.nreg 7517 = CDb)
    (hkp : ∀ j < m, c.nmem (KPb + j) = kp j) (hk1 : ∀ j < m, kp j ≤ 1)
    (hP0 : ∀ j < m, c.nmem (POb + j) = 0)
    (dKP : KPb + m ≤ POb) (dPC : POb + m ≤ CDb) (wC : CDb + m + 1 ≤ W) :
    ∃ c' k, Exec P W nmL1 c c' k ∧ k ≤ 12 * m + 5 ∧
      c'.nreg 7526 = (cLG kp m).length ∧ LRep (cLG kp m) c'.nmem CDb POb m ∧
      (∀ a, ¬ (POb ≤ a ∧ a < POb + m) → ¬ (CDb ≤ a ∧ a < CDb + m + 1) → c'.nmem a = c.nmem a) ∧
      c'.nreg 7522 = 1 ∧ c'.nreg 7525 = c.nreg 7525 ∧
      (∀ r, (r < 7522 ∨ 7539 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold nmL1
  obtain ⟨c₁, k₁, e₁, hk₁, g22, g26, g30, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 7522 1, .constN 7526 0, .constN 7530 0]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 7522 = 1 ∧ c₁.nreg 7526 = 0 ∧ c₁.nreg 7530 = 0 ∧
      (∀ x, x ≠ 7522 → x ≠ 7526 → x ≠ 7530 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    have : 1 ≤ W := by omega
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x a b d => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp
    · config_simp
    · config_simp; simp (disch := omega) only [Machine.upd_other]
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 7522 → x ≠ 7526 → x ≠ 7530 → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 7526 ∨ (7526 < x ∧ x < 7530) ∨ 7539 < x) → c'.nreg x = c₁.nreg x) ∧
    c'.nreg 7526 = (cLG kp i).length ∧ LRep (cLG kp i) c'.nmem CDb POb m ∧
    (∀ a, ¬ (POb ≤ a ∧ a < POb + m) → ¬ (CDb ≤ a ∧ a < CDb + m + 1) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h30, j1, j7, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 7530)
    (b := 7500) (body := nm1) J (B := 10) c₁ hw₁ g30
    (by rw [q _ (by omega) (by omega) (by omega), r00]) (Nat.zero_le m)
    ⟨fun _ _ => rfl, by rw [g26]; rfl,
      ⟨fun t ht => absurd ht (by simp [cLG]), fun j hj => by
        rw [gm₁, hP0 j hj]; simp [cLG]⟩, fun a _ _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h30 h00 ⟨j1, j7, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 7526 ∨ (7526 < x ∧ x < 7530) ∨ 7539 < x) → c'.nreg x = c₁.nreg x := j1
      have ek : c'.nmem (KPb + i) = kp i := by
        rw [j3 _ (by omega) (by omega)]; exact hkp i hhi
      have hlen := length_cLG_le kp i
      obtain ⟨c'', t, ex, ht, h30', h26', hm', hn', hr', hrm', ho'⟩ := nm1_exec (P := P) c' hw
        (by rw [f _ (by omega), q _ (by omega) (by omega) (by omega), r14])
        (by rw [f _ (by omega), q _ (by omega) (by omega) (by omega), r16])
        (by rw [f _ (by omega), q _ (by omega) (by omega) (by omega), r17])
        (by rw [f _ (by omega), g22]) j7 h30 ek (hk1 i hhi) (by omega) (by omega) (by omega)
        (by omega) (by omega)
      have hni : i ∉ cLG kp i := fun h => by have := lt_of_mem_cLG h; omega
      refine ⟨c'', t, ex, ht.le, h30', by rw [hn' _ (by omega)]; exact h00,
        fun x hx => by rw [hn' x hx, f x hx], ?_, ?_, fun a ha1 ha2 => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [h26', cLG_succ]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hk1 i hhi) with e | e
        · rw [e, iteF (by omega)]; rfl
        · rw [e, iteT rfl, List.length_append]; rfl
      · rw [hm', cLG_succ]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hk1 i hhi) with e | e
        · rw [e, iteF (by omega), Nat.mul_zero]
          refine j2.keep hhi ?_ dPC
          rw [j2.2 i hhi, iteF hni]
        · rw [e, iteT rfl, Nat.mul_one]
          exact j2.append hhi hni dPC
      · rw [hm', upd_other _ _ _ (fun h => ha1 ⟨by omega, by omega⟩),
          upd_other _ _ _ (fun h => ha2 ⟨by omega, by omega⟩)]
        exact j3 a ha1 ha2)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j7, j2, j3, by rw [j1 _ (by omega), g22],
    by rw [j1 _ (by omega), q _ (by omega) (by omega) (by omega)],
    fun x hx => ?_, by rw [j4, gr₁], by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x (by omega)]
  exact q x (by omega) (by omega) (by omega)

/-- **The reverses not kept**: from `LRep cL`, within `19 m' + 3` steps
`LRep (cL ++ rLG kp rv cL m')`, `m' = |cL|`. -/
theorem nmL2_exec (c : Config) (hc : WordsBounded W c) {m RVb KPb POb CDb : ℕ}
    {kp rv : ℕ → ℕ} (r01 : c.nreg 7501 = RVb) (r14 : c.nreg 7514 = KPb)
    (r16 : c.nreg 7516 = POb) (r17 : c.nreg 7517 = CDb) (r22 : c.nreg 7522 = 1)
    (r26 : c.nreg 7526 = (cLG kp m).length) (r27 : c.nreg 7527 = (cLG kp m).length)
    (hkp : ∀ j < m, c.nmem (KPb + j) = kp j) (hk1 : ∀ j < m, kp j ≤ 1)
    (hrv : ∀ j < m, c.nmem (RVb + j) = rv j) (hrvm : ∀ j < m, rv j < m)
    (hrr : ∀ j < m, rv (rv j) = j) (hL : LRep (cLG kp m) c.nmem CDb POb m)
    (dKP : KPb + m ≤ POb) (dPC : POb + m ≤ CDb) (dRV : CDb + m + 1 ≤ RVb) (wR : RVb + m ≤ W) :
    ∃ c' k, Exec P W nmL2 c c' k ∧ k ≤ 19 * (cLG kp m).length + 3 ∧
      c'.nreg 7526 = (cLG kp m ++ rLG kp rv (cLG kp m) (cLG kp m).length).length ∧
      LRep (cLG kp m ++ rLG kp rv (cLG kp m) (cLG kp m).length) c'.nmem CDb POb m ∧
      (∀ a, ¬ (POb ≤ a ∧ a < POb + m) → ¬ (CDb ≤ a ∧ a < CDb + m + 1) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 7526 ∨ (7526 < r ∧ r < 7530) ∨ 7539 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set cL := cLG kp m with hcL
  unfold nmL2
  obtain ⟨c₁, k₁, e₁, hk₁, g30, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 7530 0]) c c₁ k₁ ∧ k₁ = 1 ∧ c₁.nreg 7530 = 0 ∧
      (∀ x, x ≠ 7530 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp; simp (disch := omega) only [Machine.upd_other]
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 7530 → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  have hlenm : ∀ t, (cL ++ rLG kp rv cL t).length ≤ m := fun t =>
    length_le_of_nodup (fLG_nodup hrvm hrr) fun x hx => lt_of_mem_fLG hrvm hx
  let J : ℕ → Config → Prop := fun t c' =>
    (∀ x, (x < 7526 ∨ (7526 < x ∧ x < 7530) ∨ 7539 < x) → c'.nreg x = c₁.nreg x) ∧
    c'.nreg 7526 = (cL ++ rLG kp rv cL t).length ∧ LRep (cL ++ rLG kp rv cL t) c'.nmem CDb POb m ∧
    (∀ a, ¬ (POb ≤ a ∧ a < POb + m) → ¬ (CDb ≤ a ∧ a < CDb + m + 1) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  have hr0 : rLG kp rv cL 0 = [] := by simp [rLG]
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h30, j1, j7, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 7530)
    (b := 7527) (body := nm2) J (B := 17) c₁ hw₁ g30
    (by rw [q _ (by omega), r27]) (Nat.zero_le _)
    ⟨fun _ _ => rfl, by rw [q _ (by omega), r26, hr0, List.append_nil],
      by rw [hr0, List.append_nil, gm₁]; exact hL, fun a _ _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun t c' hlo hhi hw h30 h00 ⟨j1, j7, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 7526 ∨ (7526 < x ∧ x < 7530) ∨ 7539 < x) → c'.nreg x = c₁.nreg x := j1
      have hxm : cL.getD t 0 < m := by
        rw [List.getD_eq_getElem _ _ hhi]; exact lt_of_mem_cLG (List.getElem_mem hhi)
      have ex : c'.nmem (CDb + t) = cL.getD t 0 := by
        rw [j2.1 t (by rw [List.length_append]; omega), List.getD_append _ _ _ _ hhi]
      have hrm := hrvm _ hxm
      have er : c'.nmem (RVb + cL.getD t 0) = rv (cL.getD t 0) := by
        rw [j3 _ (by omega) (by omega)]; exact hrv _ hxm
      have ek : c'.nmem (KPb + rv (cL.getD t 0)) = kp (rv (cL.getD t 0)) := by
        rw [j3 _ (by omega) (by omega)]; exact hkp _ hrm
      have hlen := hlenm t
      have hpo := j2.2 _ hrm
      have hpo_le : c'.nmem (POb + rv (cL.getD t 0)) ≤ m := by
        rw [hpo]
        split_ifs with hm
        · have := List.idxOf_lt_length_iff.2 hm; omega
        · omega
      have hk := hk1 _ hrm
      have hcl : cL.length ≤ m := length_cLG_le kp m
      obtain ⟨c'', t', ex', ht', h30', h26', hm', hn', hr', hrm', ho'⟩ := nm2_exec (P := P) c' hw
        (by rw [f _ (by omega), q _ (by omega), r01])
        (by rw [f _ (by omega), q _ (by omega), r14])
        (by rw [f _ (by omega), q _ (by omega), r16])
        (by rw [f _ (by omega), q _ (by omega), r17])
        (by rw [f _ (by omega), q _ (by omega), r22]) j7 h30 ex er ek rfl (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (by have : (cL ++ rLG kp rv cL t).length * (1 - kp (rv (cL.getD t 0))) ≤
              (cL ++ rLG kp rv cL t).length * 1 := Nat.mul_le_mul_left _ (by omega)
            rw [Nat.add_mul, one_mul]; omega) (by omega) (by omega)
      refine ⟨c'', t', ex', ht'.le, h30', by rw [hn' _ (by omega)]; exact h00,
        fun x hx => by rw [hn' x hx, f x hx], ?_, ?_, fun a ha1 ha2 => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [h26', rLG_succ _ _ _ hhi]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with e | e
        · rw [e, iteT rfl, ← List.append_assoc, List.length_append, List.length_append,
            List.length_singleton, List.length_append]
        · rw [e, iteF (by omega)]; rfl
      · rw [hm', rLG_succ _ _ _ hhi]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with e | e
        · rw [e, iteT rfl, Nat.sub_zero, Nat.mul_one, ← List.append_assoc]
          have hnd := fLG_nodup (kp := kp) (t := t + 1) hrvm hrr
          rw [rLG_succ _ _ _ hhi, e, iteT rfl, ← List.append_assoc] at hnd
          have hn : rv (cL.getD t 0) ∉ cL ++ rLG kp rv cL t := by
            have := (List.nodup_append.1 hnd).2.2
            exact fun h => this _ h _ (List.mem_singleton_self _) rfl
          rw [j2.2 _ hrm, iteF hn, Nat.zero_add]
          exact j2.append hrm hn dPC
        · rw [e, iteF (by omega), Nat.sub_self, Nat.mul_zero, Nat.add_zero]
          exact j2.keep hrm rfl dPC
      · rw [hm', upd_other _ _ _ (fun h => ha1 ⟨by omega, by omega⟩),
          upd_other _ _ _ (fun h => ha2 ⟨by omega, by omega⟩)]
        exact j3 a ha1 ha2)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j7, j2, j3, fun x hx => ?_, by rw [j4, gr₁],
    by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x hx]
  exact q x (by omega)

/-- **The numbering of the closure**: from `POS` zero, within `31 m + 9` steps
`LRep (cLG kp m ++ rLG kp rv (cLG kp m) m')` (`m' = |cLG kp m|` in `r7527`, the length of the
whole list in `r7526`). -/
theorem nmProg_exec (c : Config) (hc : WordsBounded W c) {m RVb KPb POb CDb : ℕ}
    {kp rv : ℕ → ℕ} (r00 : c.nreg 7500 = m) (r01 : c.nreg 7501 = RVb) (r14 : c.nreg 7514 = KPb)
    (r16 : c.nreg 7516 = POb) (r17 : c.nreg 7517 = CDb)
    (hkp : ∀ j < m, c.nmem (KPb + j) = kp j) (hk1 : ∀ j < m, kp j ≤ 1)
    (hrv : ∀ j < m, c.nmem (RVb + j) = rv j) (hrvm : ∀ j < m, rv j < m)
    (hrr : ∀ j < m, rv (rv j) = j) (hP0 : ∀ j < m, c.nmem (POb + j) = 0)
    (dKP : KPb + m ≤ POb) (dPC : POb + m ≤ CDb) (dRV : CDb + m + 1 ≤ RVb) (wR : RVb + m ≤ W) :
    ∃ c' k, Exec P W nmProg c c' k ∧ k ≤ 31 * m + 9 ∧
      c'.nreg 7527 = (cLG kp m).length ∧
      c'.nreg 7526 = (cLG kp m ++ rLG kp rv (cLG kp m) (cLG kp m).length).length ∧
      LRep (cLG kp m ++ rLG kp rv (cLG kp m) (cLG kp m).length) c'.nmem CDb POb m ∧
      (∀ a, ¬ (POb ≤ a ∧ a < POb + m) → ¬ (CDb ≤ a ∧ a < CDb + m + 1) → c'.nmem a = c.nmem a) ∧
      c'.nreg 7522 = 1 ∧ c'.nreg 7525 = c.nreg 7525 ∧
      (∀ r, (r < 7522 ∨ 7539 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a26, aL, aF, a22, a25, aR, ar, arm, ao⟩ :=
    nmL1_exec (P := P) c hc r00 r14 r16 r17 hkp hk1 hP0 dKP dPC (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, b27, bR, bm, br, brm, bo⟩ : ∃ c₂ k₂,
      Exec P W (block [.copyN 7527 7526]) c₁ c₂ k₂ ∧ k₂ = 1 ∧ c₂.nreg 7527 = c₁.nreg 7526 ∧
      (∀ x, x ≠ 7527 → c₂.nreg x = c₁.nreg x) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    have hw := e₁.wb_right
    exec_block
    refine ⟨rfl, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp; simp (disch := omega) only [Machine.upd_other]
  have hm₂ : ∀ a, ¬ (POb ≤ a ∧ a < POb + m) → ¬ (CDb ≤ a ∧ a < CDb + m + 1) →
      c₂.nmem a = c.nmem a := fun a h1 h2 => by rw [bm]; exact aF a h1 h2
  obtain ⟨c₃, k₃, e₃, hk₃, d26, dL, dF, dR, dr, drm, do'⟩ :=
    nmL2_exec (P := P) c₂ e₂.wb_right (by rw [bR _ (by omega), aR _ (by omega), r01])
      (by rw [bR _ (by omega), aR _ (by omega), r14]) (by rw [bR _ (by omega), aR _ (by omega), r16])
      (by rw [bR _ (by omega), aR _ (by omega), r17]) (by rw [bR _ (by omega), a22])
      (by rw [bR _ (by omega), a26]) (by rw [b27, a26])
      (fun j hj => by rw [hm₂ _ (by omega) (by omega)]; exact hkp j hj) hk1
      (fun j hj => by rw [hm₂ _ (by omega) (by omega)]; exact hrv j hj) hrvm hrr
      (by rw [bm]; exact aL) dKP dPC dRV wR
  have hcl : (cLG kp m).length ≤ m := length_cLG_le kp m
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega,
    by rw [dR _ (by omega), b27, a26], d26, dL, fun a h1 h2 => by rw [dF a h1 h2, hm₂ a h1 h2],
    by rw [dR _ (by omega), bR _ (by omega), a22], by rw [dR _ (by omega), bR _ (by omega), a25],
    fun r hr => ?_, by rw [dr, br, ar],
    by rw [drm, brm, arm], by rw [do', bo, ao]⟩
  rw [dR _ (by omega), bR _ (by omega), aR _ hr]

end NsStep

end BKMNW

end PlanarFlow
