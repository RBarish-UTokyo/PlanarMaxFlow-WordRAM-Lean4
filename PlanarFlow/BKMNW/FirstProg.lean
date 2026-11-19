module

public import PlanarFlow.BKMNW.ChoiceE
public import PlanarFlow.BKMNW.GatherProg
public import PlanarFlow.BKMNW.IteR23

/-!
# The first index of every key on the machine; the anchor weights `pcExf`

Every choice of the split chain made by an enumeration of the darts (`ChoiceE.lean`) is a
`findE e n X`: the first index `i < n` with `e i ∈ X`. When the sets `X` are the classes of a
key (`X = {e i | fl i ≠ 0 ∧ key i = k}`), one scan finds the first index of *every* key at once:
`T[key i] := i + 1` at the first flagged index of each key (`key = 0` meaning "no key"), and
`OUT[i] := V` there (`0` elsewhere).

* pure: `fiF fl key i k` (the table after the indices `< i`), `fiO` (the marks), `fiF_zero_iff`,
  `fiF_pos`, `fiF_stable`, `fiF_eq_self_iff`, **`findE_fiF`** (`findE e n X` read off the table),
  **`pcExf_fiF`** (the anchor weights `pcExf` of `pcChoiceE` are the marks `fiO` with `V = K`, for
  the key "number of the hole of the tail" and the flag "in the piece map of the core").
* program `fiBody`, **`fiProg`** (registers `4480 = n`, `4481 = KEYb`, `4482 = FLb`,
  `4483 = Tb`, `4484 = OUTb`, `4485 = V`; written `4486 … 4492`), **`fiProg_exec`**: within
  `18 n + 5` steps `T[k] = fiF fl key n k` (`0 < k < nk`) and `OUT[i] = fiO V fl key i`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset

/-! ### The table of first indices -/

/-- The table after the indices `< i`: `T[k] = j + 1` for the first flagged `j < i` of key
`k ≠ 0`, or `0`. -/
def fiF (fl key : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | i + 1, k => if fiF fl key i k = 0 ∧ fl i ≠ 0 ∧ key i = k ∧ k ≠ 0 then i + 1 else fiF fl key i k

/-- The mark of index `i`: `V` at the first flagged index of its key, `0` elsewhere. -/
def fiO (V : ℕ) (fl key : ℕ → ℕ) (i : ℕ) : ℕ :=
  if fl i ≠ 0 ∧ key i ≠ 0 ∧ fiF fl key i (key i) = 0 then V else 0

variable {fl key : ℕ → ℕ}

lemma fiF_succ (i k : ℕ) : fiF fl key (i + 1) k =
    if fiF fl key i k = 0 ∧ fl i ≠ 0 ∧ key i = k ∧ k ≠ 0 then i + 1 else fiF fl key i k := rfl

lemma fiF_zero_iff (i k : ℕ) :
    fiF fl key i k = 0 ↔ (k = 0 ∨ ∀ j < i, ¬ (fl j ≠ 0 ∧ key j = k)) := by
  induction i with
  | zero => simp [fiF]
  | succ i ih =>
    rw [fiF_succ]
    by_cases h : fiF fl key i k = 0 ∧ fl i ≠ 0 ∧ key i = k ∧ k ≠ 0
    · rw [iteT h]
      refine ⟨fun h' => absurd h' (by omega), fun h' => ?_⟩
      rcases h' with h' | h'
      · exact absurd h' h.2.2.2
      · exact absurd ⟨h.2.1, h.2.2.1⟩ (h' i (by omega))
    · rw [iteF h, ih]
      constructor
      · rintro (h1 | h1)
        · exact Or.inl h1
        · by_cases hk : k = 0
          · exact Or.inl hk
          refine Or.inr fun j hj => ?_
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact h1 j hj
          · intro hh
            exact h ⟨ih.2 (Or.inr h1), hh.1, hh.2, hk⟩
      · rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr fun j hj => h1 j (by omega)

lemma fiF_pos {i k j : ℕ} (h : fiF fl key i k = j + 1) :
    j < i ∧ fl j ≠ 0 ∧ key j = k ∧ k ≠ 0 ∧ ∀ j' < j, ¬ (fl j' ≠ 0 ∧ key j' = k) := by
  induction i with
  | zero => simp [fiF] at h
  | succ i ih =>
    rw [fiF_succ] at h
    by_cases hc : fiF fl key i k = 0 ∧ fl i ≠ 0 ∧ key i = k ∧ k ≠ 0
    · rw [iteT hc] at h
      have hj : j = i := by omega
      subst hj
      have := (fiF_zero_iff (fl := fl) (key := key) j k).1 hc.1
      rcases this with h0 | h0
      · exact absurd h0 hc.2.2.2
      · exact ⟨by omega, hc.2.1, hc.2.2.1, hc.2.2.2, h0⟩
    · rw [iteF hc] at h
      obtain ⟨a, b, c, d, e⟩ := ih h
      exact ⟨by omega, b, c, d, e⟩

/-- Once set, an entry of the table stays. -/
lemma fiF_stable {i k : ℕ} (h : fiF fl key i k ≠ 0) : ∀ i', i ≤ i' → fiF fl key i' k = fiF fl key i k := by
  intro i' hi'
  induction i' with
  | zero => have : i = 0 := by omega
            subst this; rfl
  | succ i' ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hi') with hlt | heq
    · have ih' := ih (by omega)
      rw [fiF_succ, iteF (fun hc => h (ih' ▸ hc.1)), ih']
    · rw [heq]

/-- A flagged index of its key is the first one iff the table had no entry for the key. -/
lemma fiF_eq_self_iff {n i : ℕ} (hi : i < n) (hfl : fl i ≠ 0) (hk : key i ≠ 0) :
    fiF fl key n (key i) = i + 1 ↔ fiF fl key i (key i) = 0 := by
  have hstep : fiF fl key (i + 1) (key i) ≠ 0 := by
    rw [fiF_succ]; split_ifs <;> omega
  have hs := fiF_stable hstep n (by omega)
  constructor
  · intro h
    rw [fiF_zero_iff]
    refine Or.inr fun j hj hh => ?_
    obtain ⟨-, -, -, -, h5⟩ := fiF_pos h
    exact h5 j hj hh
  · intro h
    rw [hs, fiF_succ, iteT ⟨h, hfl, rfl, hk⟩]

/-- **The first index of a class read off the table**: for `X` the darts `e i` (`i < n`) of
key `k ≠ 0` and flag `≠ 0`, `findE e n X` is `e (T[k] - 1)`, or `none` if `T[k] = 0`. -/
theorem findE_fiF {D : Type*} [DecidableEq D] {e : ℕ → D} {n k : ℕ} {X : Finset D} (hk : k ≠ 0)
    (hX : ∀ i < n, (e i ∈ X ↔ fl i ≠ 0 ∧ key i = k)) :
    findE e n X = if fiF fl key n k = 0 then none else some (e (fiF fl key n k - 1)) := by
  suffices h : ∀ m ≤ n, (List.range m).find? (fun i => decide (e i ∈ X)) =
      if fiF fl key m k = 0 then none else some (fiF fl key m k - 1) by
    unfold findE
    rw [h n le_rfl]
    split_ifs <;> rfl
  intro m hm
  induction m with
  | zero => simp [fiF]
  | succ m ih =>
    rw [List.range_succ, List.find?_append, ih (by omega), fiF_succ]
    by_cases h0 : fiF fl key m k = 0
    · have hx := hX m (by omega)
      by_cases hp : fl m ≠ 0 ∧ key m = k
      · have hm' : e m ∈ X := hx.2 hp
        simp [h0, hp.1, hp.2, hk, hm']
      · have hm' : e m ∉ X := fun h => hp (hx.1 h)
        have hc : ¬ (fiF fl key m k = 0 ∧ fl m ≠ 0 ∧ key m = k ∧ k ≠ 0) :=
          fun hc => hp ⟨hc.2.1, hc.2.2.1⟩
        simp [h0, hm', hc]
        exact fun a b => absurd ⟨a, b⟩ hp
    · have hc : ¬ (fiF fl key m k = 0 ∧ fl m ≠ 0 ∧ key m = k ∧ k ≠ 0) := fun hc => h0 hc.1
      simp [h0, hc]

/-! ### The anchor weights of the holes -/

section Exf

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

open Classical in
/-- **The anchor weights `pcExf` of the enumeration's choices are the marks of the first index of
each hole**: with the flag "in the piece map of the core" (`fl`) and a key numbering the holes of
the tails (`key i ≠ 0` iff the tail of `e i` lies in a hole, and then equal keys are the darts
with their tails in that hole), `pcExf (e i) = fiO K fl key i` for `i < n` (`e` injective on
`[0, n)`). -/
theorem pcExf_fiF {Q : Finset V} {P : Finset D} {Hs : List (Finset V)} {e : ℕ → D} {n : ℕ}
    (d₀ : D) (K : ℕ) (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j)
    (hfl : ∀ i < n, (fl i ≠ 0 ↔ e i ∈ pdarts M (core M Q P) Hs))
    (hkey : ∀ i < n, (key i ≠ 0 ↔ ∃ H ∈ Hs, M.tail (e i) ∈ H))
    (hkeyH : ∀ i < n, ∀ H ∈ Hs, M.tail (e i) ∈ H → ∀ j < n, (M.tail (e j) ∈ H ↔ key j = key i))
    {i : ℕ} (hi : i < n) :
    pcExf M (pcChoiceE M Q e n d₀) Q P Hs K (e i) = fiO K fl key i := by
  unfold pcExf fiO
  by_cases hc : fl i ≠ 0 ∧ key i ≠ 0
  · obtain ⟨H, hH, htH⟩ := (hkey i hi).1 hc.2
    -- the anchor of a hole containing the tail of `e i` is the first index of the key
    have hanch : ∀ H' ∈ Hs, M.tail (e i) ∈ H' →
        (pcChoiceE M Q e n d₀).anch P Hs H' = e (fiF fl key n (key i) - 1) := by
      intro H' hH' ht'
      have hX : ∀ j < n, (e j ∈ (pdarts M (core M Q P) Hs).filter (fun b => M.tail b ∈ H') ↔
          fl j ≠ 0 ∧ key j = key i) := by
        intro j hj
        rw [mem_filter, ← hfl j hj, hkeyH i hi H' hH' ht' j hj]
      have hne : fiF fl key n (key i) ≠ 0 := by
        rw [Ne, fiF_zero_iff]; push Not
        exact ⟨hc.2, i, hi, hc.1, rfl⟩
      show firstE e n _ d₀ = _
      unfold firstE
      rw [findE_fiF hc.2 hX, iteF hne]
      rfl
    have hcore : e i ∈ pdarts M (core M Q P) Hs := (hfl i hi).1 hc.1
    have hsame : (∃ H' ∈ Hs, M.tail (e i) ∈ H' ∧ (pcChoiceE M Q e n d₀).anch P Hs H' = e i) ↔
        fiF fl key n (key i) = i + 1 := by
      constructor
      · rintro ⟨H', hH', ht', ha⟩
        rw [hanch H' hH' ht'] at ha
        have hne : fiF fl key n (key i) ≠ 0 := by
          rw [Ne, fiF_zero_iff]; push Not
          exact ⟨hc.2, i, hi, hc.1, rfl⟩
        obtain ⟨j, hj⟩ : ∃ j, fiF fl key n (key i) = j + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero hne).symm⟩
        rw [hj, Nat.add_sub_cancel] at ha
        have := (fiF_pos hj).1
        rw [hj, hinj j this i hi ha]
      · intro h
        refine ⟨H, hH, htH, ?_⟩
        rw [hanch H hH htH, h, Nat.add_sub_cancel]
    rw [fiF_eq_self_iff hi hc.1 hc.2] at hsame
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd ⟨hc.1, hc.2, hsame.1 h1.2⟩ h2
    · exact absurd ⟨hcore, hsame.2 h2.2.2⟩ h1
    · rfl
  · split_ifs with h1 h2 h2
    · rfl
    · obtain ⟨hcore, H, hH, htH, -⟩ := h1
      exact absurd ⟨(hfl i hi).2 hcore, (hkey i hi).2 ⟨H, hH, htH⟩⟩ hc
    · exact absurd ⟨h2.1, h2.2.1⟩ hc
    · rfl

end Exf

/-! ### The program -/

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- Read the flag `f = FL[i]` and the key `k = KEY[i]`, clear `OUT[i]`. -/
def fiB1 : Stmt := block [.addN 4489 4482 4488, .loadN 4489 4489, .addN 4490 4481 4488,
  .loadN 4490 4490, .addN 4491 4484 4488, .storeN 4491 4487]

/-- Read `T[k]`. -/
def fiB2 : Stmt := block [.addN 4492 4483 4490, .loadN 4489 4492]

/-- The first index of its key: `T[k] := i + 1`, `OUT[i] := V`. -/
def fiB3 : Stmt := block [.addN 4489 4488 4486, .storeN 4492 4489, .storeN 4491 4485]

/-- The test of a flagged, keyed index. -/
def fiIn : Stmt := .seq fiB2 (.ifLtN 4487 4489 .skip fiB3)

/-- **One index.** -/
def fiBody : Stmt :=
  .seq fiB1 (.seq (.ifLtN 4487 4489 (.ifLtN 4487 4490 fiIn .skip) .skip)
    (block [.addN 4488 4488 4486]))

/-- **The first index of every key** (registers `4480 = n`, `4481 = KEYb`, `4482 = FLb`,
`4483 = Tb`, `4484 = OUTb`, `4485 = V`). -/
def fiProg : Stmt :=
  .seq (block [.constN 4486 1, .constN 4487 0, .constN 4488 0]) (.whileLtN 4488 4480 fiBody)

/-- The memory after one index. -/
def fiM (m : ℕ → ℕ) (Tb OUTb V i f k : ℕ) : ℕ → ℕ :=
  if 0 < f ∧ 0 < k ∧ upd m (OUTb + i) 0 (Tb + k) = 0 then
    upd (upd (upd m (OUTb + i) 0) (Tb + k) (i + 1)) (OUTb + i) V
  else upd m (OUTb + i) 0

section Exec

variable {P : Input} {W : ℕ}

theorem fiB1_exec (c : Config) (hc : WordsBounded W c) {KEYb FLb OUTb i : ℕ}
    (r1 : c.nreg 4481 = KEYb) (r2 : c.nreg 4482 = FLb) (r4 : c.nreg 4484 = OUTb)
    (r7 : c.nreg 4487 = 0) (r8 : c.nreg 4488 = i)
    (w1 : KEYb + i ≤ W) (w2 : FLb + i ≤ W) (w3 : OUTb + i ≤ W) :
    ∃ c' k, Exec P W fiB1 c c' k ∧ k = 6 ∧ c'.nreg 4489 = c.nmem (FLb + i) ∧
      c'.nreg 4490 = c.nmem (KEYb + i) ∧ c'.nreg 4491 = OUTb + i ∧
      c'.nmem = upd c.nmem (OUTb + i) 0 ∧
      (∀ x, x ≠ 4489 → x ≠ 4490 → x ≠ 4491 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fiB1
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r4, r7, r8]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r1, r2, r4, r8]
  · config_simp; simp only [r1, r2, r4, r8]
  · config_simp; simp only [r4, r8]
  · config_simp; simp only [r4, r7, r8]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem fiB2_exec (c : Config) (hc : WordsBounded W c) {Tb k : ℕ}
    (r3 : c.nreg 4483 = Tb) (r10 : c.nreg 4490 = k) (w : Tb + k ≤ W) :
    ∃ c' t, Exec P W fiB2 c c' t ∧ t = 2 ∧ c'.nreg 4489 = c.nmem (Tb + k) ∧
      c'.nreg 4492 = Tb + k ∧ c'.nmem = c.nmem ∧
      (∀ x, x ≠ 4489 → x ≠ 4492 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fiB2
  exec_block
  all_goals try (config_simp; simp only [r3, r10]; omega)
  refine ⟨rfl, ?_, ?_, rfl, fun x h1 h2 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r3, r10]
  · config_simp; simp only [r3, r10]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem fiB3_exec (c : Config) (hc : WordsBounded W c) {Tb OUTb V i k : ℕ}
    (r5 : c.nreg 4485 = V) (r6 : c.nreg 4486 = 1) (r8 : c.nreg 4488 = i)
    (r11 : c.nreg 4491 = OUTb + i) (r12 : c.nreg 4492 = Tb + k) (w1 : i + 1 ≤ W) :
    ∃ c' t, Exec P W fiB3 c c' t ∧ t = 3 ∧
      c'.nmem = upd (upd c.nmem (Tb + k) (i + 1)) (OUTb + i) V ∧
      (∀ x, x ≠ 4489 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hV : V ≤ W := r5 ▸ hc.1 4485
  unfold fiB3
  exec_block
  all_goals try (config_simp; simp only [r5, r6, r8, r11, r12]; omega)
  refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r5, r6, r8, r11, r12]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **One index**: within `16` steps, the memory `fiM`. -/
theorem fiBody_exec (c : Config) (hc : WordsBounded W c) {KEYb FLb Tb OUTb V i : ℕ}
    (r1 : c.nreg 4481 = KEYb) (r2 : c.nreg 4482 = FLb) (r3 : c.nreg 4483 = Tb)
    (r4 : c.nreg 4484 = OUTb) (r5 : c.nreg 4485 = V) (r6 : c.nreg 4486 = 1)
    (r7 : c.nreg 4487 = 0) (r8 : c.nreg 4488 = i)
    (w1 : KEYb + i ≤ W) (w2 : FLb + i ≤ W) (w3 : OUTb + i ≤ W)
    (w4 : Tb + c.nmem (KEYb + i) ≤ W) (w5 : i + 1 ≤ W) :
    ∃ c' t, Exec P W fiBody c c' t ∧ t ≤ 16 ∧ c'.nreg 4488 = i + 1 ∧
      c'.nmem = fiM c.nmem Tb OUTb V i (c.nmem (FLb + i)) (c.nmem (KEYb + i)) ∧
      (∀ x, (x < 4488 ∨ 4492 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fiBody
  set f := c.nmem (FLb + i) with hf
  set k := c.nmem (KEYb + i) with hk
  obtain ⟨c₁, t₁, e₁, ht₁, g9, g10, g11, gm₁, gn₁, gr₁, grm₁, go₁⟩ :=
    fiB1_exec (P := P) c hc r1 r2 r4 r7 r8 w1 w2 w3
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 4489 → x ≠ 4490 → x ≠ 4491 → c₁.nreg x = c.nreg x := gn₁
  have q7 : c₁.nreg 4487 = 0 := by rw [q _ (by omega) (by omega) (by omega), r7]
  -- the tests
  obtain ⟨c₂, t₂, e₂, ht₂, gm₂, gn₂, gr₂, grm₂, go₂⟩ : ∃ c₂ t₂,
      Exec P W (.ifLtN 4487 4489 (.ifLtN 4487 4490 fiIn .skip) .skip) c₁ c₂ t₂ ∧ t₂ ≤ 9 ∧
      c₂.nmem = fiM c.nmem Tb OUTb V i f k ∧
      (∀ x, x ≠ 4489 → x ≠ 4490 → x ≠ 4491 → x ≠ 4492 → c₂.nreg x = c.nreg x) ∧
      c₂.rreg = c.rreg ∧ c₂.rmem = c.rmem ∧ c₂.output = c.output := by
    by_cases hf0 : c₁.nreg 4487 < c₁.nreg 4489
    · by_cases hk0 : c₁.nreg 4487 < c₁.nreg 4490
      · obtain ⟨c₃, t₃, e₃, ht₃, h9, h12, gm₃, gn₃, gr₃, grm₃, go₃⟩ :=
          fiB2_exec (P := P) c₁ hw₁ (by rw [q _ (by omega) (by omega) (by omega), r3]) g10 w4
        have hw₃ := e₃.wb_right
        have q' : ∀ x, x ≠ 4489 → x ≠ 4490 → x ≠ 4491 → x ≠ 4492 → c₃.nreg x = c.nreg x :=
          fun x a b d e => (gn₃ x a e).trans (q x a b d)
        have e9 : c₃.nreg 4489 = upd c.nmem (OUTb + i) 0 (Tb + k) := by rw [h9, gm₁]
        have e7 : c₃.nreg 4487 = 0 := by rw [gn₃ _ (by omega) (by omega), q7]
        by_cases hT : c₃.nreg 4487 < c₃.nreg 4489
        · refine ⟨c₃, t₃ + 1 + 1 + 1, .ifLtN_true hf0 (.ifLtN_true hk0
            (.seq e₃ (.ifLtN_true hT (.skip hw₃)))), by omega, ?_, q', by rw [gr₃, gr₁],
            by rw [grm₃, grm₁], by rw [go₃, go₁]⟩
          rw [gm₃, gm₁]
          have hT' : ¬ (upd c.nmem (OUTb + i) 0 (Tb + k) = 0) := by
            omega
          unfold fiM
          rw [iteF (fun h => hT' h.2.2)]
        · obtain ⟨c₄, t₄, e₄, ht₄, gm₄, gn₄, gr₄, grm₄, go₄⟩ :=
            fiB3_exec (P := P) c₃ hw₃ (by rw [q' _ (by omega) (by omega) (by omega) (by omega), r5])
              (by rw [q' _ (by omega) (by omega) (by omega) (by omega), r6])
              (by rw [q' _ (by omega) (by omega) (by omega) (by omega), r8])
              (by rw [gn₃ _ (by omega) (by omega), g11]) h12 w5
          refine ⟨c₄, t₃ + (t₄ + 2) + 1 + 1, .ifLtN_true hf0 (.ifLtN_true hk0
            (.seq e₃ (.ifLtN_false hT e₄))), by omega, ?_,
            fun x a b d e => (gn₄ x a).trans (q' x a b d e), by rw [gr₄, gr₃, gr₁],
            by rw [grm₄, grm₃, grm₁], by rw [go₄, go₃, go₁]⟩
          have hT' : upd c.nmem (OUTb + i) 0 (Tb + k) = 0 := by
            omega
          have hf' : 0 < f := by rw [g9, q7] at hf0; exact hf0
          have hk' : 0 < k := by rw [g10, q7] at hk0; exact hk0
          rw [gm₄, gm₃, gm₁]
          unfold fiM
          rw [iteT ⟨hf', hk', hT'⟩]
      · refine ⟨c₁, 0 + 2 + 1, .ifLtN_true hf0 (.ifLtN_false hk0 (.skip hw₁)), by omega, ?_,
          fun x a b d e => q x a b d, gr₁, grm₁, go₁⟩
        have hk' : ¬ 0 < k := by rw [g10, q7] at hk0; exact hk0
        rw [gm₁]; unfold fiM; rw [iteF (fun h => hk' h.2.1)]
    · refine ⟨c₁, 0 + 2, .ifLtN_false hf0 (.skip hw₁), by omega, ?_,
        fun x a b d e => q x a b d, gr₁, grm₁, go₁⟩
      have hf' : ¬ 0 < f := by rw [g9, q7] at hf0; exact hf0
      rw [gm₁]; unfold fiM; rw [iteF (fun h => hf' h.1)]
  have hw₂ := e₂.wb_right
  obtain ⟨c₃, t₃, e₃, ht₃, h88, gn₃, gm₃, gr₃, grm₃, go₃⟩ : ∃ c₃ t₃,
      Exec P W (block [.addN 4488 4488 4486]) c₂ c₃ t₃ ∧ t₃ = 1 ∧ c₃.nreg 4488 = i + 1 ∧
      (∀ x, x ≠ 4488 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have p6 : c₂.nreg 4486 = 1 := by
      rw [gn₂ _ (by omega) (by omega) (by omega) (by omega), r6]
    have p8 : c₂.nreg 4488 = i := by
      rw [gn₂ _ (by omega) (by omega) (by omega) (by omega), r8]
    exec_block
    all_goals try (config_simp; simp only [p6, p8]; omega)
    refine ⟨rfl, ?_, fun x h => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [p6, p8]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, h88, by rw [gm₃, gm₂],
    fun x hx => ?_, by rw [gr₃, gr₂], by rw [grm₃, grm₂], by rw [go₃, go₂]⟩
  rw [gn₃ x (by omega), gn₂ x (by omega) (by omega) (by omega) (by omega)]

lemma fiM_apply (m : ℕ → ℕ) (Tb OUTb V i f k a : ℕ) (hd : Tb + k ≠ OUTb + i) :
    fiM m Tb OUTb V i f k a =
      if a = OUTb + i then (if 0 < f ∧ 0 < k ∧ m (Tb + k) = 0 then V else 0)
      else if a = Tb + k ∧ 0 < f ∧ 0 < k ∧ m (Tb + k) = 0 then i + 1 else m a := by
  have e : upd m (OUTb + i) 0 (Tb + k) = m (Tb + k) := upd_other _ _ _ hd
  unfold fiM
  rw [e]
  by_cases hc : 0 < f ∧ 0 < k ∧ m (Tb + k) = 0
  · simp only [hc, and_self, and_true, ↓reduceIte, upd_apply]
    split_ifs <;> first | rfl | omega
  · simp only [hc, and_false, ↓reduceIte, upd_apply]
    try (split_ifs <;> first | rfl | omega)

/-- **The first index of every key on the machine.** With the keys `KEY[i] < nk` and flags
`FL[i]` (`i < n`) below the table `T` (`nk` words, zero on `[1, nk)`), and the marks `OUT` above
it, within `18 n + 5` steps `T[k] = fiF FL KEY n k` (`0 < k < nk`) and `OUT[i] = fiO V FL KEY i`
(`i < n`); the rest of the memory, the registers outside `4486 … 4492`, reals and output are
kept. -/
theorem fiProg_exec (c : Config) (hc : WordsBounded W c) {n KEYb FLb Tb OUTb V nk : ℕ}
    (r0 : c.nreg 4480 = n) (r1 : c.nreg 4481 = KEYb) (r2 : c.nreg 4482 = FLb)
    (r3 : c.nreg 4483 = Tb) (r4 : c.nreg 4484 = OUTb) (r5 : c.nreg 4485 = V)
    (hkey : ∀ i < n, c.nmem (KEYb + i) < nk)
    (lay : KEYb + n ≤ Tb ∧ FLb + n ≤ Tb ∧ Tb + nk ≤ OUTb ∧ OUTb + n ≤ W ∧ n + 1 ≤ W)
    (hT0 : ∀ k, 0 < k → k < nk → c.nmem (Tb + k) = 0) :
    ∃ c' t, Exec P W fiProg c c' t ∧ t ≤ 18 * n + 5 ∧
      (∀ k, 0 < k → k < nk →
        c'.nmem (Tb + k) = fiF (fun i => c.nmem (FLb + i)) (fun i => c.nmem (KEYb + i)) n k) ∧
      (∀ i < n,
        c'.nmem (OUTb + i) = fiO V (fun i => c.nmem (FLb + i)) (fun i => c.nmem (KEYb + i)) i) ∧
      (∀ a, (a < Tb + 1 ∨ (Tb + nk ≤ a ∧ a < OUTb) ∨ OUTb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4486 ∨ 4492 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5⟩ := lay
  unfold fiProg
  obtain ⟨c₁, k₁, e₁, hk₁, g6, g7, g8, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 4486 1, .constN 4487 0, .constN 4488 0]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 4486 = 1 ∧ c₁.nreg 4487 = 0 ∧ c₁.nreg 4488 = 0 ∧
      (∀ x, x ≠ 4486 → x ≠ 4487 → x ≠ 4488 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x a b d => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 4486 → x ≠ 4487 → x ≠ 4488 → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  set fl : ℕ → ℕ := fun i => m₀ (FLb + i) with hfl
  set key : ℕ → ℕ := fun i => m₀ (KEYb + i) with hkeyd
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 4488 ∨ 4492 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ k, 0 < k → k < nk → c'.nmem (Tb + k) = fiF fl key i k) ∧
    (∀ j < i, c'.nmem (OUTb + j) = fiO V fl key j) ∧
    (∀ a, (a < Tb + 1 ∨ (Tb + nk ≤ a ∧ a < OUTb) ∨ OUTb + i ≤ a) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h88, j1, j2, j3, j4, j5, j6, j7⟩ := tgRange (P := P) (a := 4488)
    (b := 4480) (body := fiBody) J (B := 16) c₁ hw₁ g8 (by rw [q _ (by omega) (by omega)
      (by omega), r0]) (Nat.zero_le n)
    ⟨fun _ _ => rfl, fun k hk hk' => by rw [gm₁, hT0 k hk hk']; rfl,
      fun j hj => absurd hj (by omega), fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h88 h80 ⟨j1, j2, j3, j4, j5, j6, j7⟩ => by
      have f : ∀ x, (x < 4488 ∨ 4492 < x) → c'.nreg x = c₁.nreg x := j1
      have eF : c'.nmem (FLb + i) = fl i := j4 _ (Or.inl (by omega))
      have eK : c'.nmem (KEYb + i) = key i := j4 _ (Or.inl (by omega))
      have hki : key i < nk := hkey i hhi
      obtain ⟨c'', t, ex, ht, h88', hm', hn', hr', hrm', ho'⟩ := fiBody_exec (P := P) c' hw
        (by rw [f _ (by omega), q _ (by omega) (by omega) (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega) (by omega) (by omega), r2])
        (by rw [f _ (by omega), q _ (by omega) (by omega) (by omega), r3])
        (by rw [f _ (by omega), q _ (by omega) (by omega) (by omega), r4])
        (by rw [f _ (by omega), q _ (by omega) (by omega) (by omega), r5])
        (by rw [f _ (by omega), g6]) (by rw [f _ (by omega), g7]) h88 (by omega) (by omega)
        (by omega) (by rw [eK]; omega) (by omega)
      rw [eF, eK] at hm'
      have hd : Tb + key i ≠ OUTb + i := by omega
      -- the condition of the step
      have hcond : (0 < fl i ∧ 0 < key i ∧ c'.nmem (Tb + key i) = 0) ↔
          (fl i ≠ 0 ∧ key i ≠ 0 ∧ fiF fl key i (key i) = 0) := by
        constructor
        · rintro ⟨a, b, d⟩
          refine ⟨by omega, by omega, ?_⟩
          rw [← j2 _ b hki]; exact d
        · rintro ⟨a, b, d⟩
          refine ⟨by omega, by omega, ?_⟩
          rw [j2 _ (by omega) hki]; exact d
      refine ⟨c'', t, ex, ht, h88', by rw [hn' _ (by omega)]; exact h80,
        ⟨fun x hx => by rw [hn' x hx, f x hx], fun k hk hk' => ?_, fun j hj => ?_,
        fun a ha => ?_, by rw [hr', j5], by rw [hrm', j6], by rw [ho', j7]⟩⟩
      · rw [hm', fiM_apply _ _ _ _ _ _ _ _ hd, iteF (by omega), fiF_succ]
        by_cases hkk : k = key i
        · subst hkk
          by_cases hc' : 0 < fl i ∧ 0 < key i ∧ c'.nmem (Tb + key i) = 0
          · rw [iteT ⟨rfl, hc'⟩, iteT ⟨(hcond.1 hc').2.2, (hcond.1 hc').1, rfl, by omega⟩]
          · rw [iteF (fun h => hc' h.2), iteF (fun h => hc' (hcond.2 ⟨h.2.1, h.2.2.2, h.1⟩)),
              j2 _ hk hk']
        · rw [iteF (fun h => hkk (by omega)), iteF (fun h => hkk h.2.2.1.symm), j2 _ hk hk']
      · rw [hm', fiM_apply _ _ _ _ _ _ _ _ hd]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [iteF (by omega), iteF (fun h => by omega)]
          exact j3 j hj
        · rw [iteT rfl]
          unfold fiO
          by_cases hc' : 0 < fl j ∧ 0 < key j ∧ c'.nmem (Tb + key j) = 0
          · rw [iteT hc', iteT (hcond.1 hc')]
          · rw [iteF hc', iteF (fun h => hc' (hcond.2 h))]
      · rw [hm', fiM_apply _ _ _ _ _ _ _ _ hd, iteF (by omega)]
        have hne : ¬ (a = Tb + key i ∧ 0 < fl i ∧ 0 < key i ∧ c'.nmem (Tb + key i) = 0) := by
          rintro ⟨rfl, -, h2, -⟩; omega
        rw [iteF hne]
        exact j4 a (by omega))
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3, j4, fun x hx => ?_, by rw [j5, gr₁],
    by rw [j6, grm₁], by rw [j7, go₁]⟩
  rw [j1 x (by omega), q x (by omega) (by omega) (by omega)]

end Exec

end BKMNW

end PlanarFlow
