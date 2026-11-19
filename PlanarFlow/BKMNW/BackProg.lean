module

public import PlanarFlow.BKMNW.ScertProg
public import PlanarFlow.BKMNW.PruneProg

/-!
# The backward pass of `scertD` on the machine: the records applied to the items

After the level loop `slProg` (`ScertProg.lean`) and the base case, `scertD` is
`(ρ, applyPr Hs ρ rs I₀)` for the path `ρ` and items `I₀` of the base (`scertD_iter`). Here the
records `rs` (stored by `slProg`, `RecOK`) are applied to the items on labels, the last record
first, by one `prProg` each (`prProg_exec`, `pruneI_rep`), with fresh labels `L₀, L₀ + 1, …`.

* pure: `scStep_rec`, **`scIter_chain`** (the kept darts of a record are the darts of the record
  after it; the records start at `s₀`), `pruneI_sub`, **`itemRep_disjB`** (items represented by
  labels are pairwise disjoint), `take_succ_eq`;
* `bpBody`, **`bpProg`** (registers `4940 = k`, `4941 = 1`, `4942 = RECb`, `4944 = L`, `4945`,
  `4946`, `4947 = 0` and `4500 … 4505` written; inputs `4933 = ℓ`, `4936 = RECb`, `4943 = NHb`,
  `4944 = L₀`, `4502 = LABb`);
* **`bpProg_exec`**: with the records `RecOK` of `rs` from `scIter … ℓ s₀ = some (s, rs)`, the
  items `I₀ ⊆ s.1` represented by the labels at `LABb` (labels `< L₀`, `1 ≤ L₀`), the flags
  `NH[i] ≠ 0 ↔ tail (e i) ∈ newHole Hs ρ.mverts`, within `ℓ (7 n + 40) + 6` steps the labels
  represent **`applyPr Hs ρ rs I₀`**.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Relation WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### Pure facts -/

section Pure

open Equiv Orbit

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

open Classical in
/-- The record of a prune: the darts before, the kept darts (those of the next state), inside. -/
theorem scStep_rec (ch : ScChoice M) (Hs : List (Finset V)) {s s' : ScSt D} {r : ScRec D}
    (h : scStep ch Hs s = some (s', r)) : r.1 = s.1 ∧ r.2.1 = s'.1 ∧ r.2.1 ⊆ r.1 := by
  obtain ⟨N, τ, ex⟩ := s
  by_cases hnc : NoCut M N Hs
  · simp [scStep, hnc] at h
  rcases hh : ch.hole N with _ | g
  · simp [scStep, hnc, hh] at h
  rcases hz : ch.heavy N g ex with _ | z
  · simp [scStep, hnc, hh, hz] at h
  rcases ha : ch.anchor (comp M N Hs g z) g with _ | a₀
  · simp [scStep, hnc, hh, hz, ha] at h
  by_cases hK : (comp M N Hs g z).card < N.card
  · simp only [scStep, hnc, hh, hz, ha, hK, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, fun d hd => (mem_comp.1 hd).1⟩
  · simp [scStep, hnc, hh, hz, ha, hK] at h

/-- **The chain of the records** (last one first): the kept darts of record `j` are the darts of
record `j - 1` (of the final state for `j = 0`) and lie in the darts of record `j`; the first
record (the last in the list) starts at `s₀`. -/
theorem scIter_chain (ch : ScChoice M) (Hs : List (Finset V)) :
    ∀ (ℓ : ℕ) (s₀ s : ScSt D) (rs : List (ScRec D)), scIter ch Hs ℓ s₀ = some (s, rs) →
      (∀ j (hj : j < rs.length), rs[j].2.1 ⊆ rs[j].1 ∧
        rs[j].2.1 = if h : j = 0 then s.1 else (rs[j - 1]'(by omega)).1) ∧
      ∀ hj : 0 < rs.length, (rs[rs.length - 1]'(by omega)).1 = s₀.1 := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro s₀ s rs h
    simp only [scIter, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun j hj => absurd hj (by simp), fun hj => absurd hj (by simp)⟩
  | succ ℓ ih =>
    intro s₀ s rs h
    rw [scIter] at h
    cases hs : scStep ch Hs s₀ with
    | none => rw [hs] at h; exact absurd h (by simp)
    | some p =>
      obtain ⟨s₁, r₀⟩ := p
      rw [hs] at h
      simp only at h
      cases h1 : scIter ch Hs ℓ s₁ with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some q =>
        obtain ⟨s₂, rs'⟩ := q
        rw [h1] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨c1, c2⟩ := ih s₁ s₂ rs' h1
        obtain ⟨q1, q2, q3⟩ := scStep_rec ch Hs hs
        have hlen := (scIter_depth ch Hs ℓ s₁ s₂ rs' h1).2
        refine ⟨fun j hj => ?_, fun hj => ?_⟩
        · simp only [List.length_append, List.length_singleton] at hj
          by_cases hjl : j < rs'.length
          · rw [List.getElem_append_left hjl]
            obtain ⟨a1, a2⟩ := c1 j hjl
            refine ⟨a1, ?_⟩
            rw [a2]
            by_cases hj0 : j = 0
            · simp [hj0]
            · simp only [hj0, ↓reduceDIte]
              rw [List.getElem_append_left (by omega)]
          · have hjl' : j = rs'.length := by omega
            subst hjl'
            rw [List.getElem_append_right (by omega)]
            simp only [Nat.sub_self, List.getElem_singleton]
            refine ⟨q3, ?_⟩
            by_cases hj0 : rs'.length = 0
            · simp only [hj0, ↓reduceDIte]
              rw [q2]
              have hℓ0 : ℓ = 0 := by omega
              subst hℓ0
              simp only [scIter, Option.some.injEq, Prod.mk.injEq] at h1
              rw [h1.1]
            · simp only [hj0, ↓reduceDIte]
              rw [List.getElem_append_left (by omega), c2 (by omega), q2]
        · simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
          rw [List.getElem_append_right (by omega)]
          simp only [Nat.sub_self, List.getElem_singleton]
          exact q1

/-- The items of a prune lie in the darts before it. -/
lemma pruneI_sub {Hs : List (Finset V)} {N K : Finset D} {a₀ : D} {ρ : HPath M}
    {I : Finset (Finset D)} (hI : ∀ X ∈ I, X ⊆ K) (hK : K ⊆ N) :
    ∀ X ∈ pruneI Hs N K a₀ ρ I, X ⊆ N := by
  intro X hX
  unfold pruneI at hX
  split_ifs at hX
  · rcases mem_insert.1 hX with rfl | hX
    · exact sdiff_subset
    · exact (hI X hX).trans hK
  · rcases mem_insert.1 hX with rfl | hX
    · refine union_subset ?_ sdiff_subset
      intro d hd
      obtain ⟨Y, hY, hdY⟩ := mem_biUnion.1 hd
      exact hK (hI Y (mem_filter.1 hY).1 hdY)
    · exact (hI X (mem_filter.1 hX).1).trans hK

/-- **Items represented by labels are pairwise disjoint.** -/
lemma itemRep_disjB {e : ℕ → D} {n : ℕ} {I : Finset (Finset D)} {lab : ℕ → ℕ}
    (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j) (hrep : ItemRep e n I lab) :
    ∀ X ∈ I, ∀ Y ∈ I, X ≠ Y → Disjoint X Y := by
  intro X hX Y hY hXY
  by_cases hX0 : X = ∅
  · subst hX0; exact disjoint_empty_left _
  by_cases hY0 : Y = ∅
  · subst hY0; exact disjoint_empty_right _
  have hX' : X ∈ labItems e n lab := by rw [← hrep]; exact mem_erase.2 ⟨hX0, hX⟩
  have hY' : Y ∈ labItems e n lab := by rw [← hrep]; exact mem_erase.2 ⟨hY0, hY⟩
  obtain ⟨i, hi, -, rfl⟩ := mem_labItems.1 hX'
  obtain ⟨j, hj, -, rfl⟩ := mem_labItems.1 hY'
  rw [disjoint_left]
  intro d hdi hdj
  obtain ⟨i', hi', hli, rfl⟩ := mem_clsL.1 hdi
  obtain ⟨j', hj', hlj, hej⟩ := mem_clsL.1 hdj
  have := hinj j' hj' i' hi' hej
  subst this
  exact hXY (by rw [← hli, ← hlj])

lemma take_succ_eq {α : Type*} (l : List α) {j : ℕ} (hj : j < l.length) :
    l.take (j + 1) = l.take j ++ [l[j]] := by
  rw [List.take_succ, List.getElem?_eq_getElem hj]
  rfl

end Pure

/-! ### The program -/

/-- One record (`k := k - 1`; record `k`: `IXb`, `s`, `i₀`; `bt := NH[i₀]`; the fill; `L += 1`). -/
def bpBody : Stmt :=
  .seq (block [.subN 4940 4940 4941, .addN 4945 4940 4940, .addN 4945 4945 4940,
      .addN 4945 4945 4942, .loadN 4501 4945, .addN 4945 4945 4941, .loadN 4500 4945,
      .addN 4945 4945 4941, .loadN 4504 4945, .addN 4946 4943 4504, .loadN 4505 4946,
      .copyN 4503 4944])
    (.seq prProg (block [.addN 4944 4944 4941]))

/-- **The backward pass of `scertD`**: the records `ℓ - 1, …, 0`. -/
def bpProg : Stmt :=
  .seq (block [.constN 4941 1, .constN 4947 0, .copyN 4940 4933, .copyN 4942 4936])
    (.whileLtN 4947 4940 bpBody)

section Exec

variable {P : Input} {W : ℕ}

theorem bpInit_exec (c : Config) (hc : WordsBounded W c) (w : 1 ≤ W) :
    ∃ c' t, Exec P W (block [.constN 4941 1, .constN 4947 0, .copyN 4940 4933, .copyN 4942 4936])
      c c' t ∧ t = 4 ∧ c'.nreg 4941 = 1 ∧ c'.nreg 4947 = 0 ∧ c'.nreg 4940 = c.nreg 4933 ∧
      c'.nreg 4942 = c.nreg 4936 ∧
      (∀ x, x ≠ 4940 → x ≠ 4941 → x ≠ 4942 → x ≠ 4947 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  all_goals try (config_simp; omega)
  refine ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp,
    fun x h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
  simp only [Config.nreg_mk, upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3,
    upd_other _ _ _ h4]

theorem bpLoad_exec (c : Config) (hc : WordsBounded W c) {k RECb NHb L : ℕ}
    (r40 : c.nreg 4940 = k + 1) (r41 : c.nreg 4941 = 1) (r42 : c.nreg 4942 = RECb)
    (r43 : c.nreg 4943 = NHb) (r44 : c.nreg 4944 = L)
    (w1 : RECb + 3 * k + 2 ≤ W) (w2 : NHb + c.nmem (RECb + 3 * k + 2) ≤ W) :
    ∃ c' t, Exec P W (block [.subN 4940 4940 4941, .addN 4945 4940 4940, .addN 4945 4945 4940,
      .addN 4945 4945 4942, .loadN 4501 4945, .addN 4945 4945 4941, .loadN 4500 4945,
      .addN 4945 4945 4941, .loadN 4504 4945, .addN 4946 4943 4504, .loadN 4505 4946,
      .copyN 4503 4944]) c c' t ∧ t = 12 ∧ c'.nreg 4940 = k ∧
      c'.nreg 4501 = c.nmem (RECb + 3 * k) ∧ c'.nreg 4500 = c.nmem (RECb + 3 * k + 1) ∧
      c'.nreg 4504 = c.nmem (RECb + 3 * k + 2) ∧
      c'.nreg 4505 = c.nmem (NHb + c.nmem (RECb + 3 * k + 2)) ∧ c'.nreg 4503 = L ∧
      (∀ x, x ≠ 4940 → x ≠ 4945 → x ≠ 4946 → x ≠ 4500 → x ≠ 4501 → x ≠ 4503 → x ≠ 4504 →
        x ≠ 4505 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have ea : k + k + k + RECb + 1 + 1 = RECb + 3 * k + 2 := by omega
  have ea' : k + k + k + RECb + 1 = RECb + 3 * k + 1 := by omega
  have ea'' : k + k + k + RECb = RECb + 3 * k := by omega
  exec_block
  all_goals try (config_simp; (try simp only [r40, r41, r42, r43, r44, Nat.add_sub_cancel]); (try rw [ea]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun x h1 h2 h3 h4 h5 h6 h7 h8 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals simp only [r40, r41, r42, r43, r44, Nat.add_sub_cancel]
  all_goals try rw [ea]
  all_goals try rw [ea']
  all_goals try rw [ea'']
  simp only [upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3, upd_other _ _ _ h4,
    upd_other _ _ _ h5, upd_other _ _ _ h6, upd_other _ _ _ h7, upd_other _ _ _ h8]

end Exec

/-! ### The pass -/

section Pass

open Equiv Orbit

variable {P : Input} {W : ℕ}
variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- The darts after `j` records of the pass (the final state's for `j = 0`). -/
def nsetF (s₁ : Finset D) (rs : List (ScRec D)) (j : ℕ) : Finset D :=
  if j = 0 then s₁ else ((rs[j - 1]?).map Prod.fst).getD s₁

/-- The registers the pass keeps. -/
def BpFr (x : ℕ) : Prop := x < 4500 ∨ (4511 < x ∧ x < 4940) ∨ x = 4943 ∨ 4947 < x

variable (W M) in
/-- The invariant of the pass (`k = r4940` records left; `ℓ - k` applied). -/
structure BpInv (Hs : List (Finset V)) (ρ : HPath M) (s₁ : Finset D) (rs : List (ScRec D))
    (I₀ : Finset (Finset D)) (c₀ : Config) (n ℓ RECb NHb L₀ LABb : ℕ) (e : ℕ → D)
    (c : Config) : Prop where
  wb : WordsBounded W c
  r41 : c.nreg 4941 = 1
  r47 : c.nreg 4947 = 0
  r42 : c.nreg 4942 = RECb
  r43 : c.nreg 4943 = NHb
  r02 : c.nreg 4502 = LABb
  kle : c.nreg 4940 ≤ ℓ
  r44 : c.nreg 4944 = L₀ + (ℓ - c.nreg 4940)
  rep : ItemRep e n (applyPr Hs ρ (rs.take (ℓ - c.nreg 4940)) I₀) fun i => c.nmem (LABb + i)
  fresh : ∀ i < n, c.nmem (LABb + i) < L₀ + (ℓ - c.nreg 4940)
  sub : ∀ X ∈ applyPr Hs ρ (rs.take (ℓ - c.nreg 4940)) I₀, X ⊆ nsetF s₁ rs (ℓ - c.nreg 4940)
  mem : ∀ a, (a < LABb ∨ LABb + n ≤ a) → c.nmem a = c₀.nmem a
  reg : ∀ x, BpFr x → c.nreg x = c₀.nreg x
  rr : c.rreg = c₀.rreg
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output

set_option maxHeartbeats 800000 in
/-- **One record of the pass.** -/
theorem bpBody_step {ch : ScChoice M} {Hs : List (Finset V)} {ℓ : ℕ} {s₀ s : ScSt D}
    {rs : List (ScRec D)} (hiter : scIter ch Hs ℓ s₀ = some (s, rs)) {ρ : HPath M}
    {I₀ : Finset (Finset D)} {c₀ : Config} {e : ℕ → D}
    {n RECb NHb L₀ LABb IX0 top : ℕ} (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j)
    (hrec : RecOK c₀.nmem RECb IX0 top n e rs)
    (hNH : ∀ i < n, (c₀.nmem (NHb + i) ≠ 0 ↔ M.tail (e i) ∈ newHole Hs ρ.mverts))
    (hL0 : 1 ≤ L₀)
    (lay : (RECb + 3 * ℓ ≤ LABb ∨ LABb + n ≤ RECb) ∧ (top ≤ LABb ∨ LABb + n ≤ IX0) ∧
      (NHb + n ≤ LABb ∨ LABb + n ≤ NHb) ∧ LABb + n ≤ W ∧ NHb + n ≤ W ∧ top ≤ W ∧
      RECb + 3 * ℓ ≤ W ∧ n + 1 ≤ W ∧ L₀ + ℓ ≤ W)
    (c : Config) (hI : BpInv W M Hs ρ s.1 rs I₀ c₀ n ℓ RECb NHb L₀ LABb e c)
    (ht : c.nreg 4947 < c.nreg 4940) :
    ∃ c' k, Exec P W bpBody c c' k ∧ BpInv W M Hs ρ s.1 rs I₀ c₀ n ℓ RECb NHb L₀ LABb e c' ∧
      c'.nreg 4940 * (7 * n + 40) + k + 2 ≤ c.nreg 4940 * (7 * n + 40) := by
  obtain ⟨wb, r41, r47, r42, r43, r02, kle, r44, rep, fresh, sub, mem, reg, rr, rm, out⟩ := hI
  obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9⟩ := lay
  have hlen : rs.length = ℓ := (scIter_depth ch Hs ℓ s₀ s rs hiter).2
  obtain ⟨chain, -⟩ := scIter_chain ch Hs ℓ s₀ s rs hiter
  obtain ⟨k, hk⟩ : ∃ k, c.nreg 4940 = k + 1 := ⟨c.nreg 4940 - 1, by rw [r47] at ht; omega⟩
  rw [hk] at kle r44 rep fresh sub
  set j := ℓ - (k + 1) with hj
  have hkℓ : k < rs.length := by omega
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hrec k hkℓ
  have hrv : rs.reverse[k]'(by simpa using hkℓ) = rs[j]'(by omega) := by
    rw [List.getElem_reverse]; congr 1; omega
  rw [hrv] at a7 a8
  set o := c₀.nmem (RECb + 3 * k) with ho
  set cnt := c₀.nmem (RECb + 3 * k + 1) with hcnt
  set ai := c₀.nmem (RECb + 3 * k + 2) with hai
  have mrec : ∀ i < 3, c.nmem (RECb + 3 * k + i) = c₀.nmem (RECb + 3 * k + i) := fun i hi =>
    mem _ (by omega)
  have m0 : c.nmem (RECb + 3 * k) = o := by have := mrec 0 (by omega); simpa using this
  have m1 : c.nmem (RECb + 3 * k + 1) = cnt := mrec 1 (by omega)
  have m2 : c.nmem (RECb + 3 * k + 2) = ai := mrec 2 (by omega)
  have mIX : ∀ i < cnt, c.nmem (o + i) = c₀.nmem (o + i) := fun i hi => mem _ (by omega)
  -- 1. the loads
  obtain ⟨c₁, k₁, e₁, hk₁, g40, g01, g00, g04, g05, g03, gn₁, gm₁, gr₁, grm₁, go₁⟩ :=
    bpLoad_exec (P := P) c wb hk r41 r42 r43 r44 (by omega) (by rw [m2]; omega)
  rw [m0] at g01; rw [m1] at g00; rw [m2] at g04 g05
  have g05' : c₁.nreg 4505 = c₀.nmem (NHb + ai) := by rw [g05, mem _ (by omega)]
  have hw₁ := e₁.wb_right
  -- 2. the fill
  obtain ⟨c₂, k₂, e₂, hk₂, F1, F2, F3, F4, F5, F6⟩ := prProg_exec (P := P) c₁ hw₁ (n := n) (s := cnt) (IXb := o) (LABb := LABb) (L := L₀ + j)
    (i₀ := ai) g00 g01 (by rw [gn₁ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)]; exact r02) g03 g04 g05' a1
    (fun i hi => by rw [gm₁, mIX i hi]; exact a6 i hi)
    ⟨by omega, by omega, by omega, by omega⟩
  have hw₂ := e₂.wb_right
  rw [gm₁] at F1
  set lab := fun i => c.nmem (LABb + i) with hlab
  set S := (range cnt).image fun i => c.nmem (o + i) with hS
  have hS' : S = (range cnt).image fun i => c₀.nmem (o + i) := by
    rw [hS]; exact image_congr fun i hi => by rw [mIX i (mem_range.1 (mem_coe.1 hi))]
  have hSsub : S ⊆ range n := fun i hi => by
    rw [hS'] at hi
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hi
    exact mem_range.2 (a6 x (mem_range.1 hx))
  have hSne : S.Nonempty := ⟨_, mem_image_of_mem _ (mem_range.2 a2)⟩
  have hSN : S.image e = rs[j].1 \ rs[j].2.1 := by rw [hS']; exact a8
  obtain ⟨ch1, ch2⟩ := chain j (by omega)
  have hIK : ∀ X ∈ applyPr Hs ρ (rs.take j) I₀, X ⊆ rs[j].2.1 := by
    intro X hX
    have := sub X hX
    rw [ch2]
    unfold nsetF at this
    by_cases hj0 : j = 0
    · simpa [hj0] using this
    · rw [if_neg hj0, List.getElem?_eq_getElem (by omega)] at this
      simpa [hj0] using this
  have key := pruneI_rep (Hs := Hs) (N := rs[j].1) (K := rs[j].2.1) (ρ := ρ) hinj rep
    (itemRep_disjB hinj rep) hIK hSsub hSN hSne a1 (L := L₀ + j) (by omega)
    (fun i hi => Nat.ne_of_lt (fresh i hi)) (c₀.nmem (NHb + ai) ≠ 0) (hNH ai a1)
  rw [← a7] at key
  have happ : applyPr Hs ρ (rs.take (j + 1)) I₀ =
      pruneI Hs rs[j].1 rs[j].2.1 rs[j].2.2 ρ (applyPr Hs ρ (rs.take j) I₀) := by
    rw [take_succ_eq rs (by omega), applyPr_append]
  -- 3. `L += 1`
  obtain ⟨c₃, k₃, e₃, hk₃, h44, hn₃, hm₃, hr₃, hrm₃, ho₃⟩ : ∃ c₃ k₃,
      Exec P W (block [.addN 4944 4944 4941]) c₂ c₃ k₃ ∧ k₃ = 1 ∧
      c₃.nreg 4944 = L₀ + j + 1 ∧ (∀ x, x ≠ 4944 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have q44 : c₂.nreg 4944 = L₀ + j := by
      rw [F3 _ (by omega), gn₁ _ (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega), r44]
    have q41 : c₂.nreg 4941 = 1 := by
      rw [F3 _ (by omega), gn₁ _ (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega), r41]
    exec_block
    all_goals try (config_simp; (try simp only [q44, q41]); omega)
    refine ⟨rfl, by config_simp; simp only [q44, q41], fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
    simp only [Config.nreg_mk, upd_other _ _ _ h1]
  have f₃ : ∀ x, x ≠ 4944 → x ≠ 4940 → x ≠ 4945 → x ≠ 4946 → (x < 4500 ∨ 4511 < x) →
      c₃.nreg x = c.nreg x := fun x h1 h2 h3 h4 h5 => by
    rw [hn₃ x h1, F3 x (by omega), gn₁ x h2 h3 h4 (by omega) (by omega) (by omega) (by omega)
      (by omega)]
  have t40 : c₃.nreg 4940 = k := by
    rw [hn₃ _ (by omega), F3 _ (by omega), g40]
  have hjk : ℓ - k = j + 1 := by omega
  have hlab3 : ∀ i < n, c₃.nmem (LABb + i) = fillL S
      (if c₀.nmem (NHb + ai) ≠ 0 ∨ lab ai = 0 then L₀ + j else lab ai) lab i := fun i hi => by
    rw [hm₃, F1 i hi]
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), ⟨e₃.wb_right,
    by rw [f₃ _ (by omega) (by omega) (by omega) (by omega) (by omega), r41],
    by rw [f₃ _ (by omega) (by omega) (by omega) (by omega) (by omega), r47],
    by rw [f₃ _ (by omega) (by omega) (by omega) (by omega) (by omega), r42],
    by rw [f₃ _ (by omega) (by omega) (by omega) (by omega) (by omega), r43],
    by rw [hn₃ _ (by omega), F3 _ (by omega), gn₁ _ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), r02],
    by rw [t40]; omega, by rw [t40, h44, hjk, Nat.add_assoc], ?_, ?_, ?_, ?_, ?_, by rw [hr₃, F4, gr₁, rr],
    by rw [hrm₃, F5, grm₁, rm], by rw [ho₃, F6, go₁, out]⟩, ?_⟩
  · rw [t40, hjk, happ]
    unfold ItemRep at key ⊢
    rw [key]
    exact labItems_congr fun i hi => (hlab3 i hi).symm
  · intro i hi
    rw [t40, hjk, hlab3 i hi]
    have f1 := fresh i hi
    have f2 := fresh ai a1
    show (if i ∈ S then (if c₀.nmem (NHb + ai) ≠ 0 ∨ c.nmem (LABb + ai) = 0 then L₀ + j
      else c.nmem (LABb + ai)) else c.nmem (LABb + i)) < L₀ + (j + 1)
    split_ifs <;> omega
  · intro X hX
    rw [t40, hjk] at hX ⊢
    rw [happ] at hX
    have := pruneI_sub (Hs := Hs) (a₀ := rs[j].2.2) (ρ := ρ) hIK ch1 X hX
    unfold nsetF
    rw [if_neg (by omega), List.getElem?_eq_getElem (by omega)]
    simpa using this
  · intro a ha
    rw [hm₃, F2 a ha, gm₁, mem a ha]
  · intro x hx
    unfold BpFr at hx
    rw [f₃ x (by omega) (by omega) (by omega) (by omega) (by omega), reg x hx]
  · rw [t40, hk]
    have hcn : 7 * cnt ≤ 7 * n := by omega
    rw [Nat.add_mul, one_mul]
    omega

/-- **The backward pass of `scertD` on the machine**: from the records `rs` of
`scIter ch Hs ℓ s₀ = some (s, rs)` stored as by `slProg` (`RecOK`), items `I₀ ⊆ s.1` on the labels
at `LABb` (labels `< L₀`, `1 ≤ L₀`) and the flags `NH[i] ≠ 0 ↔ tail (e i) ∈ newHole Hs ρ.mverts`,
within `ℓ (7 n + 40) + 6` steps the labels represent `applyPr Hs ρ rs I₀` (the items of
`scertD`, `scertD_iter`), labels `< L₀ + ℓ`; memory outside the labels and the registers `BpFr`
kept. -/
theorem bpProg_exec {ch : ScChoice M} {Hs : List (Finset V)} {ℓ : ℕ} {s₀ s : ScSt D}
    {rs : List (ScRec D)} (hiter : scIter ch Hs ℓ s₀ = some (s, rs)) {ρ : HPath M}
    {I₀ : Finset (Finset D)} {e : ℕ → D} {n RECb NHb L₀ LABb IX0 top : ℕ}
    (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j)
    (c : Config) (hc : WordsBounded W c) (r33 : c.nreg 4933 = ℓ) (r36 : c.nreg 4936 = RECb)
    (r43 : c.nreg 4943 = NHb) (r44 : c.nreg 4944 = L₀) (r02 : c.nreg 4502 = LABb)
    (hrec : RecOK c.nmem RECb IX0 top n e rs)
    (hNH : ∀ i < n, (c.nmem (NHb + i) ≠ 0 ↔ M.tail (e i) ∈ newHole Hs ρ.mverts))
    (hrep : ItemRep e n I₀ fun i => c.nmem (LABb + i)) (hsub : ∀ X ∈ I₀, X ⊆ s.1)
    (hL0 : 1 ≤ L₀) (hfr : ∀ i < n, c.nmem (LABb + i) < L₀)
    (lay : (RECb + 3 * ℓ ≤ LABb ∨ LABb + n ≤ RECb) ∧ (top ≤ LABb ∨ LABb + n ≤ IX0) ∧
      (NHb + n ≤ LABb ∨ LABb + n ≤ NHb) ∧ LABb + n ≤ W ∧ NHb + n ≤ W ∧ top ≤ W ∧
      RECb + 3 * ℓ ≤ W ∧ n + 1 ≤ W ∧ L₀ + ℓ ≤ W) :
    ∃ c' t, Exec P W bpProg c c' t ∧ t ≤ ℓ * (7 * n + 40) + 6 ∧
      ItemRep e n (applyPr Hs ρ rs I₀) (fun i => c'.nmem (LABb + i)) ∧
      (∀ i < n, c'.nmem (LABb + i) < L₀ + ℓ) ∧
      (∀ a, (a < LABb ∨ LABb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, BpFr x → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hlen : rs.length = ℓ := (scIter_depth ch Hs ℓ s₀ s rs hiter).2
  obtain ⟨c₁, k₁, e₁, hk₁, i41, i47, i40, i42, in₁, im₁, ir₁, irm₁, io₁⟩ :=
    bpInit_exec (P := P) c hc (by omega)
  have q44 : c₁.nreg 4944 = L₀ + (ℓ - c₁.nreg 4940) := by
    rw [i40, r33, in₁ _ (by omega) (by omega) (by omega) (by omega), r44, Nat.sub_self,
      Nat.add_zero]
  have hI₁ : BpInv W M Hs ρ s.1 rs I₀ c₁ n ℓ RECb NHb L₀ LABb e c₁ :=
    ⟨e₁.wb_right, i41, i47, by rw [i42, r36], by rw [in₁ _ (by omega) (by omega) (by omega)
      (by omega), r43], by rw [in₁ _ (by omega) (by omega) (by omega) (by omega), r02],
      by rw [i40, r33], q44, by rw [i40, r33, Nat.sub_self, List.take_zero, im₁]; exact hrep,
      fun i hi => by rw [i40, r33, Nat.sub_self, im₁]; simpa using hfr i hi,
      fun X hX => by
        rw [i40, r33, Nat.sub_self, List.take_zero] at hX
        rw [i40, r33, Nat.sub_self]
        unfold nsetF; simpa using hsub X hX,
      fun a _ => rfl, fun x _ => rfl, rfl, rfl, rfl⟩
  rw [← im₁] at hrec hNH
  obtain ⟨c', k₂, e₂, hI', hnt, hk₂⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 4947)
    (b := 4940) (body := bpBody) (BpInv W M Hs ρ s.1 rs I₀ c₁ n ℓ RECb NHb L₀ LABb e)
    (fun c => c.nreg 4940 * (7 * n + 40)) (fun c h => h.wb)
    (fun c h ht => bpBody_step hiter hinj hrec hNH hL0 lay c h ht) hI₁
  obtain ⟨wb, r41', r47', -, -, -, kle, r44', rep, fresh, -, mem, reg, rr, rm, out⟩ := hI'
  have hk0 : c'.nreg 4940 = 0 := by rw [r47'] at hnt; omega
  rw [hk0, Nat.sub_zero, List.take_of_length_le (by omega)] at rep
  rw [hk0, Nat.sub_zero] at fresh
  rw [i40, r33] at hk₂
  refine ⟨c', k₁ + k₂, .seq e₁ e₂, by omega, rep, fresh, fun a ha => by rw [mem a ha, im₁],
    fun x hx => by
      rw [reg x hx]
      unfold BpFr at hx
      exact in₁ x (by omega) (by omega) (by omega) (by omega),
    by rw [rr, ir₁], by rw [rm, irm₁], by rw [out, io₁]⟩

end Pass

end BKMNW

end PlanarFlow
