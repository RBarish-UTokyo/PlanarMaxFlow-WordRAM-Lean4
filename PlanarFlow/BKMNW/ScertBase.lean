module

public import PlanarFlow.BKMNW.MbBaseSpec

/-!
# `scertD` as one program from a base meeting `MbSpec'`, and unconditionally for `sepC`

* `findE_idx`, `sum_le_range_e`, **`scStepE_inv`**, **`scIterE_inv`** (along the levels of
  `scertD` with the choices `scChoiceE`, from a piece map: the state stays a nonempty piece map
  `PMap`, the weight `Σ_{s.1} (1 + ex)` is kept, the weight array grows at most to
  `(ℓ + 1) Σ_{j<n} (1 + ex₀ (e j))`);
* **`scProg_exec'`**: `scProg_exec` with the base program meeting `MbSpec'` (satisfiable);
* **`scProg_exec_sepC`**: `scertD` under `scChoiceE M (sepC M e n Bz) e n Hs A W₀` as the one
  program `scProg mbBase`, unconditionally (`mbBase_spec`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Relation WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

section Inv

open Equiv Orbit

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

lemma findE_idx {e : ℕ → D} {n : ℕ} {X : Finset D} {d : D} (h : findE e n X = some d) :
    ∃ i < n, e i = d := by
  unfold findE at h
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨i, List.mem_range.1 (List.mem_of_find?_eq_some hi), rfl⟩

lemma sum_le_range_e {e : ℕ → D} {n : ℕ} (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j)
    {N : Finset D} (hs : ∀ d ∈ N, ∃ i < n, e i = d) (f : D → ℕ) :
    ∑ d ∈ N, f d ≤ ∑ j ∈ range n, f (e j) := by
  have hsub : N ⊆ (range n).image e := fun d hd => by
    obtain ⟨i, hi, rfl⟩ := hs d hd
    exact mem_image.2 ⟨i, mem_range.2 hi, rfl⟩
  rw [← sum_image (s := range n) (g := e) fun i hi j hj h =>
    hinj i (mem_range.1 hi) j (mem_range.1 hj) h]
  exact sum_le_sum_of_subset hsub

open Classical in
/-- **One level of `scertD` with `scChoiceE` keeps a nonempty piece map** and its total weight;
the weight array grows by at most the total weight. -/
theorem scStepE_inv {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) (sepF : SepFn M)
    {e : ℕ → D} {n A W₀ : ℕ} (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j)
    {s s' : ScSt D} {r : ScRec D} (h : scStep (scChoiceE M sepF e n Hs A W₀) Hs s = some (s', r))
    (hN : PMap M s.1 Hs s.2.1) (hne : s.1.Nonempty) (hs : ∀ d ∈ s.1, ∃ i < n, e i = d) :
    PMap M s'.1 Hs s'.2.1 ∧ s'.1.Nonempty ∧ s'.1 ⊆ s.1 ∧
      ∑ d ∈ s'.1, (1 + s'.2.2 d) = ∑ d ∈ s.1, (1 + s.2.2 d) ∧
      ∑ j ∈ range n, (1 + s'.2.2 (e j)) ≤
        ∑ j ∈ range n, (1 + s.2.2 (e j)) + ∑ d ∈ s.1, (1 + s.2.2 d) := by
  obtain ⟨N, τ, ex⟩ := s
  dsimp only at hN hne hs ⊢
  set ch := scChoiceE M sepF e n Hs A W₀ with hch
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
    obtain ⟨rfl, -⟩ := h
    dsimp only
    have hg : g ∈ Hs := List.mem_of_find?_eq_some hh
    have hzN : z ∈ N := (mem_filter.1 (findE_some hz)).1
    have ha₀ : a₀ ∈ comp M N Hs g z := (mem_filter.1 (findE_some ha)).1
    obtain ⟨a, haN, rfl⟩ := findE_idx ha
    set K := comp M N Hs g z with hKdef
    have hKN : K ⊆ N := fun d hd => (mem_comp.1 hd).1
    have hgc := hClosed_of_mem hd hg
    have hKr : Stable (revPerm M) K := fun d hd => comp_rev hN.rev hd
    have hKp : PMap M K Hs (ret τ K) := PMap.del hd hN hg hKN hKr
      (fun a ha b hab => comp_closed ha hab) (comp_conn hgc hzN)
    refine ⟨hKp, ⟨z, self_mem_comp hzN⟩, hKN, sum_exP ha₀ hKN, ?_⟩
    have h5 := sum_range_exP hinj haN N K ex
    simp only [exP] at h5
    have : ∑ d ∈ N \ K, (1 + ex d) ≤ ∑ d ∈ N, (1 + ex d) := sum_le_sum_of_subset sdiff_subset
    omega
  · simp [scStep, hnc, hh, hz, ha, hK] at h

open Classical in
/-- **Along the levels of `scertD` with `scChoiceE`** from a nonempty piece map. -/
theorem scIterE_inv {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) (sepF : SepFn M)
    {e : ℕ → D} {n A W₀ : ℕ} (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j) :
    ∀ (ℓ : ℕ) (s₀ s : ScSt D) (rs : List (ScRec D)),
      scIter (scChoiceE M sepF e n Hs A W₀) Hs ℓ s₀ = some (s, rs) →
      PMap M s₀.1 Hs s₀.2.1 → s₀.1.Nonempty → (∀ d ∈ s₀.1, ∃ i < n, e i = d) →
      PMap M s.1 Hs s.2.1 ∧ s.1.Nonempty ∧
        ∑ d ∈ s.1, (1 + s.2.2 d) = ∑ d ∈ s₀.1, (1 + s₀.2.2 d) ∧
        ∑ j ∈ range n, (1 + s.2.2 (e j)) ≤
          ∑ j ∈ range n, (1 + s₀.2.2 (e j)) + ℓ * ∑ d ∈ s₀.1, (1 + s₀.2.2 d) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro s₀ s rs h hN hne _
    simp only [scIter, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hN, hne, rfl, by simp⟩
  | succ ℓ ih =>
    intro s₀ s rs h hN hne hs
    rw [scIter] at h
    cases hst : scStep (scChoiceE M sepF e n Hs A W₀) Hs s₀ with
    | none => rw [hst] at h; exact absurd h (by simp)
    | some p =>
      obtain ⟨s₁, r₀⟩ := p
      rw [hst] at h
      simp only at h
      cases h1 : scIter (scChoiceE M sepF e n Hs A W₀) Hs ℓ s₁ with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some q =>
        obtain ⟨s₂, rs'⟩ := q
        rw [h1] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨p1, p2, p3, p4, p5⟩ := scStepE_inv hd sepF hinj hst hN hne hs
        obtain ⟨q1, q2, q3, q4⟩ := ih s₁ s₂ rs' h1 p1 p2 fun d hd => hs d (p3 hd)
        refine ⟨q1, q2, q3.trans p4, ?_⟩
        rw [p4] at q4
        rw [add_mul, one_mul]
        omega

end Inv

section Full

open Equiv Orbit

variable {P : Input} {W : ℕ}
variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

set_option maxHeartbeats 1600000 in
open Classical in
/-- **`scertD` under `scChoiceE` as one program, given a base program meeting `MbSpec'`**
(the revised base spec; from a piece map `PMap M N Hs τ`, `N` nonempty, `Σ_N (1 + ex) ≤ T₀`; `sepF` the separator it computes): within
`(L + 1) (|Hs| (160 n + 36) + 244 n + 110) + Tmb + L (7 n + 40) + 22 n + 40` steps, either
`r4970 = 0` and `scertD … N τ ex = none`, or `r4970 = 1`, `scertD … N τ ex = some (ρ, I)` with the
items `I` represented by the labels at `ITEMb`, and the path `ρ` described by `PathOut` (Miller's
case, `r4900 = 0`) or the one vertex `tail (e r4902)` (the cut, `r4900 = 2`). -/
theorem scProg_exec' (sepF : SepFn M) {e : ℕ → D} {B N : Finset D} {Hs : List (Finset V)}
    (hd : Hs.Pairwise Disjoint) {τ : Perm D} {ex : D → ℕ}
    {n b A W₀ RECb IX0 L ITEMb NHb Tmb : ℕ} (mb : Stmt) (PathOut : Config → HPath M → Prop)
    (c : Config)
    {T₀ : ℕ} (hmb : MbSpec' P W M (scChoiceE M sepF e n Hs A W₀) Hs τ N mb Tmb n b A W₀ ITEMb NHb
      T₀ e B c.nmem c.nreg PathOut)
    (hPN : PMap M N Hs τ) (hNne : N.Nonempty) (hT₀ : ∑ d ∈ N, (1 + ex d) ≤ T₀)
    (hPO : PathStable ITEMb n PathOut) (hc : WordsBounded W c) (hR : LvRegs c n b Hs.length A W₀)
    (hI : LvIn M c.nmem n b e B N Hs ex) (r36 : c.nreg 4936 = RECb) (r37 : c.nreg 4937 = IX0)
    (r55 : c.nreg 4955 = ITEMb) (r56 : c.nreg 4956 = NHb)
    (hHW : Hs.length + 1 ≤ W)
    (hL : scDepth (scChoiceE M sepF e n Hs A W₀) Hs N τ ex ≤ L)
    (lay : b + 20 * n + 3 ≤ RECb ∧ RECb + 3 * L ≤ IX0 ∧ IX0 + L * n + n + 1 ≤ ITEMb ∧
      ITEMb + n ≤ NHb ∧ NHb + n ≤ W ∧ n + 2 + L ≤ W)
    (hS : A + 2 * ((L + 1) * ∑ j ∈ range n, (1 + c.nmem (b + 3 * n + j))) ≤ W) :
    ∃ c' t, Exec P W (scProg mb) c c' t ∧
      t ≤ (L + 1) * (Hs.length * (160 * n + 36) + 244 * n + 110) + Tmb + L * (7 * n + 40) +
        22 * n + 40 ∧
      ((c'.nreg 4970 = 0 ∧ scertD (scChoiceE M sepF e n Hs A W₀) Hs N τ ex = none) ∨
       (c'.nreg 4970 = 1 ∧ ∃ ρ I, scertD (scChoiceE M sepF e n Hs A W₀) Hs N τ ex = some (ρ, I) ∧
         ItemRep e n I (fun i => c'.nmem (ITEMb + i)) ∧
         ((c'.nreg 4900 = 0 ∧ PathOut c' ρ) ∨
          (c'.nreg 4900 = 2 ∧ c'.nreg 4902 < n ∧
            ρ = (SPath.point (M' := M) (e (c'.nreg 4902)) (M.tail (e (c'.nreg 4902)))).toH)))) := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := lay
  have hLn : L * n + n + 1 ≤ W := by omega
  obtain ⟨c₁, k₁, e₁, hk₁, ℓ, s, rs, iter, hst, hscert, hℓ, hlen, r33, hk1, hIn, hLO, hLAB, o1, o2,
    recs, hR₁, r36₁, r31, mem₁, reg₁, -, -, -⟩ :=
    slProg_exec (P := P) sepF hd c hc hR hI r36 r37 hHW hL ⟨l1, l2, by omega⟩ hS
  have hw₁ := e₁.wb_right
  have hℓn : ℓ * n ≤ L * n := Nat.mul_le_mul_right n hℓ
  have hℓc : ℓ * (7 * n + 40) ≤ L * (7 * n + 40) := Nat.mul_le_mul_right _ hℓ
  set ch := scChoiceE M sepF e n Hs A W₀ with hch
  have r55₁ : c₁.nreg 4955 = ITEMb := by rw [reg₁ _ (by unfold SlFr LvFr; omega), r55]
  have r56₁ : c₁.nreg 4956 = NHb := by rw [reg₁ _ (by unfold SlFr LvFr; omega), r56]
  -- the constants
  obtain ⟨c₂, k₂, e₂, hk₂, g74, g75, gn₂, gm₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
      Exec P W (block [.constN 4974 3, .constN 4975 0]) c₁ c₂ k₂ ∧ k₂ = 2 ∧
      c₂.nreg 4974 = 3 ∧ c₂.nreg 4975 = 0 ∧
      (∀ x, x ≠ 4974 → x ≠ 4975 → c₂.nreg x = c₁.nreg x) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    exec_block
    all_goals try (config_simp; omega)
    refine ⟨rfl, by config_simp, by config_simp, fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    simp only [Config.nreg_mk, upd_other _ _ _ h1, upd_other _ _ _ h2]
  have hw₂ := e₂.wb_right
  have hR₂ : LvRegs c₂ n b Hs.length A W₀ := hR₁.of_frame' fun x _ hx => gn₂ x (by omega) (by omega)
  have hIn₂ : LvIn M c₂.nmem n b e B s.1 Hs s.2.2 := by rw [gm₂]; exact hIn
  have t00 : c₂.nreg 4900 = c₁.nreg 4900 := gn₂ _ (by omega) (by omega)
  have t01 : c₂.nreg 4901 = c₁.nreg 4901 := gn₂ _ (by omega) (by omega)
  have t02 : c₂.nreg 4902 = c₁.nreg 4902 := gn₂ _ (by omega) (by omega)
  have t31 : c₂.nreg 4931 = 1 := by rw [gn₂ _ (by omega) (by omega), r31]
  have t33 : c₂.nreg 4933 = ℓ := by rw [gn₂ _ (by omega) (by omega), r33]
  have t36 : c₂.nreg 4936 = RECb := by rw [gn₂ _ (by omega) (by omega), r36₁]
  have t55 : c₂.nreg 4955 = ITEMb := by rw [gn₂ _ (by omega) (by omega), r55₁]
  have t56 : c₂.nreg 4956 = NHb := by rw [gn₂ _ (by omega) (by omega), r56₁]
  have hrec₂ : RecOK c₂.nmem RECb IX0 (c₁.nreg 4932) n e rs := by rw [gm₂]; exact recs
  have hrot := scIter_rot ch Hs ℓ (N, τ, ex) s rs iter
  have hcost0 : k₁ ≤ (L + 1) * (Hs.length * (160 * n + 36) + 244 * n + 110) + 6 := hk₁
  rcases hLO with ⟨k0, hnc, -, -⟩ | ⟨k1', -⟩ | ⟨k2, -, g, hlabN, ha₁, hbase, -, -⟩ |
      ⟨k3, -, hbase, -, -⟩
  · -- Miller's case
    have hlow : ∀ a < b, c₂.nmem a = c.nmem a := fun a ha => by
      rw [gm₂, mem₁ a (by unfold SlKept; omega)]
    have hregs : ∀ x, SlFr x → (x < 4974 ∨ 4975 < x) → c₂.nreg x = c.nreg x := fun x hx h =>
      by rw [gn₂ x (by omega) (by omega), reg₁ x hx]
    have hlt : c₂.nreg 4900 < c₂.nreg 4931 := by rw [t00, k0, t31]; omega
    obtain ⟨sP, sne, ssum, sEX⟩ := scIterE_inv hd sepF hI.inj ℓ (N, τ, ex) s rs iter hPN hNne
      (fun d hd => hI.surj d (hI.sub hd))
    have hEXW : ∑ j ∈ range n, c₂.nmem (b + 3 * n + j) ≤ W := by
      have h1 : ∑ j ∈ range n, c₂.nmem (b + 3 * n + j) ≤ ∑ j ∈ range n, (1 + s.2.2 (e j)) :=
        sum_le_sum fun j hj => by rw [hIn₂.ex j (mem_range.1 hj)]; omega
      have h2 : ∑ j ∈ range n, (1 + ex (e j)) = ∑ j ∈ range n, (1 + c.nmem (b + 3 * n + j)) :=
        sum_congr rfl fun j hj => by rw [hI.ex j (mem_range.1 hj)]
      have hle := sum_le_range_e hI.inj (fun d hd => hI.surj d (hI.sub hd)) (fun d => 1 + ex d)
      dsimp only at sEX hle
      set T := ∑ j ∈ range n, (1 + ex (e j)) with hT
      have h3 : ℓ * ∑ d ∈ N, (1 + ex d) ≤ L * T :=
        (Nat.mul_le_mul_left ℓ hle).trans (Nat.mul_le_mul_right T hℓ)
      have h4 : (L + 1) * T = L * T + T := by rw [add_mul, one_mul]
      rw [← h2] at hS
      omega
    obtain ⟨c₃, k₃, e₃, hk₃, Mm, Mr, Mres⟩ := hmb s c₂ hw₂ hR₂ hIn₂ hnc sP sne
      (by rcases hrot.1 with h | h
          · rw [h]; intro x hx; exact (ret_eq_self_of hx (hPN.stable x hx)).symm
          · rw [h]; intro x _; rfl) hrot.2 (by rw [ssum]; exact hT₀) hEXW t55 t56 hlow hregs
    have hw₃ := e₃.wb_right
    have u31 : c₃.nreg 4931 = 1 := by rw [Mr _ (by omega), t31]
    rcases Mres with ⟨f0, hb0⟩ | ⟨f1, ρ, I₀, hb1, hrep, hsub, hNH, hL1, hL2, hfr, h43, h02, hpath⟩
    · have hlt' : c₃.nreg 4970 < c₃.nreg 4931 := by rw [f0, u31]; omega
      refine ⟨c₃, k₁ + (k₂ + ((k₃ + (0 + 1)) + 1)), .seq e₁ (.seq e₂ (.ifLtN_true hlt
        (.seq e₃ (.ifLtN_true hlt' (.skip hw₃))))), by omega, Or.inl ⟨f0, ?_⟩⟩
      rw [hscert, hb0]; rfl
    · have hnlt' : ¬ c₃.nreg 4970 < c₃.nreg 4931 := by rw [f1, u31]; omega
      have hrec₃ : RecOK c₃.nmem RECb IX0 (c₁.nreg 4932) n e rs :=
        hrec₂.congr le_rfl (fun a h1 h2 => Mm a (by omega)) (fun a h1 h2 => Mm a (by omega))
      obtain ⟨c₄, k₄, e₄, hk₄, B1, -, B3, B4, B5, B6, B7⟩ := bpProg_exec (P := P) iter
        (ρ := ρ) hI.inj c₃ hw₃ (by rw [Mr _ (by omega), t33]) (by rw [Mr _ (by omega), t36])
        h43 rfl h02 hrec₃ hNH hrep hsub hL1 hfr
        ⟨Or.inl (by omega), Or.inl (by omega), Or.inr l4, by omega, l5, by omega, by omega,
          by omega, by omega⟩
      refine ⟨c₄, k₁ + (k₂ + (k₃ + (k₄ + 2) + 1)), .seq e₁ (.seq e₂ (.ifLtN_true hlt
        (.seq e₃ (.ifLtN_false hnlt' e₄)))), by omega, Or.inr ⟨by rw [B4 _ (by unfold BpFr; omega), f1],
          ρ, applyPr Hs ρ rs I₀, by rw [hscert, hb1]; rfl, B1, Or.inl ⟨?_, ?_⟩⟩⟩
      · rw [B4 _ (by unfold BpFr; omega), Mr _ (by omega), t00, k0]
      · exact hPO c₃ c₄ ρ hpath B3 B4 B5 B6 B7
  · exact absurd k1' hk1
  · -- the cut
    have hnlt : ¬ c₂.nreg 4900 < c₂.nreg 4931 := by rw [t00, k2, t31]; omega
    have hlt3 : c₂.nreg 4900 < c₂.nreg 4974 := by rw [t00, k2, g74]; omega
    by_cases hf : c₁.nreg 4901 = 0
    · have hnlt5 : ¬ c₂.nreg 4975 < c₂.nreg 4901 := by rw [g75, t01, hf]; omega
      obtain ⟨c₃, k₃, e₃, hk₃, f0, -⟩ : ∃ c₃ k₃, Exec P W (block [.constN 4970 0]) c₂ c₃ k₃ ∧
          k₃ = 1 ∧ c₃.nreg 4970 = 0 ∧ True := by
        exec_block
        all_goals try (config_simp; omega)
        exact ⟨rfl, by config_simp, trivial⟩
      refine ⟨c₃, k₁ + (k₂ + (k₃ + 2 + 1 + 2)), .seq e₁ (.seq e₂ (.ifLtN_false hnlt
        (.ifLtN_true hlt3 (.ifLtN_false hnlt5 e₃)))), by omega, Or.inl ⟨f0, ?_⟩⟩
      rw [hscert, hbase, if_pos hf]; rfl
    · have hlt5 : c₂.nreg 4975 < c₂.nreg 4901 := by rw [g75, t01]; omega
      have ha : c₁.nreg 4902 < n := ha₁ hf
      obtain ⟨c₃, k₃, e₃, hk₃, C1, -, Cn, Cr, Crm, Co⟩ := scCut_exec (P := P) iter (g := g) c₂ hw₂ hR₂
        hIn₂ t02 ha (fun i hi j hj hiN => by rw [gm₂]; exact hlabN i hi j hj hiN)
        (fun i hi => by rw [gm₂]; exact hLAB k2 i hi) t33 t36 t55 t56 hrec₂
        ⟨by omega, l4, l5, Or.inl (by omega), Or.inl (by omega), by omega, by omega, by omega⟩
      have hw₃ := e₃.wb_right
      obtain ⟨c₄, k₄, e₄, hk₄, f1, fn, fm⟩ : ∃ c₄ k₄, Exec P W (block [.constN 4970 1]) c₃ c₄ k₄ ∧
          k₄ = 1 ∧ c₄.nreg 4970 = 1 ∧ (∀ x, x ≠ 4970 → c₄.nreg x = c₃.nreg x) ∧
          c₄.nmem = c₃.nmem := by
        exec_block
        all_goals try (config_simp; omega)
        refine ⟨rfl, by config_simp, fun x h1 => ?_, rfl⟩
        simp only [Config.nreg_mk, upd_other _ _ _ h1]
      have v00 : c₄.nreg 4900 = 2 := by rw [fn _ (by omega), Cn _ (by omega), t00, k2]
      have v02 : c₄.nreg 4902 = c₁.nreg 4902 := by rw [fn _ (by omega), Cn _ (by omega), t02]
      refine ⟨c₄, k₁ + (k₂ + ((k₃ + k₄) + 1 + 1 + 2)), .seq e₁ (.seq e₂ (.ifLtN_false hnlt
        (.ifLtN_true hlt3 (.ifLtN_true hlt5 (.seq e₃ e₄))))), by omega, Or.inr ⟨f1,
          (cutCert M Hs s.1 g (e (c₁.nreg 4902))).1, _, ?_, by rw [fm]; exact C1,
          Or.inr ⟨v00, by rw [v02]; exact ha, by rw [v02]; rfl⟩⟩⟩
      rw [hscert, hbase, if_neg hf]; rfl
  · -- failure
    have hnlt : ¬ c₂.nreg 4900 < c₂.nreg 4931 := by rw [t00, k3, t31]; omega
    have hnlt3 : ¬ c₂.nreg 4900 < c₂.nreg 4974 := by rw [t00, k3, g74]; omega
    obtain ⟨c₃, k₃, e₃, hk₃, f0, -⟩ : ∃ c₃ k₃, Exec P W (block [.constN 4970 0]) c₂ c₃ k₃ ∧
        k₃ = 1 ∧ c₃.nreg 4970 = 0 ∧ True := by
      exec_block
      all_goals try (config_simp; omega)
      exact ⟨rfl, by config_simp, trivial⟩
    refine ⟨c₃, k₁ + (k₂ + (k₃ + 2 + 2)), .seq e₁ (.seq e₂ (.ifLtN_false hnlt
      (.ifLtN_false hnlt3 e₃))), by omega, Or.inl ⟨f0, ?_⟩⟩
    rw [hscert, hbase]; rfl


open Classical in
/-- **`scertD` under the choices `scChoiceE` with Miller's separator `sepC` (the one the machine
computes), as one program `scProg mbBase`, unconditionally.** From a piece map `PMap M N Hs τ`
(`N` nonempty, `Σ_N (1 + ex) ≤ T₀`) on a loopless map, the level input `LvIn` at `b`, the
rotation array of `τ` (stable on the enumerated darts `B`) at `SGb` below `b`, the base registers
`5200 … 5203 = SGb, Hb, Bz, SVb` (`encB' n ≤ Bz`), within
`(L + 1) (|Hs| (160 n + 36) + 244 n + 110) + mbT n Bz T₀ + L (7 n + 40) + 22 n + 40` steps
(`mbT n Bz T₀ = 19 (Bz + 25 n + 3 T₀ + 15) + encT n + msT n (2 n) + 237 n + 1223`): either
`r4970 = 0` and `scertD … = none`, or `r4970 = 1`, `scertD … = some (ρ, I)` with the items `I` on
the labels at `ITEMb`, and (Miller's case, `r4900 = 0`) the flags of the new hole of `ρ` at
`NHb`, or (the cut, `r4900 = 2`) `ρ` the one vertex `tail (e r4902)`. -/
theorem scProg_exec_sepC (hloopM : ∀ d, M.head d ≠ M.tail d) {e : ℕ → D} {B N : Finset D}
    {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {τ : Perm D} {ex : D → ℕ}
    {n b A W₀ RECb IX0 L ITEMb NHb T₀ SGb Hb Bz SVb : ℕ} (c : Config)
    (hPN : PMap M N Hs τ) (hNne : N.Nonempty) (hT₀ : ∑ d ∈ N, (1 + ex d) ≤ T₀)
    (hc : WordsBounded W c) (hR : LvRegs c n b Hs.length A W₀)
    (hI : LvIn M c.nmem n b e B N Hs ex) (r36 : c.nreg 4936 = RECb) (r37 : c.nreg 4937 = IX0)
    (r55 : c.nreg 4955 = ITEMb) (r56 : c.nreg 4956 = NHb)
    (s0 : c.nreg 5200 = SGb) (s1 : c.nreg 5201 = Hb) (s2 : c.nreg 5202 = Bz)
    (s3 : c.nreg 5203 = SVb)
    (hSG : ∀ i < n, c.nmem (SGb + i) < n ∧ e (c.nmem (SGb + i)) = τ (e i)) (hτB : Stable τ B)
    (hBz : encB' n ≤ Bz) (hHW : Hs.length + 1 ≤ W)
    (hL : scDepth (scChoiceE M (sepC M e n Bz) e n Hs A W₀) Hs N τ ex ≤ L)
    (lay : b + 20 * n + 3 ≤ RECb ∧ RECb + 3 * L ≤ IX0 ∧ IX0 + L * n + n + 1 ≤ ITEMb ∧
      ITEMb + n ≤ NHb ∧ n + 2 + L ≤ W ∧ SGb + n ≤ b ∧ NHb + n ≤ Hb ∧
      Bz + 25 * n + 3 * T₀ + 15 ≤ Hb ∧ Hb + 13 * n ≤ SVb ∧ SVb + Bz + 25 * n + 3 * T₀ + 16 ≤ W)
    (hS : A + 2 * ((L + 1) * ∑ j ∈ range n, (1 + c.nmem (b + 3 * n + j))) ≤ W) :
    ∃ c' t, Exec P W (scProg mbBase) c c' t ∧
      t ≤ (L + 1) * (Hs.length * (160 * n + 36) + 244 * n + 110) + mbT n Bz T₀ +
        L * (7 * n + 40) + 22 * n + 40 ∧
      ((c'.nreg 4970 = 0 ∧ scertD (scChoiceE M (sepC M e n Bz) e n Hs A W₀) Hs N τ ex = none) ∨
       (c'.nreg 4970 = 1 ∧ ∃ ρ I,
         scertD (scChoiceE M (sepC M e n Bz) e n Hs A W₀) Hs N τ ex = some (ρ, I) ∧
         ItemRep e n I (fun i => c'.nmem (ITEMb + i)) ∧
         ((c'.nreg 4900 = 0 ∧ PathNH M e n NHb Hs c' ρ) ∨
          (c'.nreg 4900 = 2 ∧ c'.nreg 4902 < n ∧
            ρ = (SPath.point (M' := M) (e (c'.nreg 4902)) (M.tail (e (c'.nreg 4902)))).toH)))) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := lay
  have hL1 : L * n + n + 1 ≤ ITEMb := by omega
  exact scProg_exec' (P := P) (W := W) (sepC M e n Bz) hd mbBase (PathNH M e n NHb Hs) c
    (mbBase_spec (P := P) (W := W) hloopM hd e n Bz τ N B c.nmem c.nreg s0 s1 s2 s3 hSG hτB hBz
      ⟨l6, by omega, l4, l7, l8, l9, l10⟩)
    hPN hNne hT₀ (pathStable_NH l4) hc hR hI r36 r37 r55 r56 hHW hL
    ⟨l1, l2, l3, l4, by omega, l5⟩ hS

end Full

end BKMNW

end PlanarFlow
