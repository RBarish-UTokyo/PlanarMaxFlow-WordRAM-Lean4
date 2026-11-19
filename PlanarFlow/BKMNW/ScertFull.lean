module

public import PlanarFlow.BKMNW.CutBase

/-!
# `scertD` as one program, given a program for Miller's base

`scProg mb := slProg ; dispatch`: the level loop (`slProg`), then by the kind of the last level:
kind `0` (`NoCut`, Miller's separator) — the base program `mb` (a parameter with the stated
specification `MbSpec`), then the backward pass `bpProg`; kind `2` (the cut) — `scCut` if the
anchor was found; else failure. The flag `r4970` is `1` exactly when `scertD` returns a
certificate, and then the labels at `ITEMb` represent its items.

* pure: `scStep_rot`, **`scIter_rot`** (the rotation of the state reached is the original one
  or its first return to the darts reached, `ret_ret`);
* **`MbSpec`** (what a program for the base in the `NoCut` case must do: compute
  `scBase ch Hs s` — the items as labels at `ITEMb`, the flags of the new hole of its path at
  `NHb`, a fresh label in `4944`, the registers of `bpProg` — keeping the memory below `ITEMb`
  and the registers `4900`, `4931`, `4933`, `4936`; the path described by a predicate
  `PathOut` stable under `bpProg`);
* `scDisp`, **`scProg`**, **`scProg_exec`**: for the choices `scChoiceE M sepF e n Hs A W₀`
  (`sepF` the separator `mb` computes), `L ≥ scDepth`, the cost
  `(L + 1) (|Hs| (160 n + 36) + 244 n + 110) + Tmb + L (7 n + 40) + 22 n + 40`; the output:
  `r4970 = 0 ∧ scertD … = none`, or `r4970 = 1 ∧ scertD … = some (ρ, I)` with `I` on the labels
  and the path `ρ` given by `PathOut` (kind `0`) or the one vertex `tail (e r4902)` (kind `2`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Relation WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

section Pure

open Equiv Orbit

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

open Classical in
/-- The rotation after a prune is the first return to the kept darts. -/
theorem scStep_rot (ch : ScChoice M) (Hs : List (Finset V)) {s s' : ScSt D} {r : ScRec D}
    (h : scStep ch Hs s = some (s', r)) : s'.2.1 = ret s.2.1 s'.1 ∧ s'.1 ⊆ s.1 := by
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
    exact ⟨rfl, fun d hd => (mem_comp.1 hd).1⟩
  · simp [scStep, hnc, hh, hz, ha, hK] at h

/-- **The rotation of the state reached**: the original one (no prune) or its first return to the
darts reached. -/
theorem scIter_rot (ch : ScChoice M) (Hs : List (Finset V)) :
    ∀ (ℓ : ℕ) (s₀ s : ScSt D) (rs : List (ScRec D)), scIter ch Hs ℓ s₀ = some (s, rs) →
      (s = s₀ ∨ s.2.1 = ret s₀.2.1 s.1) ∧ s.1 ⊆ s₀.1 := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro s₀ s rs h
    simp only [scIter, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Or.inl rfl, subset_rfl⟩
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
        obtain ⟨q1, q2⟩ := scStep_rot ch Hs hs
        refine ⟨Or.inr ?_, c2.trans q2⟩
        rcases c1 with rfl | c1
        · exact q1
        · rw [c1, q1, ret_ret c2]

end Pure

/-! ### The program -/

/-- The dispatch on the kind of the last level. -/
def scDisp (mb : Stmt) : Stmt :=
  .seq (block [.constN 4974 3, .constN 4975 0])
    (.ifLtN 4900 4931 (.seq mb (.ifLtN 4970 4931 .skip bpProg))
      (.ifLtN 4900 4974
        (.ifLtN 4975 4901 (.seq scCut (block [.constN 4970 1])) (block [.constN 4970 0]))
        (block [.constN 4970 0])))

/-- **`scertD` as one program** (given the base program `mb` of the `NoCut` case). -/
def scProg (mb : Stmt) : Stmt := .seq slProg (scDisp mb)

section Full

open Equiv Orbit

variable {P : Input} {W : ℕ}
variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (P W M) in
/-- **The specification of a base program for the `NoCut` case** (Miller's separator): from a
state `s` without cut-vertex holes (its input `LvIn` in memory, rotation `τ` or `ret τ s.1`,
`s.1 ⊆ N₀`, the memory below `b` and the registers `SlFr` as at the start `m₀`, `r₀`), within `T` steps, keeping the memory below `ITEMb` and the registers `4900`, `4931`,
`4933`, `4936`: `r4970 = 0` and `scBase ch Hs s = none`, or `r4970 = 1`,
`scBase ch Hs s = some (ρ, I₀)`, the items `I₀ ⊆ s.1` as labels at `ITEMb` (below the fresh label
`r4944 ∈ [1, n + 2]`), the flags of `newHole Hs ρ.mverts` at `NHb`, `r4943 = NHb`,
`r4502 = ITEMb`, and `PathOut c' ρ`. -/
def MbSpec (ch : ScChoice M) (Hs : List (Finset V)) (τ : Perm D) (N₀ : Finset D) (mb : Stmt)
    (T n b A W₀ ITEMb NHb : ℕ) (e : ℕ → D) (B : Finset D) (m₀ r₀ : ℕ → ℕ)
    (PathOut : Config → HPath M → Prop) : Prop :=
  ∀ (s : ScSt D) (c : Config), WordsBounded W c → LvRegs c n b Hs.length A W₀ →
    LvIn M c.nmem n b e B s.1 Hs s.2.2 → NoCut M s.1 Hs → (s.2.1 = τ ∨ s.2.1 = ret τ s.1) →
    s.1 ⊆ N₀ → c.nreg 4955 = ITEMb → c.nreg 4956 = NHb → (∀ a < b, c.nmem a = m₀ a) →
    (∀ x, SlFr x → (x < 4974 ∨ 4975 < x) → c.nreg x = r₀ x) →
    ∃ c' t, Exec P W mb c c' t ∧ t ≤ T ∧
      (∀ a, a < ITEMb → c'.nmem a = c.nmem a) ∧
      (∀ x, (x = 4900 ∨ x = 4931 ∨ x = 4933 ∨ x = 4936) → c'.nreg x = c.nreg x) ∧
      ((c'.nreg 4970 = 0 ∧ scBase ch Hs s = none) ∨
       (c'.nreg 4970 = 1 ∧ ∃ ρ I₀, scBase ch Hs s = some (ρ, I₀) ∧
         ItemRep e n I₀ (fun i => c'.nmem (ITEMb + i)) ∧ (∀ X ∈ I₀, X ⊆ s.1) ∧
         (∀ i < n, (c'.nmem (NHb + i) ≠ 0 ↔ M.tail (e i) ∈ newHole Hs ρ.mverts)) ∧
         1 ≤ c'.nreg 4944 ∧ c'.nreg 4944 ≤ n + 2 ∧
         (∀ i < n, c'.nmem (ITEMb + i) < c'.nreg 4944) ∧
         c'.nreg 4943 = NHb ∧ c'.nreg 4502 = ITEMb ∧ PathOut c' ρ))

/-- A path description that the backward pass keeps (it writes only the labels and the registers
outside `BpFr`). -/
def PathStable (ITEMb n : ℕ) (PathOut : Config → HPath M → Prop) : Prop :=
  ∀ c c' ρ, PathOut c ρ → (∀ a, (a < ITEMb ∨ ITEMb + n ≤ a) → c'.nmem a = c.nmem a) →
    (∀ x, BpFr x → c'.nreg x = c.nreg x) → c'.rreg = c.rreg → c'.rmem = c.rmem →
    c'.output = c.output → PathOut c' ρ

set_option maxHeartbeats 1600000 in
open Classical in
/-- **`scertD` under `scChoiceE` as one program, given a base program for the `NoCut` case**
(`MbSpec`; `sepF` the separator it computes): within
`(L + 1) (|Hs| (160 n + 36) + 244 n + 110) + Tmb + L (7 n + 40) + 22 n + 40` steps, either
`r4970 = 0` and `scertD … N τ ex = none`, or `r4970 = 1`, `scertD … N τ ex = some (ρ, I)` with the
items `I` represented by the labels at `ITEMb`, and the path `ρ` described by `PathOut` (Miller's
case, `r4900 = 0`) or the one vertex `tail (e r4902)` (the cut, `r4900 = 2`). -/
theorem scProg_exec (sepF : SepFn M) {e : ℕ → D} {B N : Finset D} {Hs : List (Finset V)}
    (hd : Hs.Pairwise Disjoint) {τ : Perm D} {ex : D → ℕ}
    {n b A W₀ RECb IX0 L ITEMb NHb Tmb : ℕ} (mb : Stmt) (PathOut : Config → HPath M → Prop)
    (c : Config)
    (hmb : MbSpec P W M (scChoiceE M sepF e n Hs A W₀) Hs τ N mb Tmb n b A W₀ ITEMb NHb e B
      c.nmem c.nreg PathOut)
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
    obtain ⟨c₃, k₃, e₃, hk₃, Mm, Mr, Mres⟩ := hmb s c₂ hw₂ hR₂ hIn₂ hnc
      (by rcases hrot.1 with h | h
          · left; rw [h]
          · right; exact h) hrot.2 t55 t56 hlow hregs
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
/-- **`MbSpec` is not vacuous**: for the separator that never answers, the one-instruction
program `r4970 := 0` meets it (the base is `none`). A real Miller base program meets it for the
separator it computes. -/
theorem mbSpec_none (e : ℕ → D) (n : ℕ) (Hs : List (Finset V)) (A W₀ : ℕ) (τ : Perm D)
    (N₀ : Finset D) (b ITEMb NHb : ℕ) (B : Finset D) (m₀ r₀ : ℕ → ℕ)
    (PathOut : Config → HPath M → Prop) (hW : 1 ≤ W) :
    MbSpec P W M (scChoiceE M (fun _ _ _ _ _ => none) e n Hs A W₀) Hs τ N₀
      (block [.constN 4970 0]) 1 n b A W₀ ITEMb NHb e B m₀ r₀ PathOut := by
  intro s c hc _ _ hnc _ _ _ _ _ _
  obtain ⟨c', k, ex, hk, h70, hn, hm⟩ : ∃ c' k, Exec P W (block [.constN 4970 0]) c c' k ∧
      k = 1 ∧ c'.nreg 4970 = 0 ∧ (∀ x, x ≠ 4970 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem := by
    exec_block
    all_goals try (config_simp; omega)
    refine ⟨rfl, by config_simp, fun x h1 => ?_, rfl⟩
    simp only [Config.nreg_mk, upd_other _ _ _ h1]
  refine ⟨c', k, ex, by omega, fun a _ => by rw [hm], fun x hx => hn x (by omega),
    Or.inl ⟨h70, ?_⟩⟩
  simp only [scBase, hnc, ↓reduceIte]
  split_ifs <;> rfl

end Full

end BKMNW

end PlanarFlow
