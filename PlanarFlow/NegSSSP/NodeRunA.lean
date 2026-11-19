module

public import PlanarFlow.BKMNW.FRDijNum
public import PlanarFlow.Monge.FRReloc

/-!
# Pieces of the run of a node: clearing, copying, Dijkstra inside a larger configuration

The composition of the runs of a node (`PlanarFlow/NegSSSP/NodeRun.lean`) runs FR-Dijkstra in
the low memory of a configuration holding the node above. This file has the pieces it needs:

* `zeroRegs_exec`: the block clearing a list of registers.
* `clrProg_exec`: the loop clearing the natural memory below a bound (`r900`), so that the
  memory of a run of FR-Dijkstra is bounded by its word bound.
* `cpyProg_exec`: the loop copying `r910` natural and real cells (the heads and the lengths of
  the explicit arcs, from the counting sort to the layout of `mkPrm`).
* `csList_congr`, `length_arcList_csList`: the list of the counting sort depends only on the
  kept lengths; all its arcs are laid out when the tails are below `N`.
* `dijk_exec_emb`: the calls of Dijkstra of a step (`NegSSSP.dijk_exec_num`) **inside a larger
  configuration**, by `WordRAM.Machine.Exec.lift_trunc`: the registers `≥ 372` and the memory
  above the word bound of the layout are kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge Monge.FR BKMNW

variable {P : Input} {W : ℕ}

open Lean Elab Tactic Meta in
/-- Clear every hypothesis that mentions a machine configuration or is an implication. -/
elab "pclear" : tactic => do
  liftMetaTactic fun g => do
    let g' ← g.withContext do
      let mut fvs : Array FVarId := #[]
      for d in (← getLCtx) do
        if d.isImplementationDetail then continue
        let t ← instantiateMVars d.type
        if (← isProp t) then
          let bad := t.foldConsts false fun c b => b || c.components.contains `Config
          if bad || t.isForall then fvs := fvs.push d.fvarId
      g.tryClearMany fvs
    return [g']

/-- `omega` after `pclear` (keeps the arithmetic context of a long composition small). -/
macro "pomega" : tactic => `(tactic| (pclear; omega))

/-! ### Clearing registers -/

/-- The block clearing the registers of `l`. -/
def zeroRegs (l : List ℕ) : Stmt := block (l.map fun r => .constN r 0)

theorem zeroRegs_exec (l : List ℕ) (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W (zeroRegs l) c c' k ∧ k = l.length ∧
      (∀ r, c'.nreg r = if r ∈ l then 0 else c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  induction l generalizing c with
  | nil => exact ⟨c, 0, Exec.block_nil hc, rfl, fun r => by simp, rfl, rfl, rfl, rfl⟩
  | cons r₀ l ih =>
    have e₁ := Exec.constN (P := P) hc r₀ 0 (Nat.zero_le _)
    obtain ⟨c', k, e, hk, hn, hr, hm, hrm, ho⟩ := ih _ e₁.wb_right
    refine ⟨c', k + 1, Exec.block_cons e₁ e, by simp [hk], fun r => ?_, hr, hm, hrm, ho⟩
    rw [hn r]
    by_cases h1 : r ∈ l
    · simp [h1]
    · by_cases h2 : r = r₀
      · subst h2; simp [h1]
      · simp [h1, h2]

/-- The registers `< 372`, those of `frProg`. -/
def lowRegs : List ℕ := List.range 372

theorem mem_lowRegs {r : ℕ} : r ∈ lowRegs ↔ r < 372 := by simp [lowRegs]

/-! ### Clearing the natural memory below a bound -/

/-- `nmem[r901] := 0` for `r901 < r900`. -/
def clrProg : Stmt :=
  .seq (block [.constN 902 1, .constN 903 0, .constN 901 0])
    (.whileLtN 901 900 (block [.storeN 901 903, .addN 901 901 902]))

theorem clrProg_exec {L : ℕ} (hL : L + 1 ≤ W) (c : Config) (hc : WordsBounded W c)
    (h900 : c.nreg 900 = L) :
    ∃ c' k, Exec P W clrProg c c' k ∧ k ≤ 4 * L + 5 ∧
      (∀ a < L, c'.nmem a = 0) ∧ (∀ a, L ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 901 ∨ 903 < r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold clrProg
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ a < i, c'.nmem a = 0) ∧ (∀ a, i ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 901 ∨ 903 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 902 = 1 ∧ c'.nreg 903 = 0 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 901) (bR := 900) J (K := 2) (n := L) _ ‹_›
    (by config_simp) (by config_simp; exact h900) ⟨fun a ha => absurd ha (by omega),
      fun a _ => rfl, fun r hr => (by
        config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl),
      by config_simp, by config_simp, rfl, rfl, rfl⟩
    (fun i c₁ hi hw ha hb ⟨g0, gk, gn, g2, g3, gr, grm, go⟩ => by
      exec_block
      all_goals try ((try config_simp); (try simp only [ha, g2]); omega)
      dsimp only [J]
      config_simp
      simp only [ha, g2, g3]
      refine ⟨by omega, trivial, hb, fun a ha' => ?_,
        fun a ha' => ?_, fun r hr => ?_, trivial, trivial, gr, grm, go⟩
      · simp only [upd_apply]
        split_ifs with h
        · rfl
        · exact g0 a (by omega)
      · simp only [upd_apply]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact gk a (by omega)
      · simp only [upd_apply]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact gn r hr)) ?_
  rintro c₂ k₂ hk₂ - ⟨-, g0, gk, gn, -, -, gr, grm, go⟩
  refine ⟨by omega, g0, gk, fun r hr => ?_, gr, grm, ?_⟩
  · rw [gn r hr]; try (config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl)
  · rw [go]

/-! ### Copying natural and real cells -/

/-- For `e = r915 < r910`: `nmem[r911 + e] := nmem[r912 + e]`,
`rmem[r913 + e] := rmem[r914 + e]`. -/
def cpyBody : Stmt :=
  block [.addN 917 912 915, .loadN 918 917, .addN 917 911 915, .storeN 917 918,
    .addN 917 914 915, .loadR 910 917, .addN 917 913 915, .storeR 917 910, .addN 915 915 916]

/-- **The copy of `r910` natural and real cells.** -/
def cpyProg : Stmt :=
  .seq (block [.constN 916 1, .constN 915 0]) (.whileLtN 915 910 cpyBody)

/-- The layout of `cpyProg`: the regions written apart from the regions read. -/
structure CpyLay (n Dn Sn Dr Sr W : ℕ) : Prop where
  dn : Dn + n ≤ Sn ∨ Sn + n ≤ Dn
  dr : Dr + n ≤ Sr ∨ Sr + n ≤ Dr
  wDn : Dn + n ≤ W
  wSn : Sn + n ≤ W
  wDr : Dr + n ≤ W
  wSr : Sr + n ≤ W
  wn : n + 1 ≤ W

theorem cpyProg_exec {n Dn Sn Dr Sr : ℕ} (hL : CpyLay n Dn Sn Dr Sr W) (c : Config)
    (hc : WordsBounded W c) (h910 : c.nreg 910 = n) (h911 : c.nreg 911 = Dn)
    (h912 : c.nreg 912 = Sn) (h913 : c.nreg 913 = Dr) (h914 : c.nreg 914 = Sr) :
    ∃ c' k, Exec P W cpyProg c c' k ∧ k ≤ 11 * n + 4 ∧
      (∀ e < n, c'.nmem (Dn + e) = c.nmem (Sn + e) ∧ c'.rmem (Dr + e) = c.rmem (Sr + e)) ∧
      (∀ a, (a < Dn ∨ Dn + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, (a < Dr ∨ Dr + n ≤ a) → c'.rmem a = c.rmem a) ∧
      (∀ r, r < 915 ∨ 918 < r → c'.nreg r = c.nreg r) ∧
      (∀ r, r ≠ 910 → c'.rreg r = c.rreg r) ∧ c'.output = c.output := by
  have := hL.dn; have := hL.dr; have := hL.wDn; have := hL.wSn; have := hL.wDr; have := hL.wSr
  have := hL.wn
  unfold cpyProg
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ e < i, c'.nmem (Dn + e) = c.nmem (Sn + e) ∧ c'.rmem (Dr + e) = c.rmem (Sr + e)) ∧
      (∀ a, (a < Dn ∨ Dn + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, (a < Dr ∨ Dr + i ≤ a) → c'.rmem a = c.rmem a) ∧
      (∀ r, r < 915 ∨ 918 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 916 = 1 ∧
      (∀ r, r ≠ 910 → c'.rreg r = c.rreg r) ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 915) (bR := 910) J (K := 9) (n := n) _ ‹_›
    (by config_simp) (by config_simp; exact h910) ⟨fun e he => absurd he (by omega),
      fun a _ => rfl, fun a _ => rfl, fun r hr => (by
        config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl),
      by config_simp, fun _ _ => rfl, rfl⟩
    (fun i c₁ hi hw ha hb ⟨g, gm, grm, gn, g916, gr, go⟩ => by
      have e911 : c₁.nreg 911 = Dn := (gn 911 (by omega)).trans h911
      have e912 : c₁.nreg 912 = Sn := (gn 912 (by omega)).trans h912
      have e913 : c₁.nreg 913 = Dr := (gn 913 (by omega)).trans h913
      have e914 : c₁.nreg 914 = Sr := (gn 914 (by omega)).trans h914
      have xs : c₁.nmem (Sn + i) = c.nmem (Sn + i) := gm _ (by omega)
      have xr : c₁.rmem (Sr + i) = c.rmem (Sr + i) := grm _ (by omega)
      unfold cpyBody
      exec_block
      all_goals try ((try config_simp); (try simp only [e911, e912, e913, e914, ha, g916]); omega)
      dsimp only [J]
      config_simp
      simp only [e911, e912, e913, e914, ha, g916]
      refine ⟨by omega, trivial, hb, fun e he => ?_,
        fun a ha' => ?_, fun a ha' => ?_, fun r hr => ?_, trivial, fun r hr => ?_, go⟩
      · simp only [upd_apply]
        by_cases hei : e = i
        · subst hei
          have h1 : Sr + e ≠ Dr + e := by omega
          simp only [↓reduceIte, h1]
          refine ⟨?_, xr⟩
          first
            | exact xs
            | rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact xs
        · have h1 : Dn + e ≠ Dn + i := by omega
          have h2 : Dr + e ≠ Dr + i := by omega
          simp only [h1, h2, ↓reduceIte]
          exact g e (by omega)
      · simp only [upd_apply]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact gm a (by omega)
      · simp only [upd_apply]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact grm a (by omega)
      · simp only [upd_apply]
        split_ifs <;> first | omega | exact gn r hr
      · simp only [upd_apply, hr, ↓reduceIte]; exact gr r hr)) ?_
  rintro c₂ k₂ hk₂ - ⟨-, g, gm, grm, gn, -, gr, go⟩
  refine ⟨by omega, g, gm, grm, fun r hr => ?_, gr, ?_⟩
  · rw [gn r hr]; try (config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl)
  · rw [go]

/-! ### The list of the counting sort -/

theorem csList_congr {T H K : ℕ → ℕ} {Lz Lz' : ℕ → ℤ} :
    ∀ n, (∀ i < n, K i ≠ 0 → Lz i = Lz' i) → csList T H K Lz n = csList T H K Lz' n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [csList]
    rw [csList_congr n fun i hi => h i (by omega)]
    by_cases hK : K n = 0
    · simp [hK]
    · simp [hK, h n (by omega) hK]

theorem length_pre_of_lt {N : ℕ} : ∀ (L : List (ℕ × ℕ × ℤ)), (∀ a ∈ L, a.1 < N) →
    (pre L N).length = L.length := by
  intro L hL
  have h1 : ∀ u, (pre L u).length = (L.filter fun a => a.1 < u).length := by
    intro u
    induction u with
    | zero => simp [pre]
    | succ u ih =>
      rw [pre_succ, List.length_append, ih]
      unfold FR.blk
      rw [← List.countP_eq_length_filter,
        ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      exact countP_split L u
  rw [h1, List.filter_eq_self.2 fun a ha => by simpa using hL a ha]

/-- **All the arcs of the counting sort are laid out** when the kept tails are below `N`. -/
theorem length_arcList_csList {T H K : ℕ → ℕ} {Lz : ℕ → ℤ} {N M : ℕ}
    (h : ∀ i < M, K i ≠ 0 → T i < N) :
    (arcList N (csList T H K Lz M)).length = (csList T H K Lz M).length := by
  refine length_pre_of_lt _ fun a ha => ?_
  obtain ⟨i, hi, hK, rfl⟩ := (mem_csList M).1 ha
  exact h i hi hK

/-! ### The calls of Dijkstra of a step inside a larger configuration -/

section Emb

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {N : CombMap D V F}

/-- **The calls of Dijkstra of a step inside a larger configuration** (`dijk_exec_num` lifted
by `WordRAM.Machine.Exec.lift_trunc`): from any `d` bounded by `W' ≥ P.W` holding the input,
with its registers `< 372` and its natural memory at addresses `≤ P.W` bounded by `P.W`
(`P = mkPrm (w + 1) 1 Dm p 0 Es`), `frProg` runs within `cNegMach.dij (w + 1) |Es|` steps to the
flags and the distances of `dijk_exec_num`, keeping the output, the registers `≥ 372` and the
memory above `P.W`. -/
theorem dijk_exec_emb (C : ℕ) {fr : FRFun (Option V)} (hfr : FRSpec fr) {P₀ P₁ : Finset D}
    {m w : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V} (h : NodeEnc N P₀ P₁ m w e ν ι)
    {X : Finset D} (hX : X ⊆ P₀ ∪ P₁) (hXn : X.Nonempty) (ℓ : D → ℤ) (B : Finset V)
    (E δ : V → ℤ) (hδ : (pg N X ℓ).IsPot δ) (Es : List (ℕ × ℕ × ℤ))
    (hEs : ∀ a ∈ Es, ∃ a' ∈ dijArcs N X ℓ (verts N X) (initLen B E δ),
      (numV ν a'.1, numV ν a'.2.1, a'.2.2) = a)
    (hEs' : ∀ a' ∈ dijArcs N X ℓ (verts N X) (initLen B E δ),
      (numV ν a'.1, numV ν a'.2.1, a'.2.2) ∈ Es)
    (hhd : ∀ a ∈ Es, a.2.1 < w + 1)
    (Dm : ℕ → ℕ → ℤ) (p : ℕ → ℤ) (hp0 : p 0 = price B E δ none)
    (hpv : ∀ x ∈ verts N (P₀ ∪ P₁), p (ν x + 1) = δ x) (I : Input) {W' : ℕ}
    (hW : (mkPrm (w + 1) 1 Dm p 0 Es).W ≤ W') (d : Config) (hd : WordsBounded W' d)
    (hin : Inp (mkPrm (w + 1) 1 Dm p 0 Es) d) (hDa : Data (mkPrm (w + 1) 1 Dm p 0 Es) d)
    (hrb : ∀ r < 372, d.nreg r ≤ (mkPrm (w + 1) 1 Dm p 0 Es).W)
    (hmb : ∀ a ≤ (mkPrm (w + 1) 1 Dm p 0 Es).W, d.nmem a ≤ (mkPrm (w + 1) 1 Dm p 0 Es).W) :
    ∃ d' k, Exec I W' frProg d d' k ∧ k ≤ (cNegMach C).dij (w + 1) Es.length ∧
      d'.output = d.output ∧
      (∀ v < w, (d'.nmem ((mkPrm (w + 1) 1 Dm p 0 Es).sb + (v + 1)) = 1 ↔
        ∃ x ∈ verts N (P₀ ∪ P₁), ν x = v ∧ dijk N fr X ℓ B E δ (some x) ≠ none)) ∧
      (∀ x ∈ verts N (P₀ ∪ P₁), ∀ z, dijk N fr X ℓ B E δ (some x) = some z →
        d'.rmem ((mkPrm (w + 1) 1 Dm p 0 Es).db + (ν x + 1)) = z) ∧
      (∀ r, 372 ≤ r → d'.nreg r = d.nreg r) ∧ (∀ r, 372 ≤ r → d'.rreg r = d.rreg r) ∧
      (∀ a, (mkPrm (w + 1) 1 Dm p 0 Es).W < a → d'.nmem a = d.nmem a) ∧
      (∀ a, (mkPrm (w + 1) 1 Dm p 0 Es).W < a → d'.rmem a = d.rmem a) := by
  set Pr := mkPrm (w + 1) 1 Dm p 0 Es with hPr
  have hL : Lay Pr := mkPrm_lay le_rfl (by omega) (by omega) hhd
  have := hL.m5; have := hL.m6; have := lay_w hL
  have hN : Pr.N = w + 1 := rfl
  have hWW : (mkPrm (w + 1) 1 Dm p 0 Es).W = Pr.W := rfl
  have hsb : Pr.sb + (w + 1) ≤ Pr.W := by omega
  have hdb : Pr.db + (w + 1) ≤ Pr.W := by omega
  set c := trunc frU Pr.W d with hcdef
  have hA := agree_trunc frU Pr.W d
  have hn : ∀ r < 372, c.nreg r = d.nreg r := fun r hr => (hA.nreg r (by simp [frU, hr])).symm
  have hw : WordsBounded Pr.W c :=
    wordsBounded_trunc (fun r hr => hrb r (by simpa [frU] using hr)) hmb
  have hinc : Inp Pr c := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hn _ (by omega)]
    exacts [hin.r100, hin.r101, hin.r102, hin.r103, hin.r104, hin.r105, hin.r106, hin.r107,
      hin.r108, hin.r109]
  have hDac : Data Pr c :=
    hDa.congr hL (fun a ha => (hA.nmem a ha).symm) (fun a ha => (hA.rmem a ha).symm)
  obtain ⟨c', k, ex, hk, ho, hfl, hval⟩ := dijk_exec_num C hfr h hX hXn ℓ B E δ hδ Es hEs hEs'
    Dm p hp0 hpv I c hw hinc hDac
  obtain ⟨d', e', hA', hK, ho'⟩ :=
    Exec.lift_trunc (P' := I) ex frProg_regsOK frProg_noInp frProg_noRand hW hd
  refine ⟨d', k, e', hk, by rw [ho', ho]; rfl, fun v hv => ?_, fun x hx z hz => ?_,
    fun r hr => hK.nreg r (by simp [frU]; omega), fun r hr => hK.rreg r (by simp [frU]; omega),
    hK.nmem, hK.rmem⟩
  · rw [hA'.nmem _ (by omega)]; exact hfl v hv
  · have := h.lt x hx
    rw [hA'.rmem _ (by omega)]; exact hval x hx z hz

end Emb

end NegSSSP

end PlanarFlow
