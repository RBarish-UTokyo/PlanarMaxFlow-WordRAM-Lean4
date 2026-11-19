module

public import PlanarFlow.NegSSSP.SplitPrep
public import PlanarFlow.NegSSSP.ChildRun

/-!
# The split stage of the driver: the split of the machine and the frames of the children

**`splitS`** `= spStage ; chSet0 ; ceProg ; chMid ; ceProg ; chEnd`: from the frame of a piece
`P` (`InP (n + 1) P d e`, `r3004 = d`, `r3003 = h` the heap top), the canonical split
(`spStage`, so the sides are those of `msplit P`), then the frames of the two children in the
canonical format at `h + 5` and `el + 5` (`ceProg` twice, `s = 0, 1`), `r2998 = el`,
`r2999 = er`. **`splitS_exec`** gives the conclusion of the field `spl` of `NSpec` (all but the
invariant `G` of the driver) with `split = msplit g N`, within
`prepCost k + splitT k + 2 (44 k + 41 m + 70) + 43` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Frame

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Driver

variable {I : Input} {W : ℕ}

/-- The registers of the first child (`s = 0`, `Cb = h + 5`; `r2981 = Ob`, `r2983 = Cb`). -/
def chSet0 : Stmt := block [.constN 2930 0, .copyN 2931 3004, .constN 2981 41,
  .mulN 2981 2981 2969, .addN 2981 2981 2972, .constN 2982 4, .addN 2981 2981 2982,
  .copyN 2934 2981, .constN 2935 0, .copyN 2936 2969, .constN 2982 5, .addN 2937 3003 2982,
  .copyN 2983 2937]

/-- `el` (the end of the first child) into `r2998`, the registers of the second child
(`s = 1`, `Cb = el + 5`, kept in `r2989`). -/
def chMid : Stmt := block [.addN 2984 2983 2966, .loadN 2985 2984, .addN 2984 2984 2966,
  .loadN 2986 2984, .addN 2987 2985 2986, .constN 2988 5, .mulN 2987 2987 2988,
  .constN 2988 6, .addN 2987 2987 2988, .addN 2987 2987 2983, .copyN 2998 2987,
  .constN 2930 1, .copyN 2931 3004, .copyN 2934 2981, .constN 2935 0, .copyN 2936 2969,
  .constN 2988 5, .addN 2937 2987 2988, .copyN 2989 2937]

/-- `er` (the end of the second child) into `r2999`. -/
def chEnd : Stmt := block [.addN 2984 2989 2966, .loadN 2985 2984, .addN 2984 2984 2966,
  .loadN 2986 2984, .addN 2987 2985 2986, .constN 2988 5, .mulN 2987 2987 2988,
  .constN 2988 6, .addN 2987 2987 2988, .addN 2987 2987 2989, .copyN 2999 2987]

/-- **The split stage of the driver.** -/
def splitS : Stmt :=
  .seq spStage <| .seq chSet0 <| .seq ceProg <| .seq chMid <| .seq ceProg chEnd

set_option maxHeartbeats 1000000 in
theorem chSet0_exec (c : Config) (hc : WordsBounded W c) {d h k B : ℕ}
    (r04 : c.nreg 3004 = d) (r03 : c.nreg 3003 = h) (r69 : c.nreg 2969 = k)
    (r72 : c.nreg 2972 = B) (hW : B + 41 * k + 4 + h + 5 ≤ W) (w41 : 41 ≤ W) :
    ∃ c' t, Exec I W chSet0 c c' t ∧ t = 13 ∧ c'.nreg 2930 = 0 ∧ c'.nreg 2931 = d ∧
      c'.nreg 2934 = B + 41 * k + 4 ∧ c'.nreg 2935 = 0 ∧ c'.nreg 2936 = k ∧
      c'.nreg 2937 = h + 5 ∧ c'.nreg 2981 = B + 41 * k + 4 ∧ c'.nreg 2983 = h + 5 ∧
      (∀ r, (r < 2930 ∨ 2983 < r) → c'.nreg r = c.nreg r) ∧
      (∀ r, 2965 < r → r < 2981 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold chSet0
  exec_block
  all_goals try ((try config_simp); (try simp only [r04, r03, r69, r72]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl,
    rfl⟩
  all_goals config_simp
  all_goals try (simp only [r04, r03, r69, r72])
  all_goals try omega
  all_goals simp only [upd_apply]; split_ifs <;> omega

set_option maxHeartbeats 2000000 in
theorem chMid_exec (c : Config) (hc : WordsBounded W c) {d k Ob Cb m₀ k₀ : ℕ}
    (r66 : c.nreg 2966 = 1) (r04 : c.nreg 3004 = d) (r69 : c.nreg 2969 = k)
    (r81 : c.nreg 2981 = Ob) (r83 : c.nreg 2983 = Cb) (hm : c.nmem (Cb + 1) = m₀)
    (hk : c.nmem (Cb + 2) = k₀) (hW : Cb + fsz m₀ k₀ + 5 ≤ W) :
    ∃ c' t, Exec I W chMid c c' t ∧ t = 19 ∧ c'.nreg 2998 = Cb + fsz m₀ k₀ ∧
      c'.nreg 2930 = 1 ∧ c'.nreg 2931 = d ∧ c'.nreg 2934 = Ob ∧ c'.nreg 2935 = 0 ∧
      c'.nreg 2936 = k ∧ c'.nreg 2937 = Cb + fsz m₀ k₀ + 5 ∧
      c'.nreg 2989 = Cb + fsz m₀ k₀ + 5 ∧
      (∀ r, (r < 2930 ∨ (2989 < r ∧ r ≠ 2998)) → c'.nreg r = c.nreg r) ∧
      (∀ r, 2965 < r → r < 2984 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fsz at hW ⊢
  unfold chMid
  exec_block
  all_goals try ((try config_simp); (try simp only [r66, r04, r69, r81, r83, hm, hk]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl,
    rfl⟩
  all_goals config_simp
  all_goals try (simp only [r66, r04, r69, r81, r83, hm, hk])
  all_goals try omega
  all_goals (repeat rw [upd_other _ _ _ (by omega)])

theorem chEnd_exec (c : Config) (hc : WordsBounded W c) {Cb m₁ k₁ : ℕ}
    (r66 : c.nreg 2966 = 1) (r89 : c.nreg 2989 = Cb) (hm : c.nmem (Cb + 1) = m₁)
    (hk : c.nmem (Cb + 2) = k₁) (hW : Cb + fsz m₁ k₁ ≤ W) :
    ∃ c' t, Exec I W chEnd c c' t ∧ t = 11 ∧ c'.nreg 2999 = Cb + fsz m₁ k₁ ∧
      (∀ r, (r < 2984 ∨ (2988 < r ∧ r ≠ 2999)) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fsz at hW ⊢
  unfold chEnd
  exec_block
  all_goals try ((try config_simp); (try simp only [r66, r89, hm, hk]); omega)
  refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r66, r89, hm, hk])
  all_goals try omega
  simp only [upd_apply]; split_ifs <;> omega

/-- The cost of the split stage (`m` darts, `k` half-edges). -/
def splitSCost (m k : ℕ) : ℕ :=
  prepCost k + splitT k + 13 + (44 * k + 41 * m + 70) + 19 + (44 * k + 41 * m + 70) + 11

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {g : GIds D V} {N : CombMap D V F}

set_option maxHeartbeats 4000000 in
/-- **The split stage of the driver on the machine** (the field `spl` of `NSpec` but the
invariant `G`): from the frame of `Q ⊆ reps N` with `n + 1` rounds at `[d, e)`, the heap top
`h` in `r3003`, the work area `[0, spWs k]` below the heap base `Hb`, its reals zero: within
`splitSCost m k` steps the frames of the two parts of `msplit g N Q` with `n` rounds at
`[h + 5, el)` and `[el + 5, er)`, `r2998 = el`, `r2999 = er`; the registers `≥ 3000` and the
heap `[Hb, h)` kept. -/
theorem splitS_exec (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {ℓ : D → ℤ} {L n : ℕ} {Q : Finset D} (hQ : Q ⊆ reps N) {d e h Hb : ℕ} (c : Config)
    (hc : WordsBounded W c) (hin : InP g N ℓ L (n + 1) Q d e c) (r04 : c.nreg 3004 = d)
    (r03 : c.nreg 3003 = h) (hHb : spWs (ck N Q) < Hb) (hHd : Hb ≤ d)
    (heh : e ≤ h) (hrr : ∀ r < 972, c.rreg r = 0) (hrm : ∀ a ≤ spWs (ck N Q), c.rmem a = 0)
    (hW : h + 10 + 2 * fsz Q.card (ck N Q) + spWs (ck N Q) + 205 ≤ W) :
    ∃ c' t el er, Exec I W splitS c c' t ∧ t ≤ splitSCost Q.card (ck N Q) ∧ RegKeep c c' ∧
      HeapKeep Hb h h h c c' ∧ c'.output = c.output ∧ c'.nreg 2998 = el ∧
      c'.nreg 2999 = er ∧ h + 5 ≤ el ∧ el + 5 ≤ er ∧
      InP g N ℓ L n (msplit g N Q).1 (h + 5) el c' ∧
      InP g N ℓ L n (msplit g N Q).2 (el + 5) er c' ∧
      (∀ r, 972 ≤ r → c'.rreg r = c.rreg r) ∧
      (∀ a, spWs (ck N Q) < a → c'.rmem a = c.rmem a) := by
  set k := ck N Q with hk
  have eq1 : spWs (ck N Q) = spWs k := rfl
  have eq2 : spB0 (ck N Q) = spB0 k := rfl
  have eq3 : ck N Q = k := rfl
  have eq4 : prepCost (ck N Q) = prepCost k := rfl
  have eq5 : splitT (ck N Q) = splitT k := rfl
  have hmk : Q.card ≤ k := ck_ge Q
  have hk2 : k ≤ 2 * Q.card := card_rcl_le Q
  have he := hin.en
  unfold fsz at he hW
  have hWs : spWs k = spB0 k + 66 * k + 35 := rfl
  have hB3 : 3 * k ≤ spB0 k := by unfold spB0; omega
  set Q₀ := (msplit g N Q).1 with hQ₀
  set Q₁ := (msplit g N Q).2 with hQ₁
  have hQ₀Q : Q₀ ⊆ Q := filter_subset _ _
  have hQ₁Q : Q₁ ⊆ Q := filter_subset _ _
  have hk₀ : ck N Q₀ ≤ k := card_le_card (rcl_mono' hQ₀Q)
  have hk₁ : ck N Q₁ ≤ k := card_le_card (rcl_mono' hQ₁Q)
  have hm₀ : Q₀.card ≤ Q.card := card_le_card hQ₀Q
  have hm₁ : Q₁.card ≤ Q.card := card_le_card hQ₁Q
  -- the canonical split
  obtain ⟨c₁, t₁, e₁, ht₁, hside, p66, p69, p72, m₁, n₁, rr₁, rm₁, o₁⟩ :=
    spStage_exec (P := I) hM hrot hface hQ c hc
      (by have := hin; exact this) r04 (by omega) hrr hrm (by omega) (by omega)
  have hw₁ := e₁.wb_right
  have hin₁ : InP g N ℓ L (n + 1) Q d e c₁ := inP_stab hin fun a h1 h2 =>
    ⟨m₁ a (by omega), (by
      have := rm₁ a (by omega); exact this)⟩
  -- the first child
  obtain ⟨c₂, t₂, e₂, ht₂, s30, s31, s34, s35, s36, s37, s81, s83, sn₂, sk₂, sm₂, sr₂, srm₂,
    so₂⟩ := chSet0_exec (I := I) (d := d) (h := h) (k := k) (B := spB0 k) c₁ hw₁
      (by rw [n₁ _ (by omega) (by omega)]; exact r04)
      (by rw [n₁ _ (by omega) (by omega)]; exact r03) p69 p72 (by omega) (by omega)
  have hw₂ := e₂.wb_right
  have hin₂ : InP g N ℓ L (n + 1) Q d e c₂ := inP_stab hin₁ fun a _ _ => by rw [sm₂, srm₂]; simp
  have hS₀ : SideOK Q Q₀ 0 (fun x => c₂.nmem (spB0 k + 41 * k + 4 + x)) (cδ g N Q) :=
    ⟨hQ₀Q, fun x hx => by rw [sm₂]; exact (hside x hx).1⟩
  obtain ⟨c₃, t₃, e₃, ht₃, ch₀, cm₃, cn₃, cr₃, crm₃, co₃⟩ :=
    ceProg_exec (I := I) (Q := Q₀) (s := 0) c₂ hw₂ hin₂ s30 s31 s34 s35 s36 s37 hS₀
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by unfold fsz; omega)
  have hw₃ := e₃.wb_right
  -- the second child
  obtain ⟨c₄, t₄, e₄, ht₄, u98, u30, u31, u34, u35, u36, u37, u89, un₄, uk₄, um₄, ur₄, urm₄,
    uo₄⟩ := chMid_exec (I := I) (d := d) (k := k) (Ob := spB0 k + 41 * k + 4) (Cb := h + 5)
      c₃ hw₃ (by rw [cn₃ _ (by omega), sk₂ _ (by omega) (by omega)]; exact p66)
      (by rw [cn₃ _ (by omega), sn₂ _ (by omega), n₁ _ (by omega) (by omega)]; exact r04)
      (by rw [cn₃ _ (by omega), sk₂ _ (by omega) (by omega)]; exact p69)
      (by rw [cn₃ _ (by omega)]; exact s81) (by rw [cn₃ _ (by omega)]; exact s83)
      ch₀.rm ch₀.rk (by unfold fsz; omega)
  have hw₄ := e₄.wb_right
  have hin₄ : InP g N ℓ L (n + 1) Q d e c₄ := inP_stab hin₂ fun a h1 h2 => by
    rw [um₄, urm₄, cm₃ a (by omega) (by omega) (by omega), crm₃]; simp
  have hS₁ : SideOK Q Q₁ 1 (fun x => c₄.nmem (spB0 k + 41 * k + 4 + x)) (cδ g N Q) :=
    ⟨hQ₁Q, fun x hx => by
      dsimp only
      rw [um₄, cm₃ (spB0 k + 41 * k + 4 + x) (by omega) (by omega) (by omega), sm₂]
      have := (hside x hx).2.2
      change c₁.nmem (spB0 (ck N Q) + 41 * ck N Q + 4 + x) = 1 ↔ _
      rw [← (hside x hx).2.1]; omega⟩
  obtain ⟨c₅, t₅, e₅, ht₅, ch₁, cm₅, cn₅, cr₅, crm₅, co₅⟩ :=
    ceProg_exec (I := I) (Q := Q₁) (s := 1) c₄ hw₄ hin₄ u30 u31 u34 u35 u36 u37 hS₁
      (by unfold fsz; omega) (by unfold fsz; omega) (by omega) (by unfold fsz; omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by unfold fsz; omega)
  have hw₅ := e₅.wb_right
  obtain ⟨c₆, t₆, e₆, ht₆, v99, vn₆, vm₆, vr₆, vrm₆, vo₆⟩ :=
    chEnd_exec (I := I) (Cb := h + 5 + fsz Q₀.card (ck N Q₀) + 5) c₅ hw₅
      (by rw [cn₅ _ (by omega), uk₄ _ (by omega) (by omega), cn₃ _ (by omega),
            sk₂ _ (by omega) (by omega)]
          exact p66)
      (by rw [cn₅ _ (by omega)]; exact u89) ch₁.rm ch₁.rk (by unfold fsz; omega)
  -- the first child survives
  have ch₀' : InP g N ℓ L n Q₀ (h + 5) (h + 5 + fsz Q₀.card (ck N Q₀)) c₆ := by
    have : n + 1 - 1 = n := rfl
    rw [this] at ch₀
    refine inP_stab ch₀ fun a h1 h2 => ?_
    rw [vm₆, vrm₆, cm₅ a (by unfold fsz at h2 ⊢; omega) (by omega) (by omega), crm₅, um₄, urm₄]
    simp
  have ch₁' : InP g N ℓ L n Q₁ (h + 5 + fsz Q₀.card (ck N Q₀) + 5)
      (h + 5 + fsz Q₀.card (ck N Q₀) + 5 + fsz Q₁.card (ck N Q₁)) c₆ := by
    have : n + 1 - 1 = n := rfl
    rw [this] at ch₁
    exact inP_stab ch₁ fun a _ _ => by rw [vm₆, vrm₆]; simp
  refine ⟨c₆, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + t₆)))), _, _,
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), ?_, fun r hr => ?_, fun a h1 h2 _ => ?_,
    ?_, by rw [vn₆ _ (by omega), cn₅ _ (by omega)]; exact u98, v99, by unfold fsz; omega,
    by unfold fsz; omega, ch₀', ch₁', fun r hr => ?_, fun a ha => ?_⟩
  · unfold splitSCost; omega
  · rw [vn₆ r (by omega), cn₅ r (by omega), un₄ r (by omega), cn₃ r (by omega), sn₂ r (by omega),
      n₁ r (by omega) (by omega)]
  · have hm : c₆.nmem a = c.nmem a := by
      rw [vm₆, cm₅ a (by omega) (by omega) (by omega), um₄, cm₃ a (by omega) (by omega)
        (by omega), sm₂, m₁ a (by omega)]
    have hr : c₆.rmem a = c.rmem a := by
      rw [vrm₆, crm₅, urm₄, crm₃, srm₂, rm₁ a (by omega)]
    exact ⟨hm, hr⟩
  · rw [vo₆, co₅, uo₄, co₃, so₂, o₁]
  · rw [vr₆, cr₅, ur₄, cr₃, sr₂, rr₁ r hr]
  · rw [vrm₆, crm₅, urm₄, crm₃, srm₂, rm₁ a ha]

/-! ### The test of the driver -/

/-- **The parts of `msplit` cover the piece** (they are the two filters by the side). -/
theorem msplit_union (P : Finset D) : (msplit g N P).1 ∪ (msplit g N P).2 = P := by
  ext x
  simp only [msplit, mem_union, mem_filter]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    by_cases h0 : (spFin g N P).nmem (spB0 (ck N P) + 41 * ck N P + 4 + (cL g P).idxOf x) = 0
    · exact Or.inl ⟨h, h0⟩
    · exact Or.inr ⟨h, h0⟩

/-- The condition of a node with the machine's split: a round left and more than `10⁶` darts. -/
theorem cnd_msplit {n : ℕ} {P : Finset D} :
    Cnd (msplit g N) n P ↔ 0 < n ∧ 1000000 < P.card :=
  ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, msplit_union P⟩⟩

/-- The test: `r2997 := 1` if `0 < n` and `10⁶ < m` (read from the frame at `r3004`). -/
def testS : Stmt :=
  .seq (block [.constN 2991 1, .addN 2992 3004 2991, .loadN 2993 2992, .loadN 2994 3004,
      .constN 2997 0, .constN 2995 1000000, .constN 2996 0])
    (.ifLtN 2996 2994 (.ifLtN 2995 2993 (.instr (.constN 2997 1)) .skip) .skip)

/-- **The test of the driver** (the field `test` of `NSpec` but `G`, for `split = msplit`). -/
theorem testS_exec {ℓ : D → ℤ} {L n : ℕ} {P : Finset D} {d e : ℕ} (c : Config)
    (hc : WordsBounded W c) (hin : InP g N ℓ L n P d e c) (r04 : c.nreg 3004 = d)
    (hW : d + 1 ≤ W) (hW' : 1000000 ≤ W) :
    ∃ c' t, Exec I W testS c c' t ∧ t ≤ 11 ∧ (c'.nreg 2997 < 1 ↔ ¬ Cnd (msplit g N) n P) ∧
      (∀ r, r ≠ 2997 → (r < 2991 ∨ 2996 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, g93, g94, g95, g96, g97, gn, gm, gr, grm, go⟩ : ∃ c₁ t₁,
      Exec I W (block [.constN 2991 1, .addN 2992 3004 2991, .loadN 2993 2992, .loadN 2994 3004,
        .constN 2997 0, .constN 2995 1000000, .constN 2996 0]) c c₁ t₁ ∧ t₁ = 7 ∧
      c₁.nreg 2993 = P.card ∧ c₁.nreg 2994 = n ∧ c₁.nreg 2995 = 1000000 ∧ c₁.nreg 2996 = 0 ∧
      c₁.nreg 2997 = 0 ∧ (∀ r, r ≠ 2997 → (r < 2991 ∨ 2996 < r) → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    have hm := hin.rm
    have hn := hin.rn
    exec_block
    all_goals try ((try config_simp); (try simp only [r04, hm, hn]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r04, hm, hn])
    repeat rw [upd_other _ _ _ (by omega)]
  have hw₁ := e₁.wb_right
  rw [cnd_msplit]
  by_cases hn0 : 0 < n
  · by_cases hm0 : 1000000 < P.card
    · have e₂ := Exec.constN (P := I) hw₁ 2997 1 (by omega)
      refine ⟨_, t₁ + ((1 + 1) + 1), .seq e₁ (.ifLtN_true (by rw [g96, g94]; exact hn0)
        (.ifLtN_true (by rw [g95, g93]; exact hm0) e₂)), by omega, ?_, fun r h1 h2 => ?_,
        by simp [gm], by simp [gr], by simp [grm], by simp [go]⟩
      · simp only [upd_apply, ite_true]; omega
      · simp only [upd_apply, h1, ite_false]; exact gn r h1 h2
    · refine ⟨c₁, t₁ + ((0 + 2) + 1), .seq e₁ (.ifLtN_true (by rw [g96, g94]; exact hn0)
        (.ifLtN_false (by rw [g95, g93]; exact hm0) (.skip hw₁))), by omega, ?_, gn, gm, gr,
        grm, go⟩
      rw [g97]; omega
  · refine ⟨c₁, t₁ + (0 + 2), .seq e₁ (.ifLtN_false (by rw [g96, g94]; exact hn0)
      (.skip hw₁)), by omega, ?_, gn, gm, gr, grm, go⟩
    rw [g97]; omega

end Frame

end NegSSSP

end PlanarFlow
