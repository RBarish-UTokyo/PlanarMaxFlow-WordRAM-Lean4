module

public import PlanarFlow.NegSSSP.SplitChild
public import PlanarFlow.NegSSSP.DriverRoomRun

/-!
# Towards the instance of `NSpecR`: the invariant, the test and the split fields

* `exec_reals_keep`: a statement without real instructions (`Klein.natOnly`) keeps the real
  registers and the real memory.
* `GZ Hb c`: the invariant of the driver — every real register zero, the real memory below `Hb`
  zero (`gz_stab`: the field `g_stab`). Every subprogram of the driver is natural-only, so `GZ`
  is kept.
* `InPR`: the frame input `InP` with `P ⊆ reps N` (a pure side condition, stable).
* `rSf`: the room of the split, `10 + 2 fsz m k + spWs k + 205`; `spWs_mono`.
* **`nspec_testR`**, **`nspec_splR`**: the fields `test` and `spl` of `NSpecR` for `testS`,
  `splitS` with `split = msplit g N`, `G = GZ Hb`, `In = InPR`, the costs `11` and
  `splitSCost #P (ck N P)`, the room `rSf`, for `Hb > spWs (#D)` (the work area of the split
  below the heap) and `W ≥ 10⁶`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Frame

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Driver

variable {I : Input} {W : ℕ}

/-- A non-real instruction keeps the reals. -/
theorem effect_reals_keep {i : Instr} (hi : i.isReal = false) {c c' : Config}
    (he : i.effect I c = some c') : c'.rreg = c.rreg ∧ c'.rmem = c.rmem := by
  cases i <;> simp_all [Instr.isReal, Instr.effect] <;> (subst he; exact ⟨rfl, rfl⟩)

/-- **A statement without real instructions keeps the real registers and the real memory.** -/
theorem exec_reals_keep {s : Stmt} (hs : Klein.natOnly s = true) {c c' : Config} {t : ℕ}
    (e : Exec I W s c c' t) : c'.rreg = c.rreg ∧ c'.rmem = c.rmem := by
  induction e with
  | skip _ => exact ⟨rfl, rfl⟩
  | instr _ he _ _ =>
    simp only [Klein.natOnly, Bool.not_eq_true'] at hs
    exact effect_reals_keep hs he
  | seq _ _ ih₁ ih₂ =>
    simp only [Klein.natOnly, Bool.and_eq_true] at hs
    obtain ⟨a1, b1⟩ := ih₁ hs.1
    obtain ⟨a2, b2⟩ := ih₂ hs.2
    exact ⟨a2.trans a1, b2.trans b1⟩
  | ifLtN_true _ _ ih =>
    simp only [Klein.natOnly, Bool.and_eq_true] at hs; exact ih hs.1
  | ifLtN_false _ _ ih =>
    simp only [Klein.natOnly, Bool.and_eq_true] at hs; exact ih hs.2
  | ifLtR_true _ _ _ => simp [Klein.natOnly] at hs
  | ifLtR_false _ _ _ => simp [Klein.natOnly] at hs
  | whileLtN_false _ _ => exact ⟨rfl, rfl⟩
  | whileLtN_true _ _ _ ih₁ ih₂ =>
    obtain ⟨a1, b1⟩ := ih₁ (by simpa [Klein.natOnly] using hs)
    obtain ⟨a2, b2⟩ := ih₂ hs
    exact ⟨a2.trans a1, b2.trans b1⟩
  | whileLtR_false _ _ => simp [Klein.natOnly] at hs
  | whileLtR_true _ _ _ _ _ => simp [Klein.natOnly] at hs

theorem splitS_natOnly : Klein.natOnly splitS = true := by decide +kernel
theorem testS_natOnly : Klein.natOnly testS = true := by decide +kernel

/-- **The invariant of the driver**: the reals zero (the registers everywhere, the memory below
`Hb`) and the scratch table `[Gt, Gt + nG)` of the numberings zero. -/
def GZ (Hb Gt nG : ℕ) (c : Config) : Prop :=
  (∀ r, c.rreg r = 0) ∧ (∀ a < Hb, c.rmem a = 0) ∧ ∀ a < nG, c.nmem (Gt + a) = 0

theorem gz_stab {Hb Gt nG : ℕ} (hG : Gt + nG ≤ Hb) {c c' : Config} (h : GZ Hb Gt nG c)
    (hr : c'.rreg = c.rreg) (hm : MemEq c c' 0 Hb) : GZ Hb Gt nG c' :=
  ⟨fun r => by rw [hr]; exact h.1 r,
    fun a ha => by rw [(hm a (Nat.zero_le _) ha).2]; exact h.2.1 a ha,
    fun a ha => by rw [(hm (Gt + a) (Nat.zero_le _) (by omega)).1]; exact h.2.2 a ha⟩

/-- `GZ` after a natural-only run keeping the table. -/
theorem gz_of_natOnly {Hb Gt nG : ℕ} {s : Stmt} (hs : Klein.natOnly s = true) {c c' : Config}
    {t : ℕ} (e : Exec I W s c c' t) (h : GZ Hb Gt nG c)
    (hT : ∀ a < nG, c'.nmem (Gt + a) = c.nmem (Gt + a)) : GZ Hb Gt nG c' := by
  obtain ⟨h1, h2⟩ := exec_reals_keep hs e
  exact ⟨fun r => by rw [h1]; exact h.1 r, fun a ha => by rw [h2]; exact h.2.1 a ha,
    fun a ha => by rw [hT a ha]; exact h.2.2 a ha⟩

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {g : GIds D V} {N : CombMap D V F}

variable (g N) in
/-- The frame input with the piece among the kept darts. -/
def InPR (ℓ : D → ℤ) (L n : ℕ) (P : Finset D) (d e : ℕ) (c : Config) : Prop :=
  P ⊆ reps N ∧ InP g N ℓ L n P d e c

theorem inPR_stab {ℓ : D → ℤ} {L n : ℕ} {P : Finset D} {d e : ℕ} {c c' : Config}
    (h : InPR g N ℓ L n P d e c) (hm : MemEq c c' d e) : InPR g N ℓ L n P d e c' :=
  ⟨h.1, inP_stab h.2 hm⟩

/-- The room of the split. -/
def rSf (m k : ℕ) : ℕ := 10 + 2 * fsz m k + spWs k + 205

theorem spWs_mono {k k' : ℕ} (h : k ≤ k') : spWs k ≤ spWs k' := by
  have e1 := spB0_eq k
  have e2 := spB0_eq k'
  have hl : Nat.log 2 (3 * k) ≤ Nat.log 2 (3 * k') := Nat.log_mono_right (by omega)
  have : (Nat.log 2 (3 * k) + 2) * (3 * k) ≤ (Nat.log 2 (3 * k') + 2) * (3 * k') :=
    Nat.mul_le_mul (by omega) (by omega)
  unfold spWs; omega

theorem ck_le_card (P : Finset D) : ck N P ≤ Fintype.card D := card_le_univ _

set_option maxHeartbeats 4000000 in
/-- **`splitS_exec` with the memory above the work area kept** (below the heap too) (the field `spl` of `NSpec` but the
invariant `G`): from the frame of `Q ⊆ reps N` with `n + 1` rounds at `[d, e)`, the heap top
`h` in `r3003`, the work area `[0, spWs k]` below the heap base `Hb`, its reals zero: within
`splitSCost m k` steps the frames of the two parts of `msplit g N Q` with `n` rounds at
`[h + 5, el)` and `[el + 5, er)`, `r2998 = el`, `r2999 = er`; the registers `≥ 3000` and the
heap `[Hb, h)` kept. -/
theorem splitS_exec' (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {ℓ : D → ℤ} {L n : ℕ} {Q : Finset D} (hQ : Q ⊆ reps N) {d e h Hb : ℕ} (c : Config)
    (hc : WordsBounded W c) (hin : InP g N ℓ L (n + 1) Q d e c) (r04 : c.nreg 3004 = d)
    (r03 : c.nreg 3003 = h) (hHb : spWs (ck N Q) < Hb) (hHd : Hb ≤ d)
    (heh : e ≤ h) (hrr : ∀ r < 972, c.rreg r = 0) (hrm : ∀ a ≤ spWs (ck N Q), c.rmem a = 0)
    (hW : h + 10 + 2 * fsz Q.card (ck N Q) + spWs (ck N Q) + 205 ≤ W) :
    ∃ c' t el er, Exec I W splitS c c' t ∧ t ≤ splitSCost Q.card (ck N Q) ∧ RegKeep c c' ∧
      (∀ a, spWs (ck N Q) < a → a < h → c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧
      c'.output = c.output ∧ c'.nreg 2998 = el ∧
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
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), ?_, fun r hr => ?_, fun a h1 h2 => ?_,
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


/-- **The field `test` of `NSpecR`.** -/
theorem nspec_testR {ℓ : D → ℤ} {L Hb Gt nG : ℕ} (hW6 : 1000000 ≤ W) :
    ∀ n P d e h c, GZ Hb Gt nG c → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → InPR g N ℓ L n P d e c →
    ∃ c' t, Exec I W testS c c' t ∧ t ≤ 11 ∧ GZ Hb Gt nG c' ∧ RegKeep c c' ∧ HeapKeep Hb h h h c c' ∧
      c'.output = c.output ∧ (c'.nreg 2997 < 1 ↔ ¬ Cnd (msplit g N) n P) := by
  intro n P d e h c hg hc r04 r05 r03 b1 b2 b3 ⟨_, hin⟩
  have hhW : h ≤ W := r03 ▸ WordsBounded.nreg hc 3003
  have he := hin.en
  unfold fsz at he
  obtain ⟨c', t, ex, ht, hcnd, hr, hn, hrr, hrm, ho⟩ :=
    testS_exec (I := I) c hc hin r04 (by omega) hW6
  exact ⟨c', t, ex, ht, gz_of_natOnly testS_natOnly ex hg (fun a _ => by rw [hn]),
    fun r hr' => hr r (by omega) (by omega), heapKeep_of_eq hn hrm _ _ _ _, ho, hcnd⟩

/-- **The field `spl` of `NSpecR`** (room `rSf`). -/
theorem nspec_splR (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans) {ℓ : D → ℤ}
    {L Hb Gt nG : ℕ} (hGt : spWs (Fintype.card D) < Gt) (hGH : Gt + nG ≤ Hb) :
    ∀ n P d e h c, GZ Hb Gt nG c → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → h + rSf P.card (ck N P) ≤ W →
    InPR g N ℓ L (n + 1) P d e c → Cnd (msplit g N) (n + 1) P →
    ∃ c' t el er, Exec I W splitS c c' t ∧ t ≤ splitSCost P.card (ck N P) ∧ GZ Hb Gt nG c' ∧
      RegKeep c c' ∧ HeapKeep Hb h h h c c' ∧ c'.output = c.output ∧ c'.nreg 2998 = el ∧
      c'.nreg 2999 = er ∧ h + 5 ≤ el ∧ el + 5 ≤ er ∧ er ≤ h + rSf P.card (ck N P) ∧
      InPR g N ℓ L n (msplit g N P).1 (h + 5) el c' ∧
      InPR g N ℓ L n (msplit g N P).2 (el + 5) er c' := by
  intro n P d e h c hg hc r04 r05 r03 b1 b2 b3 hroom ⟨hPr, hin⟩ _
  have hws : spWs (ck N P) ≤ spWs (Fintype.card D) := spWs_mono (ck_le_card P)
  obtain ⟨c', t, el, er, ex, ht, rk, hk, ho, s98, s99, hel, her, i0, i1, rr, rm⟩ :=
    splitS_exec' (I := I) (Hb := Hb) hM hrot hface hPr c hc hin r04 r03 (by omega) (by omega) b3
      (fun r _ => hg.1 r) (fun a ha => hg.2.1 a (by omega)) (by unfold rSf at hroom; omega)
  have hP0 : (msplit g N P).1 ⊆ P := filter_subset _ _
  have hP1 : (msplit g N P).2 ⊆ P := filter_subset _ _
  have e0 := i0.en
  have e1 := i1.en
  have hk0 : ck N (msplit g N P).1 ≤ ck N P := card_le_card (rcl_mono' hP0)
  have hk1 : ck N (msplit g N P).2 ≤ ck N P := card_le_card (rcl_mono' hP1)
  have hm0 := card_le_card hP0
  have hm1 := card_le_card hP1
  refine ⟨c', t, el, er, ex, ht, ?_, rk, fun a h1 h2 _ => hk a (by omega) h2, ho, s98, s99, hel,
    her, ?_, ⟨hP0.trans hPr, i0⟩, ⟨hP1.trans hPr, i1⟩⟩
  · obtain ⟨h1, h2⟩ := exec_reals_keep splitS_natOnly ex
    exact ⟨fun r => by rw [h1]; exact hg.1 r, fun a ha => by rw [h2]; exact hg.2.1 a ha,
      fun a ha => by rw [(hk (Gt + a) (by omega) (by omega)).1]; exact hg.2.2 a ha⟩
  · unfold rSf; unfold fsz at e0 e1 ⊢; omega

end Frame

end NegSSSP

end PlanarFlow
