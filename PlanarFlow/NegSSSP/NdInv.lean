module

public import PlanarFlow.NegSSSP.NdComb

/-!
# The driver's invariant with the memory below the heap zero

The node of the driver needs the natural memory below its word bound zero (the residue area of
the simulated real memory); zeroing it at every
node is too slow. So the driver keeps **all** natural memory below the heap base zero:

* `GZ0 Hb c`: reals zero (registers, memory below `Hb`), natural memory below `Hb` zero;
  `gz0_stab` (the field `g_stab`), `gz0_gz` (it implies `GZ Hb Gt nG` for a table below `Hb`).
* `wsClr` (`prepB ; prepLog ; prepB0 ;` the zero loop of `spPrep`) and **`wsClr_exec`**: zero
  the split's work area `[0, spWs k]` (`k` read from the frame at `r3004`) within
  `wsCost k = 30 + 12 k + 4 (spWs k + 1)` steps.
* `splitS0 = splitS ; wsClr` (the split followed by the clearing of its work area) and
  **`nspec_splR0`**, **`nspec_testR0`**: the fields `spl`, `test` of `NSpecR` with `GZ0`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Frame

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Driver

variable {I : Input} {W : ℕ}

/-- **The invariant**: the reals zero (every register, the memory below `Hb`) and the natural
memory below `Hb` zero. -/
def GZ0 (Hb : ℕ) (c : Config) : Prop :=
  (∀ r, c.rreg r = 0) ∧ (∀ a < Hb, c.rmem a = 0) ∧ ∀ a < Hb, c.nmem a = 0

theorem gz0_stab {Hb : ℕ} {c c' : Config} (h : GZ0 Hb c) (hr : c'.rreg = c.rreg)
    (hm : MemEq c c' 0 Hb) : GZ0 Hb c' :=
  ⟨fun r => by rw [hr]; exact h.1 r,
    fun a ha => by rw [(hm a (Nat.zero_le _) ha).2]; exact h.2.1 a ha,
    fun a ha => by rw [(hm a (Nat.zero_le _) ha).1]; exact h.2.2 a ha⟩

theorem gz0_gz {Hb Gt nG : ℕ} (hG : Gt + nG ≤ Hb) {c : Config} (h : GZ0 Hb c) :
    GZ Hb Gt nG c :=
  ⟨h.1, h.2.1, fun a ha => h.2.2 _ (by omega)⟩

/-- `GZ0` after a natural-only run keeping the memory below `Hb`. -/
theorem gz0_of_natOnly {Hb : ℕ} {s : Stmt} (hs : Klein.natOnly s = true) {c c' : Config}
    {t : ℕ} (e : Exec I W s c c' t) (h : GZ0 Hb c)
    (hT : ∀ a < Hb, c'.nmem a = c.nmem a) : GZ0 Hb c' := by
  obtain ⟨h1, h2⟩ := exec_reals_keep hs e
  exact ⟨fun r => by rw [h1]; exact h.1 r, fun a ha => by rw [h2]; exact h.2.1 a ha,
    fun a ha => by rw [hT a ha]; exact h.2.2 a ha⟩

/-! ### Clearing the work area of the split -/

/-- **Zero the split's work area `[0, spWs k]`** (`k` from the frame at `r3004`). -/
def wsClr : Stmt :=
  .seq prepB <| .seq prepLog <| .seq prepB0 (.whileLtN 2974 2978 prepZeroBody)

theorem wsClr_natOnly : Klein.natOnly wsClr = true := by decide

/-- The cost of `wsClr`. -/
def wsCost (k : ℕ) : ℕ := 30 + 12 * k + 4 * (spWs k + 1)

theorem wsClr_exec (c : Config) (hc : WordsBounded W c) {d m k : ℕ} (r04 : c.nreg 3004 = d)
    (hm : c.nmem (d + 1) = m) (hk : c.nmem (d + 2) = k) (w1 : d + 2 ≤ W)
    (hW : spWs k + 205 ≤ W) :
    ∃ c' t, Exec I W wsClr c c' t ∧ t ≤ wsCost k ∧ (∀ a ≤ spWs k, c'.nmem a = 0) ∧
      (∀ a, spWs k < a → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2966 ∨ 2978 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hWs : spWs k = spB0 k + 66 * k + 35 := rfl
  have hB3 : 3 * k ≤ spB0 k := by unfold spB0; omega
  obtain ⟨c₁, t₁, e₁, ht₁, p66, p67, p77, p68, p69, p70, p71, pn₁, pm₁, pr₁, prm₁, po₁⟩ :=
    prepB_exec (P := I) c hc r04 hm hk w1 (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, q71, qn₂, qm₂, qr₂, qrm₂, qo₂⟩ :=
    prepLog_exec (P := I) c₁ e₁.wb_right p66 p67 p70 p71 (by omega)
  obtain ⟨c₃, t₃, e₃, ht₃, s72, s73, s74, s78, sn₃, sm₃, sr₃, srm₃, so₃⟩ :=
    prepB0_exec (P := I) (k := k) c₂ e₂.wb_right (by rw [qn₂ _ (by omega) (by omega)]; exact p66)
      (by rw [qn₂ _ (by omega) (by omega)]; exact p67)
      (by rw [qn₂ _ (by omega) (by omega)]; exact p69)
      (by rw [q71]; congr 1; omega) hW
  obtain ⟨c₄, t₄, e₄, ht₄, z₄, k₄, n₄, r₄, rm₄, o₄⟩ :=
    prepZero_exec (P := I) c₃ e₃.wb_right
      (by rw [sn₃ _ (by omega), qn₂ _ (by omega) (by omega)]; exact p66) s74
      (by rw [sn₃ _ (by omega), qn₂ _ (by omega) (by omega)]; exact p77) s78 (by omega)
  refine ⟨c₄, t₁ + (t₂ + (t₃ + t₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), ?_, fun a ha => z₄ a
    (by omega), fun a ha => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · unfold wsCost; omega
  · rw [k₄ a (by omega), sm₃, qm₂, pm₁]
  · rw [n₄ r (by omega), sn₃ r (by omega), qn₂ r (by omega) (by omega), pn₁ r (by omega)]
  · rw [r₄, sr₃, qr₂, pr₁]
  · rw [rm₄, srm₃, qrm₂, prm₁]
  · rw [o₄, so₃, qo₂, po₁]

/-! ### The test and the split with `GZ0` -/

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {g : GIds D V} {N : CombMap D V F}

/-- **The field `test` of `NSpecR` with `GZ0`.** -/
theorem nspec_testR0 {ℓ : D → ℤ} {L Hb : ℕ} (hW6 : 1000000 ≤ W) :
    ∀ n P d e h c, GZ0 Hb c → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → InPR g N ℓ L n P d e c →
    ∃ c' t, Exec I W testS c c' t ∧ t ≤ 11 ∧ GZ0 Hb c' ∧ RegKeep c c' ∧ HeapKeep Hb h h h c c' ∧
      c'.output = c.output ∧ (c'.nreg 2997 < 1 ↔ ¬ Cnd (msplit g N) n P) := by
  intro n P d e h c hg hc r04 r05 r03 b1 b2 b3 ⟨_, hin⟩
  have hhW : h ≤ W := r03 ▸ WordsBounded.nreg hc 3003
  have he := hin.en
  unfold fsz at he
  obtain ⟨c', t, ex, ht, hcnd, hr, hn, hrr, hrm, ho⟩ :=
    testS_exec (I := I) c hc hin r04 (by omega) hW6
  exact ⟨c', t, ex, ht, gz0_of_natOnly testS_natOnly ex hg (fun a _ => by rw [hn]),
    fun r hr' => hr r (by omega) (by omega), heapKeep_of_eq hn hrm _ _ _ _, ho, hcnd⟩

/-- **The split followed by the clearing of its work area.** -/
def splitS0 : Stmt := .seq splitS wsClr

theorem splitS0_natOnly : Klein.natOnly splitS0 = true := by decide +kernel

/-- **The field `spl` of `NSpecR` with `GZ0`** (room `rSf`, cost
`splitSCost m k + wsCost k`). -/
theorem nspec_splR0 (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans) {ℓ : D → ℤ}
    {L Hb : ℕ} (hGt : spWs (Fintype.card D) < Hb) :
    ∀ n P d e h c, GZ0 Hb c → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3003 = h → Hb + 5 ≤ d → d ≤ e → e ≤ h → h + rSf P.card (ck N P) ≤ W →
    InPR g N ℓ L (n + 1) P d e c → Cnd (msplit g N) (n + 1) P →
    ∃ c' t el er, Exec I W splitS0 c c' t ∧
      t ≤ splitSCost P.card (ck N P) + wsCost (ck N P) ∧ GZ0 Hb c' ∧
      RegKeep c c' ∧ HeapKeep Hb h h h c c' ∧ c'.output = c.output ∧ c'.nreg 2998 = el ∧
      c'.nreg 2999 = er ∧ h + 5 ≤ el ∧ el + 5 ≤ er ∧ er ≤ h + rSf P.card (ck N P) ∧
      InPR g N ℓ L n (msplit g N P).1 (h + 5) el c' ∧
      InPR g N ℓ L n (msplit g N P).2 (el + 5) er c' := by
  intro n P d e h c hg hc r04 r05 r03 b1 b2 b3 hroom ⟨hPr, hin⟩ _
  have hws : spWs (ck N P) ≤ spWs (Fintype.card D) := spWs_mono (ck_le_card P)
  have he := hin.en
  unfold fsz at he
  obtain ⟨c', t, el, er, ex, ht, rk, hk, ho, s98, s99, hel, her, i0, i1, rr, rm⟩ :=
    splitS_exec' (I := I) (Hb := Hb) hM hrot hface hPr c hc hin r04 r03 (by omega) (by omega) b3
      (fun r _ => hg.1 r) (fun a ha => hg.2.1 a (by omega)) (by unfold rSf at hroom; unfold fsz at hroom ⊢; omega)
  have hin' : InP g N ℓ L (n + 1) P d e c' := inP_stab hin fun a h1 h2 =>
    hk a (by omega) (by omega)
  obtain ⟨c'', t', ex', ht', z, km, kn, kr, krm, ko⟩ :=
    wsClr_exec (I := I) c' ex.wb_right (by rw [rk 3004 (by omega)]; exact r04) hin'.rm hin'.rk
      (by omega) (by unfold rSf at hroom; unfold fsz at hroom; omega)
  have hP0 : (msplit g N P).1 ⊆ P := filter_subset _ _
  have hP1 : (msplit g N P).2 ⊆ P := filter_subset _ _
  have e0 := i0.en
  have e1 := i1.en
  have hk0 : ck N (msplit g N P).1 ≤ ck N P := card_le_card (rcl_mono' hP0)
  have hk1 : ck N (msplit g N P).2 ≤ ck N P := card_le_card (rcl_mono' hP1)
  have hm0 := card_le_card hP0
  have hm1 := card_le_card hP1
  have hmk := ck_ge (N := N) P
  unfold fsz at e0 e1
  have K : ∀ a, spWs (ck N P) < a → c''.nmem a = c'.nmem a := km
  refine ⟨c'', t + t', el, er, .seq ex ex', by omega, ?_, fun r hr => ?_,
    fun a h1 h2 _ => ?_, by rw [ko, ho], by rw [kn _ (by omega)]; exact s98,
    by rw [kn _ (by omega)]; exact s99, hel, her, by unfold rSf fsz; omega,
    ⟨hP0.trans hPr, inP_stab i0 fun a h1 h2 => ⟨K a (by omega), by rw [krm]⟩⟩,
    ⟨hP1.trans hPr, inP_stab i1 fun a h1 h2 => ⟨K a (by omega), by rw [krm]⟩⟩⟩
  · obtain ⟨h1, h2⟩ := exec_reals_keep splitS0_natOnly (Exec.seq ex ex')
    refine ⟨fun r => by rw [h1]; exact hg.1 r, fun a ha => by rw [h2]; exact hg.2.1 a ha,
      fun a ha => ?_⟩
    by_cases h : a ≤ spWs (ck N P)
    · exact z a h
    · rw [K a (by omega), (hk a (by omega) (by omega)).1]; exact hg.2.2 a ha
  · rw [kn r (by omega)]; exact rk r hr
  · exact ⟨by rw [K a (by omega)]; exact (hk a (by omega) h2).1,
      by rw [krm]; exact (hk a (by omega) h2).2⟩

end Frame

end NegSSSP

end PlanarFlow
