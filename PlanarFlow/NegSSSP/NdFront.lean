module

public import PlanarFlow.NegSSSP.NdDrive0

/-!
# The node step: the front (the sides, the children's outcome regions, the flags)

The node step starts by re-running the canonical split of its piece `P` (`spStage`: the side of
every dart, `0` exactly on `(msplit g N P).1`), counts the darts of the first part
(`m₀ = #(msplit g N P).1`), locates the children's outcome regions from the ends of their frames
(`R₀ = el − 4 m₀ − 2 = (bl + 5) + fin m₀ k₀`, `R₁ = er − 4 m₁ − 2`), reads their flags, and clears
the split's work area again (`wsClr`):

* `ndA1`, `ndCntB`, `ndA2`, **`ndA`** (registers `2472 … 2486`), the block lemmas,
  `card_side`, `msplit_card`;
* **`ndFront_exec`**: `spStage ; ndA ; wsClr` within `prepCost k + splitT k + 7m + 33 +
  wsCost k` steps, with `r2479 = m₀`, `r2481 = m₁`, `r2482 = R₀`, `r2485 = R₁`,
  `r2486 = mem[R₀] + mem[R₁]`, `GZ0` kept, the memory from `Hb` on kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Frame

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Driver

variable {I : Input} {W : ℕ}

/-- The constants, `m`, `k`, `L` from the frame at `r3004`, the base `S` of the sides. -/
def ndA1 : Stmt := block [.constN 2472 1, .constN 2473 0, .addN 2480 3004 2472, .loadN 2474 2480,
  .addN 2480 2480 2472, .loadN 2475 2480, .addN 2480 2480 2472, .loadN 2476 2480,
  .constN 2483 41, .mulN 2477 2483 2969, .addN 2477 2477 2972, .constN 2483 4,
  .addN 2477 2477 2483, .constN 2478 0, .constN 2479 0]

/-- `m₀ += 1 − side[x]`. -/
def ndCntB : Stmt := block [.addN 2480 2477 2478, .loadN 2480 2480, .subN 2480 2472 2480,
  .addN 2479 2479 2480, .addN 2478 2478 2472]

/-- `m₁`, `R₀ = el − 4 m₀ − 2`, `R₁ = er − 4 m₁ − 2`, the sum of the flags. -/
def ndA2 : Stmt := block [.subN 2481 2474 2479, .constN 2483 4, .mulN 2484 2483 2479,
  .subN 2482 3007 2484, .constN 2483 2, .subN 2482 2482 2483, .constN 2483 4,
  .mulN 2484 2483 2481, .subN 2485 3009 2484, .constN 2483 2, .subN 2485 2485 2483,
  .loadN 2486 2482, .divN 2486 2486 2486, .loadN 2484 2485, .divN 2484 2484 2484,
  .addN 2486 2486 2484]

/-- **The front of the node after the split.** -/
def ndA : Stmt := .seq ndA1 (.seq (.whileLtN 2478 2474 ndCntB) ndA2)

theorem ndA1_exec (c : Config) (hc : WordsBounded W c) {d m k L B : ℕ} (r04 : c.nreg 3004 = d)
    (r69 : c.nreg 2969 = k) (r72 : c.nreg 2972 = B) (m1 : c.nmem (d + 1) = m)
    (m2 : c.nmem (d + 2) = k) (m3 : c.nmem (d + 3) = L) (w1 : d + 3 ≤ W)
    (w2 : B + 41 * k + 4 ≤ W) (w0 : 41 ≤ W) :
    ∃ c' t, Exec I W ndA1 c c' t ∧ t = 15 ∧ c'.nreg 2472 = 1 ∧ c'.nreg 2473 = 0 ∧
      c'.nreg 2474 = m ∧ c'.nreg 2475 = k ∧ c'.nreg 2476 = L ∧
      c'.nreg 2477 = B + 41 * k + 4 ∧ c'.nreg 2478 = 0 ∧ c'.nreg 2479 = 0 ∧
      (∀ r, (r < 2472 ∨ 2483 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hm : m ≤ W := m1 ▸ WordsBounded.nmem hc _
  unfold ndA1
  exec_block
  all_goals try ((try config_simp); (try simp only [r04, r69, r72, m1, m2, m3]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r04, r69, r72, m1, m2, m3])
  all_goals first | omega | (simp (disch := omega) only [upd_other])

theorem ndCntB_exec (c : Config) (hc : WordsBounded W c) {S x n s : ℕ} (r72 : c.nreg 2472 = 1)
    (r77 : c.nreg 2477 = S) (r78 : c.nreg 2478 = x) (r79 : c.nreg 2479 = n)
    (ms : c.nmem (S + x) = s) (w1 : S + x ≤ W) (w2 : n + 1 ≤ W) (w3 : x + 1 ≤ W) :
    ∃ c' t, Exec I W ndCntB c c' t ∧ t = 5 ∧ c'.nreg 2478 = x + 1 ∧ c'.nreg 2479 = n + (1 - s) ∧
      (∀ r, r ≠ 2478 → r ≠ 2479 → r ≠ 2480 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ndCntB
  exec_block
  all_goals try ((try config_simp); (try simp only [r72, r77, r78, r79, ms]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r72, r77, r78, r79, ms])
  all_goals first | omega | (simp (disch := omega) only [upd_other])

/-- **The count of the darts of side `0`.** -/
theorem ndCnt_exec (c : Config) (hc : WordsBounded W c) {S m : ℕ} (r72 : c.nreg 2472 = 1)
    (r74 : c.nreg 2474 = m) (r77 : c.nreg 2477 = S) (r78 : c.nreg 2478 = 0)
    (r79 : c.nreg 2479 = 0) (hs : ∀ x < m, c.nmem (S + x) ≤ 1) (w1 : S + m ≤ W)
    (w2 : m + 1 ≤ W) :
    ∃ c' t, Exec I W (.whileLtN 2478 2474 ndCntB) c c' t ∧ t ≤ 7 * m + 2 ∧
      c'.nreg 2479 = ((range m).filter fun x => c.nmem (S + x) = 0).card ∧
      (∀ r, r ≠ 2478 → r ≠ 2479 → r ≠ 2480 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun i c' =>
    c'.nreg 2479 = ((range i).filter fun x => c.nmem (S + x) = 0).card ∧
      (∀ r, r ≠ 2478 → r ≠ 2479 → r ≠ 2480 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := I) (a := 2478) (bR := 2474)
    (body := ndCntB) J (K := 5) (n := m) c hc r78 r74
    ⟨by rw [r79]; simp, fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, jn, jm, jr, jrm, jo⟩ := hJ
      have hcnt : ((range i).filter fun x => c.nmem (S + x) = 0).card ≤ i := by
        have := card_filter_le (range i) (fun x => c.nmem (S + x) = 0)
        rw [card_range] at this; exact this
      obtain ⟨c'', t, ex, ht, h78, h79, hn, hm, hr, hrm, ho⟩ :=
        ndCntB_exec (I := I) c' hw ((jn 2472 (by omega) (by omega) (by omega)).trans r72)
          ((jn 2477 (by omega) (by omega) (by omega)).trans r77) ha j1
          (by rw [jm]) (by omega) (by omega) (by omega)
      refine ⟨c'', t, ex, by omega, h78, (hn 2474 (by omega) (by omega) (by omega)).trans hb,
        ?_, fun r h1 h2 h3 => (hn r h1 h2 h3).trans (jn r h1 h2 h3), by rw [hm, jm],
        by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩
      rw [h79, range_add_one, filter_insert]
      have := hs i hi
      by_cases h0 : c.nmem (S + i) = 0
      · rw [if_pos h0, card_insert_of_notMem (by simp), h0]
      · rw [if_neg h0]; omega)
  obtain ⟨j1, jn, jm, jr, jrm, jo⟩ := hJ
  exact ⟨c₂, k₂, e₂, by omega, j1, jn, jm, jr, jrm, jo⟩

theorem ndA2_exec (c : Config) (hc : WordsBounded W c) {m n el er : ℕ}
    (r74 : c.nreg 2474 = m) (r79 : c.nreg 2479 = n) (r07 : c.nreg 3007 = el)
    (r09 : c.nreg 3009 = er) (hn : n ≤ m) (h0 : 4 * n + 2 ≤ el) (h1 : 4 * (m - n) + 2 ≤ er)
    (w1 : 4 * m + 2 ≤ W) (w0 : 4 ≤ W) :
    ∃ c' t, Exec I W ndA2 c c' t ∧ t = 16 ∧ c'.nreg 2481 = m - n ∧
      c'.nreg 2482 = el - 4 * n - 2 ∧ c'.nreg 2485 = er - 4 * (m - n) - 2 ∧
      c'.nreg 2486 = c.nmem (el - 4 * n - 2) / c.nmem (el - 4 * n - 2) +
        c.nmem (er - 4 * (m - n) - 2) / c.nmem (er - 4 * (m - n) - 2) ∧
      (∀ r, (r < 2481 ∨ 2486 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have i0 : ∀ x : ℕ, x / x ≤ 1 := fun x => by
    rcases Nat.eq_zero_or_pos x with h | h
    · subst h; simp
    · rw [Nat.div_self h]
  have j0 := i0 (c.nmem (el - 4 * n - 2))
  have j1 := i0 (c.nmem (er - 4 * (m - n) - 2))
  unfold ndA2
  exec_block
  all_goals try ((try config_simp); (try simp only [r74, r79, r07, r09]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r74, r79, r07, r09])
  all_goals first | omega | (congr 1; omega) | (simp (disch := omega) only [upd_other]) |
    (congr 2 <;> omega)

/-! ### Counting the darts of a part -/

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {g : GIds D V} {N : CombMap D V F}

/-- The count of the darts of side `0` is the size of the part. -/
theorem card_side {P Q : Finset D} (hQ : Q ⊆ P) {s : ℕ → ℕ}
    (hs : ∀ x < P.card, (s x = 0 ↔ cδ g N P x ∈ Q)) :
    ((range P.card).filter fun x => s x = 0).card = Q.card := by
  have hinj : Set.InjOn (cδ g N P) ((range P.card).filter fun x => s x = 0 : Set ℕ) := by
    intro a ha b hb e
    simp only [coe_filter, mem_range, Set.mem_setOf_eq] at ha hb
    have hk := ck_ge (N := N) P
    exact cδ_inj (by unfold ck at hk; omega) (by unfold ck at hk; omega) e
  rw [← card_image_of_injOn hinj]
  congr 1
  ext y
  simp only [mem_image, mem_filter, mem_range]
  constructor
  · rintro ⟨x, ⟨hx, h0⟩, rfl⟩
    exact (hs x hx).1 h0
  · intro hy
    obtain ⟨h1, h2⟩ := cδ_idxOf (g := g) (N := N) (hQ hy)
    exact ⟨_, ⟨h1, (hs _ h1).2 (by rw [h2]; exact hy)⟩, h2⟩

theorem msplit_card (P : Finset D) :
    (msplit g N P).1.card + (msplit g N P).2.card = P.card := by
  rw [← card_union_of_disjoint, msplit_union]
  unfold msplit
  exact disjoint_filter_filter_not P P _

/-- The front of the node: the split, the counts and flags, the clearing. -/
def ndFront : Stmt := .seq spStage (.seq ndA wsClr)

theorem ndFront_natOnly : Klein.natOnly ndFront = true := by decide +kernel

/-- The indicator `x / x` of `x ≠ 0`. -/
theorem ind_eq (x : ℕ) : x / x = if x = 0 then 0 else 1 := by
  rcases Nat.eq_zero_or_pos x with h | h
  · subst h; simp
  · rw [Nat.div_self h, if_neg (by omega)]

set_option maxHeartbeats 4000000 in
/-- **The front of the node step.** -/
theorem ndFront_exec (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans) {ℓ : D → ℤ}
    {L n : ℕ} {P : Finset D} (hPr : P ⊆ reps N) {d e bl el er Hb : ℕ} (c : Config)
    (hc : WordsBounded W c) (hg : GZ0 Hb c) (hin : InP g N ℓ L (n + 1) P d e c)
    (r04 : c.nreg 3004 = d) (r07 : c.nreg 3007 = el) (r09 : c.nreg 3009 = er)
    (hHb : spWs (ck N P) < Hb) (b1 : Hb + 5 ≤ d) (b3 : e ≤ bl)
    (hel : el = bl + 5 + fsz (msplit g N P).1.card (ck N (msplit g N P).1))
    (her : er = el + 5 + fsz (msplit g N P).2.card (ck N (msplit g N P).2))
    (hW : er ≤ W) (hW2 : spWs (ck N P) + 205 ≤ W) (h41 : 41 ≤ W) :
    ∃ c' t, Exec I W ndFront c c' t ∧
      t ≤ prepCost (ck N P) + splitT (ck N P) + (7 * P.card + 33) + wsCost (ck N P) ∧
      c'.nreg 2472 = 1 ∧ c'.nreg 2473 = 0 ∧ c'.nreg 2474 = P.card ∧ c'.nreg 2475 = ck N P ∧
      c'.nreg 2476 = L ∧ c'.nreg 2479 = (msplit g N P).1.card ∧
      c'.nreg 2481 = (msplit g N P).2.card ∧
      c'.nreg 2482 = bl + 5 + fin (msplit g N P).1.card (ck N (msplit g N P).1) ∧
      c'.nreg 2485 = el + 5 + fin (msplit g N P).2.card (ck N (msplit g N P).2) ∧
      c'.nreg 2486 =
        c.nmem (bl + 5 + fin (msplit g N P).1.card (ck N (msplit g N P).1)) /
          c.nmem (bl + 5 + fin (msplit g N P).1.card (ck N (msplit g N P).1)) +
        c.nmem (el + 5 + fin (msplit g N P).2.card (ck N (msplit g N P).2)) /
          c.nmem (el + 5 + fin (msplit g N P).2.card (ck N (msplit g N P).2)) ∧
      (∀ r, ((972 ≤ r ∧ r < 2472) ∨ (2486 < r ∧ r < 2966) ∨ 2980 < r) →
        c'.nreg r = c.nreg r) ∧
      GZ0 Hb c' ∧ (∀ a, Hb ≤ a → c'.nmem a = c.nmem a) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  set P₀ := (msplit g N P).1 with hP₀
  set P₁ := (msplit g N P).2 with hP₁
  have hmk : P.card ≤ (ck N P) := ck_ge P
  have he := hin.en
  unfold fsz at he hel her
  have hWs : spWs (ck N P) = spB0 (ck N P) + 66 * (ck N P) + 35 := rfl
  have hB3 : 3 * (ck N P) ≤ spB0 (ck N P) := by unfold spB0; omega
  have hcard := msplit_card (g := g) (N := N) P
  rw [← hP₀, ← hP₁] at hcard
  -- the split
  obtain ⟨c₁, t₁, e₁, ht₁, hside, p66, p69, p72, m₁, n₁, rr₁, rm₁, o₁⟩ :=
    spStage_exec (P := I) hM hrot hface hPr c hc hin r04 (by omega) (fun r _ => hg.1 r)
      (fun a ha => hg.2.1 a (by omega)) (by omega) hW2
  have M1 : ∀ a, spWs (ck N P) < a → c₁.nmem a = c.nmem a := m₁
  -- the constants
  obtain ⟨c₂, t₂, e₂, ht₂, a72, a73, a74, a75, a76, a77, a78, a79, an₂, am₂, ar₂, arm₂, ao₂⟩ :=
    ndA1_exec (I := I) c₁ e₁.wb_right (d := d) (m := P.card) (k := ck N P) (L := L)
      (by rw [n₁ _ (by omega) (by omega)]; exact r04) p69 p72
      (by rw [M1 _ (by omega)]; exact hin.rm) (by rw [M1 _ (by omega)]; exact hin.rk)
      (by rw [M1 _ (by omega)]; exact hin.rL) (by omega) (by omega) h41
  -- the count
  obtain ⟨c₃, t₃, e₃, ht₃, b79, bn₃, bm₃, br₃, brm₃, bo₃⟩ :=
    ndCnt_exec (I := I) c₂ e₂.wb_right a72 a74 a77 a78 a79
      (fun x hx => by rw [am₂]; exact (hside x hx).2.2) (by omega) (by omega)
  have hcnt : ((range P.card).filter fun x =>
      c₂.nmem (spB0 (ck N P) + 41 * (ck N P) + 4 + x) = 0).card = P₀.card :=
    card_side (filter_subset _ _) fun x hx => by rw [am₂]; exact (hside x hx).1
  rw [hcnt] at b79
  -- the regions
  obtain ⟨c₄, t₄, e₄, ht₄, d81, d82, d85, d86, dn₄, dm₄, dr₄, drm₄, do₄⟩ :=
    ndA2_exec (I := I) c₃ e₃.wb_right (m := P.card) (n := P₀.card) (el := el) (er := er)
      (by rw [bn₃ _ (by omega) (by omega) (by omega)]; exact a74) b79
      (by rw [bn₃ _ (by omega) (by omega) (by omega), an₂ _ (by omega),
        n₁ _ (by omega) (by omega)]; exact r07)
      (by rw [bn₃ _ (by omega) (by omega) (by omega), an₂ _ (by omega),
        n₁ _ (by omega) (by omega)]; exact r09)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  have eR₀ : el - 4 * P₀.card - 2 = bl + 5 + fin P₀.card (ck N P₀) := by unfold fin; omega
  have eR₁ : er - 4 * (P.card - P₀.card) - 2 = el + 5 + fin P₁.card (ck N P₁) := by
    unfold fin; omega
  rw [eR₀, eR₁] at d86
  rw [eR₀] at d82
  rw [eR₁] at d85
  have M4 : ∀ a, spWs (ck N P) < a → c₄.nmem a = c.nmem a := fun a ha => by
    rw [dm₄, bm₃, am₂, M1 a ha]
  -- the clearing
  have hin₄ : InP g N ℓ L (n + 1) P d e c₄ := inP_stab hin fun a h1 h2 =>
    ⟨M4 a (by omega), by rw [drm₄, brm₃, arm₂, rm₁ a (by omega)]⟩
  have R4 : ∀ r, 3000 ≤ r → c₄.nreg r = c.nreg r := fun r hr => by
    rw [dn₄ r (by omega), bn₃ r (by omega) (by omega) (by omega), an₂ r (by omega),
      n₁ r (by omega) (by omega)]
  obtain ⟨c₅, t₅, e₅, ht₅, z₅, k₅, n₅, r₅, rm₅, o₅⟩ :=
    wsClr_exec (I := I) c₄ e₄.wb_right (by rw [R4 _ (by omega)]; exact r04) hin₄.rm hin₄.rk
      (by omega) hW2
  have ex : Exec I W ndFront c c₅ (t₁ + (t₂ + (t₃ + t₄) + t₅)) :=
    .seq e₁ (.seq (.seq e₂ (.seq e₃ e₄)) e₅)
  obtain ⟨hrr, hrm⟩ := exec_reals_keep ndFront_natOnly ex
  have K5 : ∀ r, ((972 ≤ r ∧ r < 2472) ∨ (2486 < r ∧ r < 2966) ∨ 2980 < r) →
      c₅.nreg r = c.nreg r := fun r hr => by
    rw [n₅ r (by omega), dn₄ r (by omega), bn₃ r (by omega) (by omega) (by omega),
      an₂ r (by omega), n₁ r (by omega) (by omega)]
  refine ⟨c₅, _, ex, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, K5,
    ⟨fun r => by rw [hrr]; exact hg.1 r, fun a ha => by rw [hrm]; exact hg.2.1 a ha,
      fun a ha => ?_⟩, fun a ha => ?_, hrr, hrm, by rw [o₅, do₄, bo₃, ao₂, o₁]⟩
  · rw [n₅ 2472 (by omega), dn₄ 2472 (by omega), bn₃ 2472 (by omega) (by omega) (by omega)]
    exact a72
  · rw [n₅ 2473 (by omega), dn₄ 2473 (by omega), bn₃ 2473 (by omega) (by omega) (by omega)]
    exact a73
  · rw [n₅ 2474 (by omega), dn₄ 2474 (by omega), bn₃ 2474 (by omega) (by omega) (by omega)]
    exact a74
  · rw [n₅ 2475 (by omega), dn₄ 2475 (by omega), bn₃ 2475 (by omega) (by omega) (by omega)]
    exact a75
  · rw [n₅ 2476 (by omega), dn₄ 2476 (by omega), bn₃ 2476 (by omega) (by omega) (by omega)]
    exact a76
  · rw [n₅ 2479 (by omega), dn₄ 2479 (by omega)]; exact b79
  · rw [n₅ 2481 (by omega), d81]; omega
  · rw [n₅ 2482 (by omega)]; exact d82
  · rw [n₅ 2485 (by omega)]; exact d85
  · rw [n₅ 2486 (by omega), d86, bm₃, am₂, M1 _ (by unfold fin; omega),
      M1 _ (by unfold fin; omega)]
  · by_cases h : a ≤ spWs (ck N P)
    · exact z₅ a h
    · rw [k₅ a (by omega), M4 a (by omega)]; exact hg.2.2 a ha
  · rw [k₅ a (by omega), M4 a (by omega)]

end Frame

end NegSSSP

end PlanarFlow
