module

public import PlanarFlow.Monge.FRSearch

/-!
# FR-Dijkstra on the machine: writing and clearing triplets

The effect of the two writes of the triplet structure on its representation `TMem`, with a
*hole* `H` (rows not extracted, not recorded):

* `TMem.clr`: clearing the start `x` moves its rows `[x, tEnd x]` to the hole;
* `TMem.set`: writing a start `x` with the last row `y` (the rows `[x, y]` in the hole, one owner)
  moves them out of the hole;
* `TMem.rearr`, `TMem.congr_own`, `TMem.congr_e`, `TMem.congr_mem`: moving rows between the hole
  and the extracted rows, changing the owners of uncovered rows, the entries of non-owners, and
  the memory outside the structure.

The routines `tPut` (a new triplet `[j1, j2)` with the owner `σ`, its least entry by a query
`rmq`) and `tDel` (clear a start), with their specifications `tPut_exec`, `tDel_exec`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace FR

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Heap

/-- The records of the rows other than `x` are the same in `nm, rm` and `nm', rm'`. -/
def RecEq (Q s x : ℕ) (nm nm' : ℕ → ℕ) (rm rm' : ℕ → ℝ) : Prop :=
  ∀ z < s, z ≠ x → tPr Q nm' z = tPr Q nm z ∧ tOwn Q nm' z = tOwn Q nm z ∧
    tEnd Q nm' z = tEnd Q nm z ∧ tMin Q nm' z = tMin Q nm z ∧ tKey Q rm' z = tKey Q rm z

lemma recEq_of {Q s x : ℕ} {nm nm' : ℕ → ℕ} {rm rm' : ℕ → ℝ}
    (hn : ∀ a, a < Q + 8 * s → a ≠ Q + 8 * x → a ≠ Q + 8 * x + 1 → a ≠ Q + 8 * x + 2 →
      a ≠ Q + 8 * x + 5 → nm' a = nm a)
    (hr : ∀ a, a ≠ Q + 8 * x → rm' a = rm a) : RecEq Q s x nm nm' rm rm' := by
  intro z hz hzx
  unfold tPr tOwn tEnd tMin tKey
  refine ⟨hn _ ?_ ?_ ?_ ?_ ?_, hn _ ?_ ?_ ?_ ?_ ?_, hn _ ?_ ?_ ?_ ?_ ?_, hn _ ?_ ?_ ?_ ?_ ?_,
    hr _ ?_⟩ <;> omega

section mem

variable {s nr : ℕ} {F : ℕ → ℕ → ℝ} {e : ℕ → ℝ} {own : ℕ → ℕ} {X H : ℕ → Prop} {Q : ℕ}
  {nm : ℕ → ℕ} {rm : ℕ → ℝ}

/-- A start is not in the hole. -/
lemma TMem.not_hole (h : TMem s nr F e own X H Q nm rm) {x : ℕ} (hx : x < s)
    (hpx : tPr Q nm x = 1) {ρ : ℕ} (h1 : x ≤ ρ) (h2 : ρ ≤ tEnd Q nm x) : ¬ X ρ ∧ ¬ H ρ := by
  have := (h.st x hx hpx).2
  exact (h.cover ρ (by omega)).2 ⟨x, hx, hpx, h1, h2⟩

/-- **Clearing the start `x`** moves its rows to the hole. -/
theorem TMem.clr (h : TMem s nr F e own X H Q nm rm) {x : ℕ} (hx : x < s)
    (hpx : tPr Q nm x = 1) {nm' : ℕ → ℕ} {rm' : ℕ → ℝ} (hpr : tPr Q nm' x = 0)
    (hrec : RecEq Q s x nm nm' rm rm')
    (hW : WinOK s (tPr Q nm') (tKey Q rm') (tWn Q s nm') 0)
    (hWl : WinOK s (tPr Q nm') (fun x => (x : ℝ)) (tWl Q s nm') 0) :
    TMem s nr F e own X (fun ρ => H ρ ∨ (x ≤ ρ ∧ ρ ≤ tEnd Q nm x)) Q nm' rm' := by
  have hst := h.st x hx hpx
  have pz : ∀ z < s, tPr Q nm' z = 1 → z ≠ x ∧ tPr Q nm z = 1 := fun z hz hp => by
    by_cases e : z = x
    · subst e; omega
    · exact ⟨e, (hrec z hz e).1 ▸ hp⟩
  refine ⟨h.nr_le, fun z hz => ?_, fun z hz hp => ?_, fun ρ hρ => ⟨fun ⟨h1, h2⟩ => ?_, ?_⟩,
    fun ρ => ?_, fun y z hyz hz hy hz' => ?_, fun z hz hp ρ h1 h2 => ?_,
    fun z hz hp => ?_, hW, hWl⟩
  · by_cases e : z = x
    · subst e; omega
    · rw [(hrec z hz e).1]; exact h.pr01 z hz
  · obtain ⟨e, hp'⟩ := pz z hz hp
    rw [(hrec z hz e).2.2.1]; exact h.st z hz hp'
  · obtain ⟨z, hz, hp, hz1, hz2⟩ := (h.cover ρ hρ).1 ⟨h1, fun h' => h2 (Or.inl h')⟩
    have hzx : z ≠ x := fun e => h2 (Or.inr (e ▸ ⟨hz1, hz2⟩))
    obtain ⟨r1, -, r2, -⟩ := hrec z hz hzx
    exact ⟨z, hz, r1 ▸ hp, hz1, r2 ▸ hz2⟩
  · rintro ⟨z, hz, hp, hz1, hz2⟩
    obtain ⟨hzx, hp'⟩ := pz z hz hp
    obtain ⟨-, -, r2, -⟩ := hrec z hz hzx
    rw [r2] at hz2
    obtain ⟨n1, n2⟩ := h.not_hole hz hp' hz1 hz2
    refine ⟨n1, fun h' => h'.elim n2 fun ⟨i1, i2⟩ => ?_⟩
    rcases Nat.lt_or_gt_of_ne hzx with hzx | hzx
    · have := h.disj z x hzx hx hp' hpx; omega
    · have := h.disj x z hzx hz hpx hp'; omega
  · rintro (h' | ⟨i1, i2⟩)
    · exact h.hole ρ h'
    · exact ⟨by omega, (h.not_hole hx hpx i1 i2).1⟩
  · obtain ⟨hyx, hy'⟩ := pz y (by omega) hy
    obtain ⟨hzx, hz''⟩ := pz z hz hz'
    rw [(hrec y (by omega) hyx).2.2.1]; exact h.disj y z hyz hz hy' hz''
  · obtain ⟨hzx, hp'⟩ := pz z hz hp
    obtain ⟨-, r1, r2, -⟩ := hrec z hz hzx
    rw [r1]; rw [r2] at h2; exact h.own z hz hp' ρ h1 h2
  · obtain ⟨hzx, hp'⟩ := pz z hz hp
    obtain ⟨-, r1, r2, r3, r4⟩ := hrec z hz hzx
    rw [r1, r2, r3, r4]; exact h.mn z hz hp'

/-- **Writing the start `x`** with the last row `y`, the owner `o` and the least entry at the
row `m`, for rows `[x, y]` of the hole owned by `o`, moves them out of the hole. -/
theorem TMem.set (h : TMem s nr F e own X H Q nm rm) {x y m o : ℕ} (hx : x < s) (hxy : x ≤ y)
    (hy : y < nr) (hH : ∀ ρ, x ≤ ρ → ρ ≤ y → H ρ) (ho : ∀ ρ, x ≤ ρ → ρ ≤ y → own ρ = o)
    (hm1 : x ≤ m) (hm2 : m ≤ y) (hmin : ∀ ρ, x ≤ ρ → ρ ≤ y → F m o ≤ F ρ o)
    {nm' : ℕ → ℕ} {rm' : ℕ → ℝ} (hpr : tPr Q nm' x = 1) (hown : tOwn Q nm' x = o)
    (hend : tEnd Q nm' x = y) (hmn : tMin Q nm' x = m) (hkey : tKey Q rm' x = e o + F m o)
    (hrec : RecEq Q s x nm nm' rm rm')
    (hW : WinOK s (tPr Q nm') (tKey Q rm') (tWn Q s nm') 0)
    (hWl : WinOK s (tPr Q nm') (fun x => (x : ℝ)) (tWl Q s nm') 0) :
    TMem s nr F e own X (fun ρ => H ρ ∧ ¬ (x ≤ ρ ∧ ρ ≤ y)) Q nm' rm' := by
  have hHx := hH x le_rfl hxy
  -- the old starts other than `x`
  have pz : ∀ z < s, z ≠ x → tPr Q nm' z = 1 → tPr Q nm z = 1 := fun z hz e hp =>
    (hrec z hz e).1 ▸ hp
  -- an old start does not reach the rows `[x, y]`
  have far : ∀ z < s, tPr Q nm z = 1 → ∀ ρ, x ≤ ρ → ρ ≤ y → ¬ (z ≤ ρ ∧ ρ ≤ tEnd Q nm z) :=
    fun z hz hp ρ h1 h2 ⟨i1, i2⟩ => (h.not_hole hz hp i1 i2).2 (hH ρ h1 h2)
  refine ⟨h.nr_le, fun z hz => ?_, fun z hz hp => ?_, fun ρ hρ => ⟨fun ⟨h1, h2⟩ => ?_, ?_⟩,
    fun ρ hρ => h.hole ρ hρ.1, fun y' z hyz hz hy' hz' => ?_, fun z hz hp ρ h1 h2 => ?_,
    fun z hz hp => ?_, hW, hWl⟩
  · by_cases e : z = x
    · subst e; omega
    · rw [(hrec z hz e).1]; exact h.pr01 z hz
  · by_cases e : z = x
    · subst e; rw [hend]; exact ⟨hxy, hy⟩
    · rw [(hrec z hz e).2.2.1]; exact h.st z hz (pz z hz e hp)
  · by_cases hin : x ≤ ρ ∧ ρ ≤ y
    · exact ⟨x, hx, hpr, hin.1, by rw [hend]; exact hin.2⟩
    · obtain ⟨z, hz, hp, hz1, hz2⟩ := (h.cover ρ hρ).1 ⟨h1, fun h' => h2 ⟨h', hin⟩⟩
      have hzx : z ≠ x := fun e =>
        (h.not_hole hz hp le_rfl (h.st z hz hp).1).2 (e ▸ hHx)
      obtain ⟨r1, -, r2, -⟩ := hrec z hz hzx
      exact ⟨z, hz, r1 ▸ hp, hz1, r2 ▸ hz2⟩
  · rintro ⟨z, hz, hp, hz1, hz2⟩
    by_cases e : z = x
    · subst e
      rw [hend] at hz2
      exact ⟨(h.hole ρ (hH ρ hz1 hz2)).2, fun h' => h'.2 ⟨hz1, hz2⟩⟩
    · rw [(hrec z hz e).2.2.1] at hz2
      obtain ⟨n1, n2⟩ := h.not_hole hz (pz z hz e hp) hz1 hz2
      exact ⟨n1, fun h' => n2 h'.1⟩
  · by_cases ey : y' = x
    · subst ey
      have hzx : z ≠ y' := by omega
      rw [hend]
      by_contra hc
      exact far z hz (pz z hz hzx hz') z (by omega) (by omega)
        ⟨le_rfl, (h.st z hz (pz z hz hzx hz')).1⟩
    · by_cases ez : z = x
      · subst ez
        rw [(hrec y' (by omega) ey).2.2.1]
        by_contra hc
        exact far y' (by omega) (pz y' (by omega) ey hy') z le_rfl hxy ⟨by omega, by omega⟩
      · rw [(hrec y' (by omega) ey).2.2.1]
        exact h.disj y' z hyz hz (pz y' (by omega) ey hy') (pz z hz ez hz')
  · by_cases e : z = x
    · subst e; rw [hown]; rw [hend] at h2; exact ho ρ h1 h2
    · obtain ⟨-, r1, r2, -⟩ := hrec z hz e
      rw [r1]; rw [r2] at h2; exact h.own z hz (pz z hz e hp) ρ h1 h2
  · by_cases e : z = x
    · subst e
      rw [hmn, hend, hown, hkey]
      exact ⟨hm1, hm2, rfl, hmin⟩
    · obtain ⟨-, r1, r2, r3, r4⟩ := hrec z hz e
      rw [r1, r2, r3, r4]; exact h.mn z hz (pz z hz e hp)

/-- Moving rows between the hole and the extracted rows. -/
theorem TMem.rearr (h : TMem s nr F e own X H Q nm rm) {X' H' : ℕ → Prop}
    (hXH : ∀ ρ < nr, (X' ρ ∨ H' ρ) ↔ (X ρ ∨ H ρ)) (hH' : ∀ ρ, H' ρ → ρ < nr ∧ ¬ X' ρ) :
    TMem s nr F e own X' H' Q nm rm :=
  ⟨h.nr_le, h.pr01, h.st, fun ρ hρ => by
    rw [← h.cover ρ hρ, ← not_or, ← not_or, hXH ρ hρ], hH', h.disj, h.own, h.mn, h.win, h.wl⟩

/-- The owners of the rows not covered do not matter. -/
theorem TMem.congr_own (h : TMem s nr F e own X H Q nm rm) {own' : ℕ → ℕ}
    (ho : ∀ ρ < nr, ¬ X ρ → ¬ H ρ → own' ρ = own ρ) : TMem s nr F e own' X H Q nm rm := by
  refine ⟨h.nr_le, h.pr01, h.st, h.cover, h.hole, h.disj, fun x hx hp ρ h1 h2 => ?_, h.mn, h.win,
    h.wl⟩
  have := (h.st x hx hp).2
  obtain ⟨n1, n2⟩ := h.not_hole hx hp h1 h2
  rw [ho ρ (by omega) n1 n2]; exact h.own x hx hp ρ h1 h2

/-- The entries of the sources that own no triplet do not matter. -/
theorem TMem.congr_e (h : TMem s nr F e own X H Q nm rm) {e' : ℕ → ℝ}
    (he : ∀ x < s, tPr Q nm x = 1 → e' (tOwn Q nm x) = e (tOwn Q nm x)) :
    TMem s nr F e' own X H Q nm rm := by
  refine ⟨h.nr_le, h.pr01, h.st, h.cover, h.hole, h.disj, h.own, fun x hx hp => ?_, h.win, h.wl⟩
  rw [he x hx hp]; exact h.mn x hx hp

/-- The structure depends only on the memory of its `12 s` cells. -/
theorem TMem.congr_mem (h : TMem s nr F e own X H Q nm rm) {nm' : ℕ → ℕ} {rm' : ℕ → ℝ}
    (hn : ∀ a, Q ≤ a → a < Q + 12 * s → nm' a = nm a)
    (hr : ∀ a, Q ≤ a → a < Q + 8 * s → rm' a = rm a) : TMem s nr F e own X H Q nm' rm' := by
  have p : ∀ x < s, tPr Q nm' x = tPr Q nm x := fun x hx => hn _ (by omega) (by omega)
  have ow : ∀ x < s, tOwn Q nm' x = tOwn Q nm x := fun x hx => hn _ (by omega) (by omega)
  have en : ∀ x < s, tEnd Q nm' x = tEnd Q nm x := fun x hx => hn _ (by omega) (by omega)
  have mi : ∀ x < s, tMin Q nm' x = tMin Q nm x := fun x hx => hn _ (by omega) (by omega)
  have ke : ∀ x < s, tKey Q rm' x = tKey Q rm x := fun x hx => hr _ (by omega) (by omega)
  have wn : ∀ i, 1 ≤ i → i < 2 * s → tWn Q s nm' i = tWn Q s nm i := fun i h1 h2 =>
    hn _ (by omega) (by omega)
  have wl : ∀ i, 1 ≤ i → i < 2 * s → tWl Q s nm' i = tWl Q s nm i := fun i h1 h2 =>
    hn _ (by omega) (by omega)
  refine ⟨h.nr_le, fun x hx => by rw [p x hx]; exact h.pr01 x hx, fun x hx hp => ?_,
    fun ρ hρ => ?_, h.hole, fun x y hxy hy hx' hy' => ?_, fun x hx hp ρ h1 h2 => ?_,
    fun x hx hp => ?_, ?_, ?_⟩
  · rw [p x hx] at hp; rw [en x hx]; exact h.st x hx hp
  · rw [h.cover ρ hρ]
    constructor
    · rintro ⟨x, hx, hp, h1, h2⟩
      exact ⟨x, hx, by rw [p x hx]; exact hp, h1, by rw [en x hx]; exact h2⟩
    · rintro ⟨x, hx, hp, h1, h2⟩
      exact ⟨x, hx, by rw [← p x hx]; exact hp, h1, by rw [← en x hx]; exact h2⟩
  · rw [p x (by omega)] at hx'; rw [p y hy] at hy'; rw [en x (by omega)]
    exact h.disj x y hxy hy hx' hy'
  · rw [p x hx] at hp; rw [en x hx] at h2; rw [ow x hx]; exact h.own x hx hp ρ h1 h2
  · rw [p x hx] at hp; rw [mi x hx, en x hx, ow x hx, ke x hx]; exact h.mn x hx hp
  · exact (h.win.congr_wn wn).congr (fun x hx => p x hx) (fun x hx => ke x hx)
  · exact (h.wl.congr_wn wl).congr (fun x hx => p x hx) (fun _ _ => rfl)

end mem

/-! ### The number of starts -/

/-- The number of starts. -/
noncomputable def nst (Q s : ℕ) (nm : ℕ → ℕ) : ℕ :=
  ((Finset.range s).filter (fun x => tPr Q nm x = 1)).card

/-- Clearing a start removes one start. -/
lemma nst_clr {Q s x : ℕ} {nm nm' : ℕ → ℕ} (hx : x < s) (hp : tPr Q nm x = 1)
    (h : ∀ y < s, tPr Q nm' y = if y = x then 0 else tPr Q nm y) :
    nst Q s nm' + 1 = nst Q s nm := by
  unfold nst
  have e : (Finset.range s).filter (fun y => tPr Q nm' y = 1) =
      ((Finset.range s).filter (fun y => tPr Q nm y = 1)).erase x := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    constructor
    · rintro ⟨h1, h2⟩
      rw [h y h1] at h2
      by_cases e : y = x
      · rw [iteT e] at h2; omega
      · rw [iteF e] at h2; exact ⟨e, h1, h2⟩
    · rintro ⟨h0, h1, h2⟩
      exact ⟨h1, by rw [h y h1, iteF h0]; exact h2⟩
  rw [e, Finset.card_erase_of_mem (by simp [hx, hp])]
  have : 0 < ((Finset.range s).filter (fun y => tPr Q nm y = 1)).card :=
    Finset.card_pos.2 ⟨x, by simp [hx, hp]⟩
  omega

/-- Writing a new start adds one start. -/
lemma nst_set {Q s x : ℕ} {nm nm' : ℕ → ℕ} (hx : x < s) (hp : tPr Q nm x ≠ 1)
    (h : ∀ y < s, tPr Q nm' y = if y = x then 1 else tPr Q nm y) :
    nst Q s nm' = nst Q s nm + 1 := by
  unfold nst
  have e : (Finset.range s).filter (fun y => tPr Q nm' y = 1) =
      insert x ((Finset.range s).filter (fun y => tPr Q nm y = 1)) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      rw [h y h1] at h2
      by_cases e : y = x
      · exact Or.inl e
      · rw [iteF e] at h2; exact Or.inr ⟨h1, h2⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨hx, by rw [h y hx, iteT rfl]⟩
      · refine ⟨h1, ?_⟩
        rw [h y h1]; split_ifs <;> first | rfl | exact h2
  rw [e, Finset.card_insert_of_notMem (by simp [hp])]

/-! ### The routines -/

/-- **Write the triplet `[r201, r202)` with the owner `r200`**, its least entry by a query. -/
def tPut : Stmt :=
  .seq rmq <|
  .seq (block [.copyN 230 201, .copyN 231 200, .subN 232 202 110, .copyN 233 203, .copyR 230 200])
    tSet

/-- **Clear the start `r230`.** -/
def tDel : Stmt := tClr

/-- The registers changed by `tPut`. -/
def TPn (r : ℕ) : Prop :=
  (130 ≤ r ∧ r < 139) ∨ (203 ≤ r ∧ r < 208) ∨ (210 ≤ r ∧ r < 235) ∨ (300 ≤ r ∧ r < 400)

/-- The real registers changed by `tPut`. -/
def TPr (r : ℕ) : Prop :=
  (130 ≤ r ∧ r < 132) ∨ (200 ≤ r ∧ r < 208) ∨ (210 ≤ r ∧ r < 212) ∨ r = 230 ∨
    (300 ≤ r ∧ r < 400)

/-- The frame of a routine: the natural registers outside `M`, the real registers outside `MR`
and the output are kept. -/
structure Fr (M MR : ℕ → Prop) (c c' : Config) : Prop where
  n : ∀ r, ¬ M r → c'.nreg r = c.nreg r
  r : ∀ r, ¬ MR r → c'.rreg r = c.rreg r
  o : c'.output = c.output

lemma Fr.trans {M MR M' MR' M'' MR'' : ℕ → Prop} {c c₁ c₂ : Config} (h₁ : Fr M MR c c₁)
    (h₂ : Fr M' MR' c₁ c₂) (a : ∀ r, M r → M'' r) (b : ∀ r, M' r → M'' r)
    (a' : ∀ r, MR r → MR'' r) (b' : ∀ r, MR' r → MR'' r) : Fr M'' MR'' c c₂ :=
  ⟨fun r hr => (h₂.n r fun h => hr (b r h)).trans (h₁.n r fun h => hr (a r h)),
    fun r hr => (h₂.r r fun h => hr (b' r h)).trans (h₁.r r fun h => hr (a' r h)),
    h₂.o.trans h₁.o⟩

lemma Fr.refl {M MR : ℕ → Prop} (c : Config) : Fr M MR c c := ⟨fun _ _ => rfl, fun _ _ => rfl, rfl⟩

variable {P : Prm} {I : Input}

/-- The triplet structure of the half block `k` of the level `2 ^ T`. -/
abbrev BM (P : Prm) (T k : ℕ) (e : ℕ → ℝ) (own : ℕ → ℕ) (X H : ℕ → Prop) (Q : ℕ) (nm : ℕ → ℕ)
    (rm : ℕ → ℝ) : Prop :=
  TMem (2 ^ T) (hbNr P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e own X H Q nm rm

/-- **Writing a triplet**: the rows `[j1, j2)` of the hole, all owned by `σ`, become the triplet
`(σ, [j1, j2 - 1])`, with a least entry found by `rmq`. -/
theorem tPut_exec (hL : Lay P) {B Q T k σ j1 j2 : ℕ} {e : ℕ → ℝ} {own : ℕ → ℕ}
    {X H : ℕ → Prop} (c : Config) (hc : WordsBounded P.W c) (hE : Env P B (2 ^ T) k c)
    (hT : TCtx Q (2 ^ T) c) (hB : B + 8 * 2 ^ T ≤ P.W) (hQ : Q + 16 * 2 ^ T ≤ P.W)
    (hR : QReady P B (2 ^ T) k c.nmem) (hM : BM P T k e own X H Q c.nmem c.rmem)
    (he : e σ = c.rmem (P.db + (sib k * 2 ^ T + σ)))
    (h200 : c.nreg 200 = σ) (hσ : σ < hbNc P.b (2 ^ T) k) (h201 : c.nreg 201 = j1)
    (h202 : c.nreg 202 = j2) (hj : j1 < j2) (hj2 : j2 ≤ hbNr P.b (2 ^ T) k)
    (hH : ∀ ρ, j1 ≤ ρ → ρ < j2 → H ρ) (ho : ∀ ρ, j1 ≤ ρ → ρ < j2 → own ρ = σ) :
    ∃ c' k', Exec I P.W tPut c c' k' ∧ k' ≤ rmqCost T + 49 * T + 20 ∧
      BM P T k e own X (fun ρ => H ρ ∧ ¬ (j1 ≤ ρ ∧ ρ < j2)) Q c'.nmem c'.rmem ∧
      (∀ y < 2 ^ T, tPr Q c'.nmem y = if y = j1 then 1 else tPr Q c.nmem y) ∧
      Fr TPn TPr c c' ∧ (∀ a, (a < Q ∨ Q + 12 * 2 ^ T ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, (a < Q ∨ Q + 8 * 2 ^ T ≤ a) → c'.rmem a = c.rmem a) := by
  have hnr : hbNr P.b (2 ^ T) k ≤ 2 ^ T := hM.nr_le
  unfold tPut
  refine spec_seq ?_
  refine spec_use (rmq_exec (I := I) hL c hc hE hB rfl hR h200 hσ h201 h202 hj hj2) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨hq, hK⟩
  have hq1 := hq.lo; have hq2 := hq.hi
  have g : ∀ r, (r < 130 ∨ (139 ≤ r ∧ r < 203) ∨ (208 ≤ r ∧ r < 300) ∨ 400 ≤ r) →
      c₁.nreg r = c.nreg r := hK.nreg
  refine spec_seq ?_
  exec_block
  generalize hc₂ : (Config.mk _ _ _ _ _ _ : Config) = c₂
  have hw₂ : WordsBounded P.W c₂ := hc₂ ▸ ‹_›
  have f230 : c₂.nreg 230 = j1 := by rw [← hc₂]; config_simp; rw [g 201 (by omega), h201]
  have f231 : c₂.nreg 231 = σ := by rw [← hc₂]; config_simp; rw [g 200 (by omega), h200]
  have f232 : c₂.nreg 232 = j2 - 1 := by
    rw [← hc₂]; config_simp; rw [g 202 (by omega), h202, (g 110 (by omega)).trans hE.g.r110]
  have f233 : c₂.nreg 233 = c₁.nreg 203 := by rw [← hc₂]; config_simp
  have r230 : c₂.rreg 230 = c₁.rreg 200 := by rw [← hc₂]; config_simp
  have fK : ∀ r, r ≠ 230 → r ≠ 231 → r ≠ 232 → r ≠ 233 → c₂.nreg r = c₁.nreg r :=
    fun r h1 h2 h3 h4 => by rw [← hc₂]; config_simp; upd_tac
  have fR : ∀ r, r ≠ 230 → c₂.rreg r = c₁.rreg r := fun r h1 => by
    rw [← hc₂]; config_simp; rw [upd_other _ _ _ h1]
  have fN : c₂.nmem = c.nmem := by rw [← hc₂]; config_simp; exact hK.nmem
  have fM : c₂.rmem = c.rmem := by rw [← hc₂]; config_simp; exact hK.rmem
  have fO : c₂.output = c.output := by rw [← hc₂]; config_simp; exact hK.out
  have kc : ∀ r, ¬ TPn r → r ≠ 230 → c₂.nreg r = c.nreg r := fun r hr h1 => by
    unfold TPn at hr
    rw [fK r h1 (by omega) (by omega) (by omega), g r (by omega)]
  have hG₂ : Glob P c₂ := hE.g.of fun r h1 h2 => kc r (by unfold TPn; omega) (by omega)
  have hT₂ : TCtx Q (2 ^ T) c₂ := hT.of fun r h1 h2 => kc r (by unfold TPn; omega) (by omega)
  refine spec_use (tSet_exec (I := I) (x := j1) c₂ hw₂ hG₂ hT₂ hQ
    (by rw [kc 121 (by unfold TPn; omega) (by omega)]; exact hE.h.r121) f230 (by omega)
    (by rw [fN]; exact hM.pr01) (by rw [fN, fM]; exact hM.win) (by rw [fN]; exact hM.wl)) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hpr₃, how₃, hen₃, hmi₃, hrm₃, hn₃, hlo₃, hW₃, hWl₃, hK₃, hR₃, hO₃⟩
  have hrec : RecEq Q (2 ^ T) j1 c.nmem c₃.nmem c.rmem c₃.rmem := recEq_of
    (fun a h1 h2 h3 h4 h5 => by rw [hn₃ a h1 h2 h3 h4 h5, fN])
    (fun a h1 => by rw [hrm₃, upd_other _ _ _ h1, fM])
  have hm := hM.set (x := j1) (y := j2 - 1) (m := c₁.nreg 203) (o := σ) (by omega) (by omega)
    (by omega) (fun ρ h1 h2 => hH ρ h1 (by omega)) (fun ρ h1 h2 => ho ρ h1 (by omega))
    hq1 (by omega) (fun ρ h1 h2 => hq.min ρ ⟨h1, by omega⟩)
    (by rw [hpr₃ j1 (by omega)]; simp) (by rw [how₃, f231]) (by rw [hen₃, f232])
    (by rw [hmi₃, f233])
    (by unfold tKey; rw [hrm₃, upd_same, r230, hq.val, he]) hrec hW₃ hWl₃
  refine ⟨by omega, hm.rearr (fun ρ hρ => ?_) (fun ρ hρ => ?_), fun y hy => ?_,
    ⟨fun r hr => ?_, fun r hr => ?_, ?_⟩, fun a ha => ?_, fun a ha => ?_⟩
  · constructor
    · rintro (h' | ⟨h1, h2⟩)
      · exact Or.inl h'
      · exact Or.inr ⟨h1, fun h' => h2 ⟨h'.1, by omega⟩⟩
    · rintro (h' | ⟨h1, h2⟩)
      · exact Or.inl h'
      · exact Or.inr ⟨h1, fun h' => h2 ⟨h'.1, by omega⟩⟩
  · exact hM.hole ρ hρ.1
  · rw [hpr₃ y hy, fN]
  · unfold TPn at hr
    rw [hK₃ r (by omega), kc r (by unfold TPn; omega) (by omega)]
  · unfold TPr at hr
    rw [hR₃ r (by omega) (by omega), fR r (by omega)]
    exact hK.rreg r (by omega) (by omega) (by omega)
  · rw [hO₃, fO]
  · rw [hlo₃ a ha, fN]
  · rw [hrm₃, upd_other _ _ _ (by omega), fM]

/-- **Clearing a start** moves its rows to the hole. -/
theorem tDel_exec {Q T k x : ℕ} {e : ℕ → ℝ} {own : ℕ → ℕ} {X H : ℕ → Prop} (c : Config)
    (hc : WordsBounded P.W c) (hG : Glob P c) (hT : TCtx Q (2 ^ T) c) (hQ : Q + 16 * 2 ^ T ≤ P.W)
    (h121 : c.nreg 121 = 2 ^ T) (h230 : c.nreg 230 = x) (hx : x < 2 ^ T)
    (hM : BM P T k e own X H Q c.nmem c.rmem) (hpx : tPr Q c.nmem x = 1) :
    ∃ c' k', Exec I P.W tDel c c' k' ∧ k' ≤ 49 * T + 7 ∧
      BM P T k e own X (fun ρ => H ρ ∨ (x ≤ ρ ∧ ρ ≤ tEnd Q c.nmem x)) Q c'.nmem c'.rmem ∧
      (∀ y < 2 ^ T, tPr Q c'.nmem y = if y = x then 0 else tPr Q c.nmem y) ∧
      Fr TPn TPr c c' ∧ (∀ a, (a < Q ∨ Q + 12 * 2 ^ T ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rmem = c.rmem := by
  unfold tDel
  refine spec_use (tClr_exec (I := I) c hc hG hT hQ h121 h230 hx hM.pr01 hM.win hM.wl) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨hpr₁, hrm₁, hn₁, hlo₁, hW₁, hWl₁, hK₁, hR₁, hO₁⟩
  refine ⟨hk₁, hM.clr hx hpx (by rw [hpr₁ x hx]; simp) (recEq_of (fun a h1 h2 _ _ _ =>
    hn₁ a h1 h2) (fun a _ => by rw [hrm₁])) hW₁ hWl₁, hpr₁, ⟨fun r hr => ?_, fun r hr => ?_, hO₁⟩,
    hlo₁, hrm₁⟩
  · unfold TPn at hr; exact hK₁ r (by omega)
  · unfold TPr at hr; exact hR₁ r (by omega) (by omega)

end FR

end Monge

end PlanarFlow
