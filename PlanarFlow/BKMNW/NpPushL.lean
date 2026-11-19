module

public import PlanarFlow.BKMNW.NpPushG

/-!
# A push-back with explicit orders (for the machine)

`pushFwd M fr` (Appendix C) cancels the flow cycles from a classically chosen root face and visits
the vertices and the darts in classically chosen orders. **`pushFwdL M fr r ord outs`** makes the
three choices explicit: the root `r` of the cancellation (`cancelR`), the order of the visits
`ord g` (any topological order of the positive darts of the cancelled flow `g`, **`TopoOK`**), and
the order `outs v` of the darts leaving `v` (any duplicate-free list of them, **`OutsOK`**); a
machine program fixes them (e.g. the frame's dart order and Kahn's order), and the proofs of
`PushBack.lean` and `Cancel.lean` go through unchanged:

* `cancelR`, **`cancelR_spec`** (`cancel_spec` for any root);
* `pushAtL`, `sum_outL_le`, **`pushLoopL_spec`** (`pushLoop_spec` with the darts in the order
  `outs`); `pairwise_idxOf`;
* **`pushSpec_pushFwdL`**: `pushFwdL M fr r ord outs` meets `PushSpec` (so `implG` with it meets
  the specifications of Algorithm 1, `implG_spec`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

/-! ### The cancellation from an explicit root -/

variable (M) in
/-- **The cancellation of the flow cycles from the root face `r`**: one pass on `g`, one pass on
the reversed flow (`cancel` with `r` for the chosen face). -/
noncomputable def cancelR (fr : FRFun F) (r : F) (g : D → ℤ) : D → ℤ :=
  -(cpass M fr r (-(cpass M fr r g)))

theorem cancelR_spec (hM : M.IsPlane) {fr : FRFun F} (hfr : FRSpec fr) (r : F) {g : D → ℤ}
    (hg : M.IsAntisymm g) :
    M.IsAntisymm (cancelR M fr r g) ∧ Conf g (cancelR M fr r g) ∧
      (∀ v, M.div (cancelR M fr r g) v = M.div g v) ∧
      ∀ v, ¬ Relation.TransGen (Pos M (cancelR M fr r g)) v v := by
  unfold cancelR
  have a₁ := cpass_antisymm (fr := fr) (r := r) hg
  generalize hg₁ : cpass M fr r g = g₁ at a₁
  have hn₁ : M.IsAntisymm (-g₁) := fun d => by simp [a₁ d]
  have a₂ := cpass_antisymm (fr := fr) (r := r) hn₁
  have c₁ : Conf g g₁ := hg₁ ▸ cpass_conf hM hfr r hg
  have c₂ : Conf (-g₁) (cpass M fr r (-g₁)) := cpass_conf hM hfr r hn₁
  generalize hg₂' : cpass M fr r (-g₁) = g₂' at a₂ c₂
  have a₂' : M.IsAntisymm (-g₂') := fun d => by simp [a₂ d]
  have c₂' : Conf g₁ (-g₂') := by
    have := c₂.neg hn₁ a₂; simpa using this
  refine ⟨a₂', c₁.trans c₂', fun v => ?_, fun v hv => ?_⟩
  · have e₂ : M.div g₂' v = M.div (-g₁) v := by rw [← hg₂']; exact div_cpass _ v
    have e₁ : M.div g₁ v = M.div g v := by rw [← hg₁]; exact div_cpass _ v
    have hn : ∀ h : D → ℤ, M.div (-h) v = - M.div h v := fun h => by
      simp [CombMap.div, sum_neg_distrib]
    rw [hn, e₂, hn, e₁, neg_neg]
  · obtain ⟨ds, hne, hpos, hdiv⟩ := exists_circ_of_transGen hv
    obtain ⟨ψ₀, hψ₀⟩ := exists_int_potential hM
      (f := circ M ds) ⟨circ_antisymm ds, fun w => by rw [hdiv]; simp⟩
    let ψ : F → ℤ := fun y => ψ₀ y - ψ₀ r
    have hψ : ∀ d, circ M ds d = M.cob ψ d := fun d => by rw [hψ₀]; simp [cob, ψ]
    have hψr : ψ r = 0 := by simp [ψ]
    have hNn : (0 : ℤ) ≤ ds.length := by positivity
    -- the dart positive for the result is positive for the first pass
    have hpos₁ : ∀ d ∈ ds, 0 < g₁ d := fun d hd => c₂'.pos a₁ a₂' (hpos d hd)
    -- the first pass: `ψ ≥ 0`
    have hge : ∀ y, 0 ≤ ψ y := by
      intro y
      refine pass_extremal hM hfr r hg hψr hNn (fun d hd => ?_) y
      rw [← hψ] at hd
      rw [hg₁]
      exact ⟨hpos₁ _ (circ_neg_mem hd), by rw [← hψ]; exact neg_circ_le ds d⟩
    -- the second pass: `ψ ≤ 0`
    have hle : ∀ y, 0 ≤ -ψ y := by
      intro y
      have hψr' : (fun y => -ψ y) r = 0 := by simp [hψr]
      refine pass_extremal hM hfr r hn₁ (ψ := fun y => -ψ y) hψr' hNn (fun d hd => ?_) y
      have e : M.cob (fun y => -ψ y) d = - circ M ds d := by rw [hψ]; simp [cob]; ring
      rw [e] at hd ⊢
      have hd' : 0 < circ M ds d := by omega
      have hmem : d ∈ ds := by
        by_contra hn; simp [circ, List.count_eq_zero_of_not_mem hn] at hd'; omega
      rw [hg₂', a₂ d]
      refine ⟨?_, by rw [neg_neg]; exact circ_le ds d⟩
      have := hpos d hmem; simp only [Pi.neg_apply] at this; omega
    -- the circulation vanishes, but not on the first dart
    obtain ⟨d₀, hd₀⟩ := List.exists_mem_of_ne_nil ds hne
    have h0 : circ M ds d₀ = 0 := by
      rw [hψ]; simp only [cob]
      have := hge (M.face (M.rev d₀)); have := hle (M.face (M.rev d₀))
      have := hge (M.face d₀); have := hle (M.face d₀)
      omega
    have hrev : M.rev d₀ ∉ ds := fun h => by
      have h1 := hpos _ h; have h2 := hpos _ hd₀
      simp only [Pi.neg_apply] at h1 h2; rw [a₂ d₀] at h1; omega
    simp only [circ, List.count_eq_zero_of_not_mem hrev] at h0
    have := List.count_pos_iff.2 hd₀
    omega

/-! ### The topological rank -/

variable (M) in

/-! ### The visits with explicit orders -/

variable (M) in
/-- **The darts leaving every vertex**, each listed once. -/
def OutsOK (outs : V → List D) : Prop := ∀ v, (outs v).Nodup ∧ ∀ d, d ∈ outs v ↔ M.tail d = v

variable (M) in
/-- **A topological order of the positive darts** of every acyclic flow: every vertex once, the
tail of a positive dart before its head. -/
def TopoOK (ord : (D → ℤ) → List V) : Prop :=
  ∀ g : D → ℤ, M.IsAntisymm g → (∀ v, ¬ Relation.TransGen (Pos M g) v v) →
    (ord g).Nodup ∧ (∀ v, v ∈ ord g) ∧
      ∀ d, 0 < g d → (ord g).idxOf (M.tail d) < (ord g).idxOf (M.head d)

variable (M) in
/-- The visit of `v` with the darts leaving it in the order `outs v`. -/
noncomputable def pushAtL (outs : V → List D) (β : V → ℤ) (Fr : Finset V) (g : D → ℤ) (v : V) :
    D → ℤ :=
  if v ∉ Fr ∧ β v < M.div g v then ((outs v).foldl (redStep M) (g, M.div g v - β v)).1 else g

lemma sum_outL_le {outs : V → List D} (houts : OutsOK M outs) (g : D → ℤ) (v : V) :
    M.div g v ≤ ((outs v).map fun d => max 0 (g d)).sum := by
  have e : (outs v).toFinset = univ.filter fun d => M.tail d = v := by
    ext d; simp [(houts v).2 d]
  rw [← List.sum_toFinset _ (houts v).1, e, CombMap.div]
  exact sum_le_sum fun d _ => le_max_right _ _

/-- **The visits in topological order**, the darts leaving each vertex in the order `outs`. -/
theorem pushLoopL_spec {outs : V → List D} (houts : OutsOK M outs) {β : V → ℤ} {Fr W : Finset V} {g₀ : D → ℤ} {rkf : V → ℕ}
    (hrk : ∀ d, 0 < g₀ d → rkf (M.tail d) < rkf (M.head d))
    (hW : ∀ d, M.tail d ∈ W → M.head d ∉ W → g₀ d ≤ 0)
    (hout : ∀ v, v ∉ W → v ∉ Fr → M.div g₀ v ≤ β v)
    (hin : ∀ v ∈ W, v ∉ Fr → 0 ≤ β v) (ha : M.IsAntisymm g₀) :
    ∀ (L : List V) (g : D → ℤ) (P : Finset V), L.Nodup →
      L.Pairwise (fun a b => rkf a ≤ rkf b) → (∀ v ∈ L, v ∉ P) →
      (∀ w ∈ P, ∀ v ∈ L, rkf w ≤ rkf v) → PInv (M := M) β Fr W g₀ g P →
      PInv (M := M) β Fr W g₀ (L.foldl (pushAtL M outs β Fr) g) (P ∪ L.toFinset) := by
  intro L
  induction L with
  | nil => intro g P _ _ _ _ h; simpa using h
  | cons v L ih =>
    intro g P hnd hpw hLP hrkP h
    obtain ⟨hvL, hnd'⟩ := List.nodup_cons.1 hnd
    obtain ⟨hpv, hpw'⟩ := List.pairwise_cons.1 hpw
    have hvP : v ∉ P := hLP v (List.mem_cons_self ..)
    rw [List.foldl_cons]
    have heq : P ∪ (v :: L).toFinset = insert v P ∪ L.toFinset := by
      ext x; simp only [mem_union, List.mem_toFinset, List.mem_cons, mem_insert]; tauto
    rw [heq]
    refine ih _ _ hnd' hpw' (fun x hx => ?_) (fun w hw x hx => ?_) ?_
    · rw [mem_insert]; push Not
      exact ⟨fun h => hvL (h ▸ hx), hLP x (List.mem_cons_of_mem _ hx)⟩
    · rcases mem_insert.1 hw with rfl | hw
      · exact hpv x hx
      · exact hrkP w hw x (List.mem_cons_of_mem _ hx)
    -- one visit
    have hrkv : ∀ w ∈ P, rkf w ≤ rkf v := fun w hw => hrkP w hw v (List.mem_cons_self ..)
    unfold pushAtL
    split_ifs with hc
    swap
    · refine ⟨h.antisymm, h.conf, h.out, fun w hw hwF => ?_, fun w => ?_⟩
      · rcases mem_insert.1 hw with rfl | hw
        · push Not at hc; exact hc hwF
        · exact h.done w hw hwF
      · rcases h.low w with h' | ⟨h1, h2, h3⟩
        · exact Or.inl h'
        · exact Or.inr ⟨mem_insert_of_mem h1, h2, h3⟩
    obtain ⟨hvF, hlt⟩ := hc
    have hvW : v ∈ W := by
      by_contra hn
      have := h.out v hn; have := hout v hn hvF; omega
    have hβ := hin v hvW hvF
    have hpos₀ : ∀ d, 0 < g d → 0 < g₀ d := fun d hd => h.conf.pos ha h.antisymm hd
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := redFold_spec (M := M) (v := v) (outs v) g
      (M.div g v - β v) h.antisymm (by omega) (houts v).1
      (fun d hd => ((houts v).2 d).1 hd)
      (fun d hd hp => by
        have h1 : M.tail d = v := ((houts v).2 d).1 hd
        have := hrk d (hpos₀ d hp)
        rw [h1] at this; intro h2; rw [h2] at this; omega)
    have h0 := i5 (by have := sum_outL_le houts g v; omega)
    rw [h0] at i4
    generalize (outs v).foldl (redStep M) (g, M.div g v - β v) = st at *
    -- the heads of the positive darts leaving `v`
    have hheads : ∀ d ∈ outs v, 0 < g d → rkf v < rkf (M.head d) ∧ M.head d ∈ W := by
      intro d hd hp
      have h1 : M.tail d = v := ((houts v).2 d).1 hd
      refine ⟨h1 ▸ hrk d (hpos₀ d hp), ?_⟩
      by_contra hn
      have := hW d (h1 ▸ hvW) hn; have := hpos₀ d hp; omega
    have hunch : ∀ w, w ≠ v → (rkf w ≤ rkf v ∨ w ∉ W) → M.div st.1 w = M.div g w := by
      intro w hw hw'
      refine i6 w hw fun d hd hp hdw => ?_
      obtain ⟨h1, h2⟩ := hheads d hd hp
      rw [hdw] at h1 h2
      rcases hw' with h3 | h3
      · omega
      · exact h3 h2
    refine ⟨i1, h.conf.trans i2, fun w hw => ?_, fun w hw hwF => ?_, fun w => ?_⟩
    · rw [hunch w (fun h' => hw (h' ▸ hvW)) (Or.inr hw)]; exact h.out w hw
    · rcases mem_insert.1 hw with rfl | hw
      · omega
      · rw [hunch w (fun h' => hvP (h' ▸ hw)) (Or.inl (hrkv w hw))]; exact h.done w hw hwF
    · by_cases hwv : w = v
      · subst hwv; exact Or.inr ⟨mem_insert_self _ _, hvF, by omega⟩
      · rcases h.low w with h' | ⟨h1, h2, h3⟩
        · exact Or.inl (h'.trans (i7 w hwv))
        · refine Or.inr ⟨mem_insert_of_mem h1, h2, ?_⟩
          rw [hunch w hwv (Or.inl (hrkv w h1))]; exact h3


/-- The positions in a list without duplicates increase along it. -/
lemma pairwise_idxOf {α : Type*} [DecidableEq α] :
    ∀ {L : List α}, L.Nodup → L.Pairwise (fun a b => L.idxOf a ≤ L.idxOf b)
  | [], _ => List.Pairwise.nil
  | x :: L, h => by
    obtain ⟨hx, hL⟩ := List.nodup_cons.1 h
    refine List.pairwise_cons.2 ⟨fun b _ => by simp, ?_⟩
    refine (pairwise_idxOf hL).imp_of_mem fun {a b} ha hb hab => ?_
    have ha' : x ≠ a := fun e => hx (e ▸ ha)
    have hb' : x ≠ b := fun e => hx (e ▸ hb)
    rw [List.idxOf_cons, List.idxOf_cons]
    simp only [beq_iff_eq, ha', hb', ↓reduceIte]
    omega

variable (M) in
/-- **The push-back with explicit choices**: cancel from `r`, then visit the vertices in the
order `ord` of the cancelled flow, reducing the darts leaving each in the order `outs`. -/
noncomputable def pushFwdL (fr : FRFun F) (r : F) (ord : (D → ℤ) → List V)
    (outs : V → List D) : PushFn D V := fun β Fr g =>
  (ord (cancelR M fr r g)).foldl (pushAtL M outs β Fr) (cancelR M fr r g)

/-- **The push-back with explicit choices meets `PushSpec`.** -/
theorem pushSpec_pushFwdL (hM : M.IsPlane) {fr : FRFun F} (hfr : FRSpec fr) (r : F)
    {ord : (D → ℤ) → List V} (hord : TopoOK M ord) {outs : V → List D}
    (houts : OutsOK M outs) : PushSpec M (pushFwdL M fr r ord outs) := by
  intro c g hc hg β Fr W hW hout hin
  classical
  obtain ⟨a₀, c₀, d₀, ac₀⟩ := cancelR_spec hM hfr r hg.antisymm
  obtain ⟨o1, hall, o3⟩ := hord _ a₀ ac₀
  have h := pushLoopL_spec (M := M) houts (β := β) (Fr := Fr) (W := W)
    (rkf := fun v => (ord (cancelR M fr r g)).idxOf v)
    (fun d hd => o3 d hd)
    (fun d h1 h2 => by
      by_contra hn
      have := hW d h1 h2; have := c₀.pos hg.antisymm a₀ (by omega : 0 < cancelR M fr r g d); omega)
    (fun v h1 h2 => by rw [d₀]; exact hout v h1 h2) (fun v h1 h2 => hin v h1 h2) a₀
    (ord (cancelR M fr r g)) (cancelR M fr r g) ∅ o1 (pairwise_idxOf o1)
    (fun _ _ => notMem_empty _) (fun _ h => absurd h (notMem_empty _))
    ⟨a₀, Conf.refl _, fun _ _ => rfl, fun _ h => absurd h (notMem_empty _),
      fun _ => Or.inl le_rfl⟩
  have hmem : ∀ v, v ∈ ∅ ∪ (ord (cancelR M fr r g)).toFinset := fun v => by
    simp [hall v]
  simp only [pushFwdL]
  generalize (ord (cancelR M fr r g)).foldl (pushAtL M outs β Fr) (cancelR M fr r g) = g' at h ⊢
  refine ⟨hg.of_conf hc h.antisymm (c₀.trans h.conf), c₀.trans h.conf,
    fun v hv => h.done v (hmem v) hv, fun v hv => ?_, fun v hv => ?_⟩
  · rcases h.low v with h' | ⟨-, -, h3⟩
    · rw [← d₀]; exact (min_le_left _ _).trans h'
    · rw [h3]; exact min_le_right _ _
  · rcases h.low v with h' | ⟨-, h2, -⟩
    · rw [← d₀]; exact h'
    · exact absurd hv h2

end BKMNW

end PlanarFlow
