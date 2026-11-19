module

public import PlanarSeparator.Machine.PieceProg

/-!
# The numbers of a piece: from the passes to the words of `ltIn`

The passes of `PlanarSeparator/Machine/PieceProg.lean` run on the global arrays of a graph
`G` on `Fin N` (offsets `gofs`, tails `tlG`, reversals `rvG`, rotation `roG` of the darts
numbered by `dartNum G`) and the vertices `lv C 0 < lv C 1 < …` of a piece `C`. Here the
numbers they compute are identified with the words of `ltIn R (ord N) C w`
(`PlanarSeparator.Piece.ltIn_words`):

* `cntB_lv`, `cntB_lv_card`, `rank_lv`: the counts of the rank pass are `sC` (the inner darts
  with a lower tail) and the rank of an inner dart is `rkC + 1`.
* `rkA`: the rank array after the rank pass; `rkA_hfr` (the first return of the rotation to the
  darts of positive rank, within `Δ` steps), `rkA_inj`, `rkA_le`.
* `rkC_gofs`: the offsets of the piece.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open Finset WordRAM

variable {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]

/-- The number of darts of `G`. -/
abbrev nD : ℕ := (dkeys G).card

/-- The tails of the darts, numerically. -/
noncomputable abbrev tlG : ℕ → ℕ := SepProg.tlI (dartNum G)
/-- The reversals of the darts, numerically. -/
noncomputable abbrev rvG : ℕ → ℕ := SepProg.rvI (dartNum G)
/-- The rotation, numerically. -/
noncomputable abbrev roG (R : Kasteleyn.RotationSystem G) : ℕ → ℕ := SepProg.roI R (dartNum G)

theorem tlG_dartNum (d : G.Dart) : tlG G (dartNum G d) = d.fst := by
  simp [SepProg.tlI]

theorem rvG_dartNum (d : G.Dart) : rvG G (dartNum G d) = dartNum G d.symm := by
  simp [SepProg.rvI]

theorem roG_dartNum (R : Kasteleyn.RotationSystem G) (d : G.Dart) :
    roG G R (dartNum G d) = dartNum G (R.rot d) := by
  simp [SepProg.roI]

theorem gofs_eq : gofs G = SepProg.ofsI (G := G) := rfl

theorem gofs_le (v : ℕ) : gofs G v ≤ nD G := by
  unfold gofs
  calc _ ≤ #(univ : Finset G.Dart) := card_le_card (filter_subset _ _)
    _ = nD G := by rw [card_univ, Fintype.card_congr (dartNum G), Fintype.card_fin]

theorem gofs_N : gofs G N = nD G := by
  unfold gofs
  rw [filter_true_of_mem (fun d _ => d.fst.2), card_univ, Fintype.card_congr (dartNum G),
    Fintype.card_fin]

theorem dartNum_symm_val {g : ℕ} (hg : g < nD G) : (dartNum G ((dartNum G).symm ⟨g, hg⟩) : ℕ) = g := by
  simp

/-! ### The sorted list of a piece -/

/-- The `j`-th vertex of `C` in increasing order. -/
def lv (C : Finset (Fin N)) (j : ℕ) : ℕ := ((clist (ord N) C).map Fin.val).getD j 0

theorem lv_eq (C : Finset (Fin N)) {j : ℕ} (hj : j < (clist (ord N) C).length) :
    lv C j = (cemb (ord N) C ⟨j, hj⟩ : ℕ) := by
  unfold lv
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  rfl

theorem lv_lt (C : Finset (Fin N)) {j : ℕ} (hj : j < (clist (ord N) C).length) : lv C j < N := by
  rw [lv_eq C hj]; exact Fin.is_lt _

theorem lv_inc (C : Finset (Fin N)) :
    ∀ i j, i < j → j < (clist (ord N) C).length → lv C i < lv C j := by
  intro i j hij hj
  rw [lv_eq C (hij.trans hj), lv_eq C hj, ← Fin.lt_def, cemb_lt_iff]
  exact hij

theorem mem_iff_lv (C : Finset (Fin N)) (x : Fin N) :
    x ∈ C ↔ ∃ j < (clist (ord N) C).length, lv C j = x := by
  rw [← mem_clist mem_ord (C := C)]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 h
    exact ⟨i, i.2, by rw [lv_eq C i.2]; exact congrArg Fin.val hi⟩
  · rintro ⟨j, hj, hx⟩
    rw [lv_eq C hj] at hx
    have : (cemb (ord N) C ⟨j, hj⟩) = x := Fin.ext hx
    rw [← this]
    exact List.get_mem _ _

theorem length_clist_ord (C : Finset (Fin N)) : (clist (ord N) C).length = #C :=
  length_clist mem_ord C

/-! ### Counting the inner darts -/

/-- The number of darts with both ends in `C` and tail below `x`. -/
noncomputable def sC (C : Finset (Fin N)) (x : ℕ) : ℕ :=
  #(univ.filter fun d : G.Dart => d.fst ∈ C ∧ d.snd ∈ C ∧ (d.fst : ℕ) < x)

theorem sC_add (C : Finset (Fin N)) {a b : ℕ} (hab : a ≤ b) :
    sC G C b = sC G C a +
      #(univ.filter fun d : G.Dart => d.fst ∈ C ∧ d.snd ∈ C ∧ a ≤ (d.fst : ℕ) ∧ (d.fst : ℕ) < b) := by
  unfold sC
  rw [← card_union_of_disjoint]
  · congr 1; ext d; simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases Nat.lt_or_ge (d.fst : ℕ) a with h | h
      · exact Or.inl ⟨h1, h2, h⟩
      · exact Or.inr ⟨h1, h2, h, h3⟩
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩)
      · exact ⟨h1, h2, by omega⟩
      · exact ⟨h1, h2, h4⟩
  · rw [disjoint_filter]; intro d _ h1 h2; omega

theorem sC_gap (C : Finset (Fin N)) {a b : ℕ} (hab : a ≤ b)
    (hgap : ∀ x : Fin N, x ∈ C → (x : ℕ) < a ∨ b ≤ x) : sC G C b = sC G C a := by
  rw [sC_add G C hab, filter_false_of_mem, card_empty, Nat.add_zero]
  intro d _ h
  rcases hgap d.fst h.1 with h' | h' <;> omega

theorem sC_vert (C : Finset (Fin N)) {v : Fin N} (hv : v ∈ C) :
    sC G C ((v : ℕ) + 1) = sC G C v + #(univ.filter fun d : G.Dart => d.fst = v ∧ d.snd ∈ C) := by
  rw [sC_add G C (Nat.le_succ _)]
  congr 2; ext d; simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨-, h2, h3, h4⟩; exact ⟨Fin.ext (by omega), h2⟩
  · rintro ⟨rfl, h2⟩; exact ⟨hv, h2, le_rfl, Nat.lt_succ_self _⟩

theorem sC_N (C : Finset (Fin N)) :
    sC G C N = #(univ.filter fun d : G.Dart => d.fst ∈ C ∧ d.snd ∈ C) := by
  unfold sC; congr 1; ext d; simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, d.fst.2⟩⟩

/-- `rkC` on a block: the inner darts of lower tails and those of the block before `g`. -/
theorem rkC_block (C : Finset (Fin N)) {v : Fin N} (hv : v ∈ C) {g : ℕ} (hg1 : gofs G v ≤ g)
    (hg2 : g ≤ gofs G ((v : ℕ) + 1)) :
    rkC G C g = sC G C v +
      #(univ.filter fun d : G.Dart => d.fst = v ∧ d.snd ∈ C ∧ (dartNum G d : ℕ) < g) := by
  unfold rkC sC
  rw [← card_union_of_disjoint]
  · congr 1; ext d; simp only [mem_filter, mem_univ, true_and, mem_union]
    have e1 := ofs_lt_iff G d v
    have e2 := ofs_lt_iff G d ((v : ℕ) + 1)
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases Nat.lt_or_ge (d.fst : ℕ) v with h | h
      · exact Or.inl ⟨h1, h2, h⟩
      · exact Or.inr ⟨Fin.ext (by omega), h2, h3⟩
    · rintro (⟨h1, h2, h3⟩ | ⟨rfl, h2, h3⟩)
      · exact ⟨h1, h2, by omega⟩
      · exact ⟨hv, h2, h3⟩
  · rw [disjoint_filter]; rintro d _ h ⟨rfl, -⟩; omega

theorem rkC_gofs (C : Finset (Fin N)) (v : ℕ) : rkC G C (gofs G v) = sC G C v := by
  unfold rkC sC; congr 1; ext d; simp only [mem_filter, mem_univ, true_and]
  rw [ofs_lt_iff]

/-- The marked darts of a block counted by `cntI`. -/
theorem cntI_block (C : Finset (Fin N)) (q : ℕ → Prop) [DecidablePred q]
    (hq : ∀ d : G.Dart, d.fst ∈ C → (q (dartNum G d) ↔ d.snd ∈ C)) {v : Fin N} (hv : v ∈ C)
    {g : ℕ} (hg2 : g ≤ gofs G ((v : ℕ) + 1)) :
    cntI q (gofs G v) g =
      #(univ.filter fun d : G.Dart => d.fst = v ∧ d.snd ∈ C ∧ (dartNum G d : ℕ) < g) := by
  unfold cntI
  symm
  refine card_bij (fun d _ => (dartNum G d : ℕ)) (fun d hd => ?_) (fun d _ d' _ h => ?_)
    (fun g' hg' => ?_)
  · simp only [mem_filter, mem_univ, true_and] at hd
    obtain ⟨rfl, h2, h3⟩ := hd
    simp only [mem_filter, mem_Ico]
    exact ⟨⟨(ofs_le_iff G d _).2 le_rfl, h3⟩, (hq d hv).2 h2⟩
  · exact (dartNum G).injective (Fin.ext h)
  · simp only [mem_filter, mem_Ico] at hg'
    obtain ⟨⟨h1, h2⟩, h3⟩ := hg'
    have hgD : g' < nD G := by have := gofs_le G ((v : ℕ) + 1); omega
    set d := (dartNum G).symm ⟨g', hgD⟩
    have hd : (dartNum G d : ℕ) = g' := by simp [d]
    have hf1 := (ofs_le_iff G d v).1 (by rw [hd]; exact h1)
    have hf2 := (ofs_lt_iff G d ((v : ℕ) + 1)).1 (by rw [hd]; omega)
    have hfv : d.fst = v := Fin.ext (by omega)
    refine ⟨d, ?_, hd⟩
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨hfv, (hq d (hfv ▸ hv)).1 (by rw [hd]; exact h3), by omega⟩

variable (C : Finset (Fin N)) (q : ℕ → Prop) [DecidablePred q]

/-- **The counts of the rank pass**: before the `j`-th vertex, the inner darts of lower tails. -/
theorem cntB_lv (hq : ∀ d : G.Dart, d.fst ∈ C → (q (dartNum G d) ↔ d.snd ∈ C)) :
    ∀ j < (clist (ord N) C).length, cntB q (gofs G) (lv C) j = sC G C (lv C j) := by
  intro j
  induction j with
  | zero =>
    intro hk
    simp only [cntB, range_zero, sum_empty]
    rw [sC_gap G C (Nat.zero_le _) (fun x hx => by
      obtain ⟨i, hi, hix⟩ := (mem_iff_lv C x).1 hx
      rw [← hix]
      right
      rcases Nat.eq_zero_or_pos i with rfl | h
      · exact le_rfl
      · exact (lv_inc C 0 i h hi).le)]
    simp [sC]
  | succ j ih =>
    intro hk
    have hj := lv_lt C (show j < _ by omega)
    have hvC : (⟨lv C j, hj⟩ : Fin N) ∈ C := (mem_iff_lv C _).2 ⟨j, by omega, rfl⟩
    rw [cntB, sum_range_succ, ← cntB, ih (by omega)]
    rw [show gofs G (lv C j) = gofs G ((⟨lv C j, hj⟩ : Fin N) : ℕ) from rfl,
      cntI_block G C q hq hvC le_rfl]
    have h1 := sC_vert G C hvC
    have h2 : sC G C (lv C (j + 1)) = sC G C (lv C j + 1) := by
      refine sC_gap G C (lv_inc C j (j + 1) (by omega) hk) (fun x hx => ?_)
      obtain ⟨i, hi, hix⟩ := (mem_iff_lv C x).1 hx
      rw [← hix]
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · left
        rcases Nat.lt_or_ge i j with h' | h'
        · have := lv_inc C i j h' (by omega); omega
        · obtain rfl : i = j := by omega
          omega
      · right
        rcases Nat.eq_or_lt_of_le h with h' | h'
        · rw [h']
        · exact (lv_inc C (j + 1) i h' hi).le
    rw [h2, h1]
    congr 2
    ext d; simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
    · rintro ⟨hdv, h2⟩
      refine ⟨hdv, h2, ?_⟩
      exact (ofs_lt_iff G d _).2 (by rw [hdv]; exact Nat.lt_succ_self _)

/-- **The number of marked darts of the piece**: the inner darts. -/
theorem cntB_lv_card (hq : ∀ d : G.Dart, d.fst ∈ C → (q (dartNum G d) ↔ d.snd ∈ C)) :
    cntB q (gofs G) (lv C) (clist (ord N) C).length =
      #(univ.filter fun d : G.Dart => d.fst ∈ C ∧ d.snd ∈ C) := by
  rw [← sC_N]
  rcases Nat.eq_zero_or_pos (clist (ord N) C).length with hk | hk
  · rw [hk]
    simp only [cntB, range_zero, sum_empty]
    rw [sC_gap G C (Nat.zero_le _) (fun x hx => by
      obtain ⟨i, hi, -⟩ := (mem_iff_lv C x).1 hx; omega)]
    simp [sC]
  · obtain ⟨j, hj⟩ : ∃ j, (clist (ord N) C).length = j + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hk).symm⟩
    have hjl := lv_lt C (show j < _ by omega)
    have hvC : (⟨lv C j, hjl⟩ : Fin N) ∈ C := (mem_iff_lv C _).2 ⟨j, by omega, rfl⟩
    rw [hj, cntB, sum_range_succ, ← cntB, cntB_lv G C q hq j (by omega),
      show gofs G (lv C j) = gofs G ((⟨lv C j, hjl⟩ : Fin N) : ℕ) from rfl,
      cntI_block G C q hq hvC le_rfl]
    have h1 := sC_vert G C hvC
    have h2 : sC G C N = sC G C (lv C j + 1) := by
      refine sC_gap G C (by omega) (fun x hx => ?_)
      obtain ⟨i, hi, hix⟩ := (mem_iff_lv C x).1 hx
      rw [← hix]
      left
      rcases Nat.lt_or_ge i j with h' | h'
      · have := lv_inc C i j h' (by omega); omega
      · obtain rfl : i = j := by omega
        omega
    rw [h2, h1]
    congr 2
    ext d; simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
    · rintro ⟨hdv, h2⟩
      exact ⟨hdv, h2, (ofs_lt_iff G d _).2 (by rw [hdv]; exact Nat.lt_succ_self _)⟩

/-- **The rank of a marked dart** (minus one) is `rkC`. -/
theorem rank_lv (hq : ∀ d : G.Dart, d.fst ∈ C → (q (dartNum G d) ↔ d.snd ∈ C)) {j : ℕ}
    (hj : j < (clist (ord N) C).length) {g : ℕ} (hg1 : gofs G (lv C j) ≤ g)
    (hg2 : g < gofs G (lv C j + 1)) :
    cntB q (gofs G) (lv C) j + cntI q (gofs G (lv C j)) g = rkC G C g := by
  have hjl := lv_lt C hj
  have hvC : (⟨lv C j, hjl⟩ : Fin N) ∈ C := (mem_iff_lv C _).2 ⟨j, hj, rfl⟩
  rw [cntB_lv G C q hq j hj,
    show gofs G (lv C j) = gofs G ((⟨lv C j, hjl⟩ : Fin N) : ℕ) from rfl,
    cntI_block G C q hq hvC hg2.le, rkC_block G C hvC hg1 hg2.le]

/-! ### The rank array -/

/-- The inner darts, numerically. -/
def innerN (g : ℕ) : Prop :=
  ∃ h : g < nD G, ((dartNum G).symm ⟨g, h⟩).fst ∈ C ∧ ((dartNum G).symm ⟨g, h⟩).snd ∈ C

open Classical in
/-- **The rank array** after the rank pass: `rkC + 1` on the inner darts, `0` elsewhere. -/
noncomputable def rkA (g : ℕ) : ℕ := if innerN G C g then rkC G C g + 1 else 0

theorem innerN_dartNum (d : G.Dart) : innerN G C (dartNum G d) ↔ d.fst ∈ C ∧ d.snd ∈ C := by
  unfold innerN
  constructor
  · rintro ⟨h, h1, h2⟩
    have : (dartNum G).symm ⟨(dartNum G d : ℕ), h⟩ = d := by
      rw [Equiv.symm_apply_eq]
    rw [this] at h1 h2; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(dartNum G d).2, ?_⟩
    have : (dartNum G).symm ⟨(dartNum G d : ℕ), (dartNum G d).2⟩ = d := by simp
    rw [this]; exact ⟨h1, h2⟩

theorem rkA_dartNum (d : G.Dart) :
    rkA G C (dartNum G d) = if d.fst ∈ C ∧ d.snd ∈ C then rkC G C (dartNum G d) + 1 else 0 := by
  simp only [rkA, innerN_dartNum]

theorem rkA_pos_iff (d : G.Dart) : 0 < rkA G C (dartNum G d) ↔ d.fst ∈ C ∧ d.snd ∈ C := by
  rw [rkA_dartNum]; split_ifs with h <;> simp [h]

theorem exists_dart_of_lt {g : ℕ} (hg : g < nD G) : ∃ d : G.Dart, (dartNum G d : ℕ) = g :=
  ⟨(dartNum G).symm ⟨g, hg⟩, by simp⟩

theorem rkC_lt (d : G.Dart) (h1 : d.fst ∈ C) (h2 : d.snd ∈ C) :
    rkC G C (dartNum G d) < #(univ.filter fun d : G.Dart => d.fst ∈ C ∧ d.snd ∈ C) := by
  unfold rkC
  refine card_lt_card ⟨fun x hx => ?_, fun h => ?_⟩
  · simp only [mem_filter, mem_univ, true_and] at hx ⊢; exact ⟨hx.1, hx.2.1⟩
  · have := h (show d ∈ _ by simp [h1, h2])
    simp at this

theorem rkA_le (g : ℕ) : rkA G C g ≤ #(univ.filter fun d : G.Dart => d.fst ∈ C ∧ d.snd ∈ C) := by
  unfold rkA
  split_ifs with h
  · obtain ⟨hg, h1, h2⟩ := h
    obtain ⟨d, rfl⟩ := exists_dart_of_lt G hg
    have : (dartNum G).symm ⟨(dartNum G d : ℕ), hg⟩ = d := by simp
    rw [this] at h1 h2
    exact rkC_lt G C d h1 h2
  · exact Nat.zero_le _

theorem rkC_strict {d d' : G.Dart} (h1 : d.fst ∈ C) (h2 : d.snd ∈ C)
    (hlt : (dartNum G d : ℕ) < dartNum G d') : rkC G C (dartNum G d) < rkC G C (dartNum G d') := by
  unfold rkC
  refine card_lt_card ⟨fun x hx => ?_, fun h => ?_⟩
  · simp only [mem_filter, mem_univ, true_and] at hx ⊢; exact ⟨hx.1, hx.2.1, by omega⟩
  · have := h (show d ∈ _ by simp only [mem_filter, mem_univ, true_and]; exact ⟨h1, h2, hlt⟩)
    simp at this

theorem rkA_inj : ∀ g g', g < nD G → g' < nD G → 0 < rkA G C g → rkA G C g = rkA G C g' →
    g = g' := by
  intro g g' hg hg' hp he
  obtain ⟨d, rfl⟩ := exists_dart_of_lt G hg
  obtain ⟨d', rfl⟩ := exists_dart_of_lt G hg'
  have hi := (rkA_pos_iff G C d).1 hp
  have hi' := (rkA_pos_iff G C d').1 (he ▸ hp)
  simp only [rkA_dartNum, hi, hi', and_self, ite_true, Nat.add_right_cancel_iff] at he
  rcases lt_trichotomy (dartNum G d : ℕ) (dartNum G d') with h | h | h
  · have := rkC_strict G C hi.1 hi.2 h; omega
  · exact h
  · have := rkC_strict G C hi'.1 hi'.2 h; omega

/-! ### The first return -/

variable (R : Kasteleyn.RotationSystem G)

theorem rotPerm_eq : PlanarFlow.Orbit.rotPerm (PlanarFlow.CombMap.ofRotation R) = R.rot :=
  Equiv.ext (rotPerm_ofRotation G R)

/-- The first return of the rotation to the inner darts, numerically. -/
noncomputable def frA (g : ℕ) : ℕ :=
  if h : g < nD G then
    dartNum G (PlanarFlow.Orbit.ret (PlanarFlow.Orbit.rotPerm (PlanarFlow.CombMap.ofRotation R))
      (InducedRot.inDarts G (cemb (ord N) C)) ((dartNum G).symm ⟨g, h⟩))
  else 0

theorem frA_dartNum (d : G.Dart) :
    frA G C R (dartNum G d) = dartNum G (PlanarFlow.Orbit.ret
      (PlanarFlow.Orbit.rotPerm (PlanarFlow.CombMap.ofRotation R))
      (InducedRot.inDarts G (cemb (ord N) C)) d) := by
  unfold frA
  simp only [(dartNum G d).2, ↓reduceDIte]
  simp

theorem roG_iterate (d : G.Dart) (i : ℕ) :
    (roG G R)^[i] (dartNum G d) = dartNum G (R.rot^[i] d) := by
  induction i generalizing d with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply, roG_dartNum, ih, Function.iterate_succ_apply]

theorem minimalPeriod_le_degree (d : G.Dart) :
    Function.minimalPeriod R.rot d ≤ G.degree d.fst := by
  rw [← G.dart_fst_fiber_card_eq_degree]
  have hfst : ∀ i, (R.rot^[i] d).fst = d.fst := fun i => by
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', R.fst_rot, ih]
  have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := R.rot) (x := d)
  calc Function.minimalPeriod R.rot d
      = #((range (Function.minimalPeriod R.rot d)).image fun i => R.rot^[i] d) := by
        rw [card_image_of_injOn (fun i hi j hj h => hinj (by simpa using hi) (by simpa using hj) h),
          card_range]
    _ ≤ _ := card_le_card (fun x hx => by
        obtain ⟨i, -, rfl⟩ := mem_image.1 hx
        simp only [mem_filter, mem_univ, true_and]
        exact hfst i)

/-- **The first return of the rotation** to the darts of positive rank, within `Δ` steps. -/
theorem rkA_hfr {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) :
    ∀ g < nD G, 0 < rkA G C g → ∃ n, 0 < n ∧ n ≤ Δ ∧ 0 < rkA G C ((roG G R)^[n] g) ∧
      (∀ i, 0 < i → i < n → rkA G C ((roG G R)^[i] g) = 0) ∧
      (∀ i ≤ n, (roG G R)^[i] g < nD G) ∧ (roG G R)^[n] g = frA G C R g := by
  intro g hg hp
  obtain ⟨d, rfl⟩ := exists_dart_of_lt G hg
  set A := InducedRot.inDarts G (cemb (ord N) C)
  have hA : ∀ d', d' ∈ A ↔ 0 < rkA G C (dartNum G d') := fun d' => by
    rw [rkA_pos_iff, mem_inDarts_iff]
  have hd : d ∈ A := (hA d).2 hp
  set π := PlanarFlow.Orbit.rotPerm (PlanarFlow.CombMap.ofRotation R)
  have hπ : π = R.rot := rotPerm_eq G R
  refine ⟨PlanarFlow.Orbit.retIdx π A d, PlanarFlow.Orbit.retIdx_pos d, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := PlanarFlow.Orbit.retIdx_le hd (PlanarFlow.Orbit.period_pos π d)
      (by rw [PlanarFlow.Orbit.iterate_period]; exact hd)
    have h2 := minimalPeriod_le_degree G R d
    rw [← hπ] at h2
    exact h1.trans (h2.trans (hΔ _))
  · rw [roG_iterate, ← (hA _), ← hπ]
    exact PlanarFlow.Orbit.iterate_retIdx_mem hd
  · intro i hi0 hin
    rw [roG_iterate, ← hπ]
    have := PlanarFlow.Orbit.not_mem_of_lt_retIdx hd hi0 hin
    rw [hA] at this
    omega
  · intro i _
    rw [roG_iterate]; exact (dartNum G _).2
  · rw [roG_iterate, frA_dartNum, PlanarFlow.Orbit.ret_apply_of_mem hd]
    simp only [π, rotPerm_eq]

end Piece

end PlanarSeparator
