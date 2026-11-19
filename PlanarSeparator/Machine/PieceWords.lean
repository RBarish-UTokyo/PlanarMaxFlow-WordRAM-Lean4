module

public import PlanarSeparator.Machine.SubCallR

/-!
# The words of the input of a piece, from the global dart numbering

For a graph `G` on `Fin N` with a rotation system `R`, the darts numbered by `dartNum G`
(lower tails first, then lower heads), and a vertex set `C`, the input `ltIn R ord C w` of the
separator program for the piece `C` (with `ord = List.finRange N`) is described here by the global
numbering, as a program computes it:

* `Piece.rkC C g`: the number of darts with both ends in `C` and global number `< g`;
* **`Piece.dartNum_comap`**: the number of a dart `x` of the induced graph is `rkC C` of the
  global number of `x` (`dartNum_lt_iff`: both numberings are lexicographic, and the numbering
  `cemb` of `C` is increasing);
* `Piece.ofs_lt_iff`: the darts with global number below `#{d | d.fst < v}` are those with tail
  below `v`; `Piece.card_fst_lt`: the offsets of the induced graph;
* `Piece.lift_indRot`: the induced rotation is the first return of the rotation to the darts with
  both ends in `C`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

open Finset WordRAM

namespace Piece

/-! ### Numberings -/

/-- The value of an equivalence with `Fin m` counts the smaller values. -/
theorem equiv_val {α : Type*} [Fintype α] {m : ℕ} (f : α ≃ Fin m) (a : α) :
    (f a : ℕ) = #(univ.filter fun b => f b < f a) := by
  have : univ.filter (fun b => f b < f a) = (Iio (f a)).map f.symm.toEmbedding := by
    ext b; simp only [mem_filter, mem_univ, true_and, mem_map, mem_Iio, Equiv.coe_toEmbedding]
    exact ⟨fun h => ⟨f b, h, by simp⟩, fun ⟨i, hi, e⟩ => by rw [← e]; simpa using hi⟩
  rw [this, card_map, Fin.card_Iio]

/-- The key `fst * k + snd` is lexicographic. -/
theorem dkey_lt_iff {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj] (y x : H.Dart) :
    dkey H y < dkey H x ↔ y.fst < x.fst ∨ (y.fst = x.fst ∧ y.snd < x.snd) := by
  simp only [dkey]
  have hy := y.snd.2
  have hx := x.snd.2
  have hfe : y.fst = x.fst ↔ (y.fst : ℕ) = x.fst := Fin.val_inj.symm
  rw [hfe, Fin.lt_def, Fin.lt_def]
  constructor
  · intro h
    rcases lt_trichotomy (y.fst : ℕ) x.fst with h1 | h1 | h1
    · exact Or.inl h1
    · right; refine ⟨h1, ?_⟩; rw [h1] at h; omega
    · exfalso
      have : (x.fst : ℕ) * k + k ≤ y.fst * k := by
        have := Nat.mul_le_mul_right k (show (x.fst : ℕ) + 1 ≤ y.fst by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; exact this
      omega
  · rintro (h | ⟨h1, h2⟩)
    · have : (y.fst : ℕ) * k + k ≤ x.fst * k := by
        have := Nat.mul_le_mul_right k (show (y.fst : ℕ) + 1 ≤ x.fst by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; exact this
      omega
    · rw [h1]; omega

/-- **The numbering `dartNum` is lexicographic.** -/
theorem dartNum_lt_iff {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj] (y x : H.Dart) :
    dartNum H y < dartNum H x ↔ y.fst < x.fst ∨ (y.fst = x.fst ∧ y.snd < x.snd) := by
  rw [← dkey_lt_iff]
  show ((dkeys H).orderIsoOfFin rfl).symm _ < ((dkeys H).orderIsoOfFin rfl).symm _ ↔ _
  rw [OrderIso.lt_iff_lt]
  exact Iff.rfl

/-! ### The piece -/

variable {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]

/-- The list of the vertices. -/
abbrev ord (N : ℕ) : List (Fin N) := List.finRange N

theorem mem_ord (v : Fin N) : v ∈ ord N := List.mem_finRange v

theorem clist_eq (C : Finset (Fin N)) : clist (ord N) C = (ord N).filter (· ∈ C) :=
  List.Nodup.dedup ((List.nodup_finRange N).filter _)

theorem clist_sorted (C : Finset (Fin N)) : (clist (ord N) C).SortedLT := by
  rw [clist_eq]
  exact ((List.sortedLT_finRange N).pairwise.filter _).sortedLT

/-- The numbering of `C` is increasing. -/
theorem cemb_lt_iff (C : Finset (Fin N)) (i j : Fin (clist (ord N) C).length) :
    cemb (ord N) C i < cemb (ord N) C j ↔ i < j := by
  have hs := clist_sorted C
  have hmono : StrictMono (clist (ord N) C).get := hs.strictMono_get
  exact hmono.lt_iff_lt

theorem cemb_le_iff (C : Finset (Fin N)) (i j : Fin (clist (ord N) C).length) :
    cemb (ord N) C i ≤ cemb (ord N) C j ↔ i ≤ j := by
  rw [← not_lt, ← not_lt, cemb_lt_iff]

/-- The number of darts with both ends in `C` and global number `< g`. -/
noncomputable def rkC (C : Finset (Fin N)) (g : ℕ) : ℕ :=
  #(univ.filter fun d : G.Dart => d.fst ∈ C ∧ d.snd ∈ C ∧ (dartNum G d : ℕ) < g)

theorem mem_inDarts_iff (C : Finset (Fin N)) {d : G.Dart} :
    d ∈ InducedRot.inDarts G (cemb (ord N) C) ↔ d.fst ∈ C ∧ d.snd ∈ C := by
  rw [InducedRot.mem_inDarts, map_cemb mem_ord]

theorem lift_lt_iff (C : Finset (Fin N)) (y x : (G.comap (cemb (ord N) C)).Dart) :
    dartNum G (InducedRot.lift G (cemb (ord N) C) y) <
        dartNum G (InducedRot.lift G (cemb (ord N) C) x) ↔
      dartNum _ y < dartNum _ x := by
  rw [dartNum_lt_iff, dartNum_lt_iff]
  simp only [InducedRot.lift]
  show cemb (ord N) C y.fst < cemb (ord N) C x.fst ∨
      (cemb (ord N) C y.fst = cemb (ord N) C x.fst ∧ cemb (ord N) C y.snd < cemb (ord N) C x.snd) ↔ _
  rw [cemb_lt_iff, cemb_lt_iff, (cemb (ord N) C).injective.eq_iff]

/-- Counting the darts of the induced graph through `lift`. -/
theorem card_lift (C : Finset (Fin N)) (p : G.Dart → Prop) [DecidablePred p] :
    #(univ.filter fun y : (G.comap (cemb (ord N) C)).Dart =>
        p (InducedRot.lift G (cemb (ord N) C) y)) =
      #(univ.filter fun d : G.Dart => d.fst ∈ C ∧ d.snd ∈ C ∧ p d) := by
  refine card_bij (fun y _ => InducedRot.lift G (cemb (ord N) C) y) (fun y hy => ?_)
    (fun y _ y' _ h => ?_) (fun d hd => ?_)
  · simp only [mem_filter, mem_univ, true_and] at hy ⊢
    exact ⟨((mem_inDarts_iff G C).1 (InducedRot.lift_mem G _ y)).1,
      ((mem_inDarts_iff G C).1 (InducedRot.lift_mem G _ y)).2, hy⟩
  · exact (InducedRot.iDartE G _).injective (Subtype.ext h)
  · simp only [mem_filter, mem_univ, true_and] at hd ⊢
    obtain ⟨h1, h2, h3⟩ := hd
    have hm : d ∈ InducedRot.inDarts G (cemb (ord N) C) := (mem_inDarts_iff G C).2 ⟨h1, h2⟩
    refine ⟨(InducedRot.iDartE G _).symm ⟨d, hm⟩, ?_, ?_⟩
    · rw [← InducedRot.iDartE_val, Equiv.apply_symm_apply]; exact h3
    · rw [← InducedRot.iDartE_val, Equiv.apply_symm_apply]

/-- **The number of a dart of the induced graph** is the number of darts with both ends in `C`
before it in the global numbering. -/
theorem dartNum_comap (C : Finset (Fin N)) (x : (G.comap (cemb (ord N) C)).Dart) :
    (dartNum _ x : ℕ) = rkC G C (dartNum G (InducedRot.lift G (cemb (ord N) C) x)) := by
  rw [equiv_val (dartNum _) x, rkC]
  simp_rw [← lift_lt_iff G C, Fin.lt_def]
  exact card_lift G C (fun d => (dartNum G d : ℕ) < dartNum G (InducedRot.lift G _ x))

/-- The number of darts of the induced graph. -/
theorem card_comap (C : Finset (Fin N)) :
    (dkeys (G.comap (cemb (ord N) C))).card =
      #(univ.filter fun d : G.Dart => d.fst ∈ C ∧ d.snd ∈ C) := by
  have h1 : (dkeys (G.comap (cemb (ord N) C))).card =
      Fintype.card (G.comap (cemb (ord N) C)).Dart := by
    rw [Fintype.card_congr (dartNum _), Fintype.card_fin]
  have := card_lift G C (fun _ => True)
  simp only [and_true] at this
  rw [h1, ← this, filter_true_of_mem (fun _ _ => trivial), card_univ]

/-! ### Offsets -/

/-- The global offsets. -/
noncomputable def gofs (v : ℕ) : ℕ := #(univ.filter fun d : G.Dart => (d.fst : ℕ) < v)

/-- **The darts numbered below the offset of `v`** are the darts with tail below `v`. -/
theorem ofs_lt_iff (d : G.Dart) (v : ℕ) : (dartNum G d : ℕ) < gofs G v ↔ (d.fst : ℕ) < v := by
  constructor
  · intro h
    by_contra hv
    have hsub : univ.filter (fun d' : G.Dart => (d'.fst : ℕ) < v) ⊆
        univ.filter fun d' => dartNum G d' < dartNum G d := by
      intro d' hd'
      simp only [mem_filter, mem_univ, true_and] at hd' ⊢
      rw [dartNum_lt_iff]; left; rw [Fin.lt_def]; omega
    have := card_le_card hsub
    rw [← equiv_val] at this
    unfold gofs at h; omega
  · intro h
    have hsub : univ.filter (fun d' : G.Dart => dartNum G d' < dartNum G d) ∪ {d} ⊆
        univ.filter fun d' : G.Dart => (d'.fst : ℕ) < v := by
      intro d' hd'
      simp only [mem_union, mem_filter, mem_univ, true_and, mem_singleton] at hd' ⊢
      rcases hd' with hd' | rfl
      · rw [dartNum_lt_iff] at hd'
        rcases hd' with hd' | ⟨hd', -⟩
        · rw [Fin.lt_def] at hd'; omega
        · rw [hd']; exact h
      · exact h
    have := card_le_card hsub
    rw [card_union_of_disjoint (disjoint_singleton_right.2 (by simp)), card_singleton,
      ← equiv_val] at this
    unfold gofs; omega

theorem ofs_le_iff (d : G.Dart) (v : ℕ) : gofs G v ≤ (dartNum G d : ℕ) ↔ v ≤ (d.fst : ℕ) := by
  rw [← not_lt, ofs_lt_iff, not_lt]

/-- **The offsets of the induced graph.** -/
theorem card_fst_lt (C : Finset (Fin N)) {j : ℕ} (hj : j < (clist (ord N) C).length) :
    #(univ.filter fun x : (G.comap (cemb (ord N) C)).Dart => (x.fst : ℕ) < j) =
      rkC G C (gofs G (cemb (ord N) C ⟨j, hj⟩)) := by
  have : ∀ x : (G.comap (cemb (ord N) C)).Dart, (x.fst : ℕ) < j ↔
      (dartNum G (InducedRot.lift G (cemb (ord N) C) x) : ℕ) <
        gofs G (cemb (ord N) C ⟨j, hj⟩) := fun x => by
    rw [ofs_lt_iff]
    show _ ↔ ((cemb (ord N) C x.fst : Fin N) : ℕ) < (cemb (ord N) C ⟨j, hj⟩ : Fin N)
    rw [← Fin.lt_def, cemb_lt_iff, Fin.lt_def]
  simp_rw [this]
  rw [card_lift G C (fun d => (dartNum G d : ℕ) < gofs G (cemb (ord N) C ⟨j, hj⟩))]
  rfl

theorem card_fst_lt_length (C : Finset (Fin N)) :
    #(univ.filter fun x : (G.comap (cemb (ord N) C)).Dart =>
        (x.fst : ℕ) < (clist (ord N) C).length) =
      #(univ.filter fun d : G.Dart => d.fst ∈ C ∧ d.snd ∈ C) := by
  have := card_lift G C (fun _ => True)
  simp only [and_true] at this
  rw [← this]
  congr 1; ext x; simp

/-! ### The rotation -/

variable (R : Kasteleyn.RotationSystem G)

theorem rotPerm_ofRotation (d : G.Dart) :
    PlanarFlow.Orbit.rotPerm (PlanarFlow.CombMap.ofRotation R) d = R.rot d := by
  show R.rot d.symm.symm = R.rot d
  rw [SimpleGraph.Dart.symm_symm]

/-- **The induced rotation is the first return.** -/
theorem lift_indRot (C : Finset (Fin N)) (x : (G.comap (cemb (ord N) C)).Dart) :
    InducedRot.lift G (cemb (ord N) C) ((InducedRot.indRot R (cemb (ord N) C)).rot x) =
      PlanarFlow.Orbit.ret (PlanarFlow.Orbit.rotPerm (PlanarFlow.CombMap.ofRotation R))
        (InducedRot.inDarts G (cemb (ord N) C)) (InducedRot.lift G (cemb (ord N) C) x) := by
  rw [← InducedRot.iDartE_val]
  show ((InducedRot.iDartE G _) ((InducedRot.iDartE G _).symm
    (InducedRot.iRotB R _ (InducedRot.iDartE G _ x)))).1 = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem lift_symm (C : Finset (Fin N)) (x : (G.comap (cemb (ord N) C)).Dart) :
    InducedRot.lift G (cemb (ord N) C) x.symm = (InducedRot.lift G (cemb (ord N) C) x).symm :=
  rfl

/-! ### The words of the piece -/

theorem length_sepInput {n m : ℕ} {H : SimpleGraph (Fin n)} [DecidableRel H.Adj]
    (Rh : Kasteleyn.RotationSystem H) (wh : Fin n → ℕ) (di : H.Dart ≃ Fin m) :
    (sepInput Rh wh di).data.length = 2 * n + 3 + 3 * m := by
  unfold sepInput; simp; omega

/-- The darts of the induced graph through `lift`, from a dart with both ends in `C`. -/
theorem exists_lift (C : Finset (Fin N)) {d : G.Dart} (h1 : d.fst ∈ C) (h2 : d.snd ∈ C) :
    ∃ x : (G.comap (cemb (ord N) C)).Dart, InducedRot.lift G (cemb (ord N) C) x = d :=
  ⟨(InducedRot.iDartE G _).symm ⟨d, (mem_inDarts_iff G C).2 ⟨h1, h2⟩⟩, by
    rw [← InducedRot.iDartE_val, Equiv.apply_symm_apply]⟩

/-- **The words of `ltIn R ord C w`, from the global numbering of the darts.** With
`k = #C` vertices numbered in increasing order by `cemb` and `m'` darts with both ends in `C`:
the words `k`, `m'`; the offsets `rkC (gofs (cemb j))` and `m'`; the weights; and for a dart `d`
with both ends in `C`, at position `rkC (dartNum d)` of the dart list, the number of its tail,
`rkC` of its reversal and `rkC` of the first return of the rotation to the darts inside `C`. Every
position of the dart list is the position of such a dart. -/
theorem ltIn_words (C : Finset (Fin N)) (w : Fin N → ℕ) :
    let k := (clist (ord N) C).length
    let m' := #(univ.filter fun d : G.Dart => d.fst ∈ C ∧ d.snd ∈ C)
    let D := (ltIn R (ord N) C w).data
    D.length = 2 * k + 3 + 3 * m' ∧ D.getD 0 0 = k ∧ D.getD 1 0 = m' ∧
    (∀ j (hj : j < k), D.getD (2 + j) 0 = rkC G C (gofs G (cemb (ord N) C ⟨j, hj⟩))) ∧
    D.getD (2 + k) 0 = m' ∧
    (∀ j (hj : j < k), D.getD (k + 3 + j) 0 = w (cemb (ord N) C ⟨j, hj⟩)) ∧
    (∀ d : G.Dart, d.fst ∈ C → d.snd ∈ C →
      rkC G C (dartNum G d) < m' ∧
      (∀ j (hj : j < k), cemb (ord N) C ⟨j, hj⟩ = d.fst →
        D.getD (2 * k + 3 + 3 * rkC G C (dartNum G d)) 0 = j) ∧
      D.getD (2 * k + 3 + 3 * rkC G C (dartNum G d) + 1) 0 = rkC G C (dartNum G d.symm) ∧
      D.getD (2 * k + 3 + 3 * rkC G C (dartNum G d) + 2) 0 =
        rkC G C (dartNum G (PlanarFlow.Orbit.ret
          (PlanarFlow.Orbit.rotPerm (PlanarFlow.CombMap.ofRotation R))
          (InducedRot.inDarts G (cemb (ord N) C)) d))) ∧
    (∀ i < m', ∃ d : G.Dart, d.fst ∈ C ∧ d.snd ∈ C ∧ rkC G C (dartNum G d) = i) := by
  intro k m' D
  set e := cemb (ord N) C
  set H := G.comap e
  have hm' : (dkeys H).card = m' := card_comap G C
  have hIn := SepProg.inHolds_sepInput (InducedRot.indRot R e) (fun i => w (e i)) (dartNum H)
  have hD : D = (sepInput (InducedRot.indRot R e) (fun i => w (e i)) (dartNum H)).data := rfl
  rw [hD]
  -- the dart of `H` above a dart of `G`
  have hx : ∀ d : G.Dart, d.fst ∈ C → d.snd ∈ C → ∃ x : H.Dart,
      InducedRot.lift G e x = d ∧ (dartNum H x : ℕ) = rkC G C (dartNum G d) := by
    intro d h1 h2
    obtain ⟨x, hx⟩ := exists_lift G C h1 h2
    exact ⟨x, hx, by rw [dartNum_comap, hx]⟩
  refine ⟨?_, ?_, ?_, fun j hj => ?_, ?_, fun j hj => ?_, fun d h1 h2 => ?_, fun i hi => ?_⟩
  · rw [length_sepInput, hm']
  · rw [hIn.n_eq]
  · rw [hIn.m_eq, hm']
  · rw [hIn.ofs_eq j hj.le, SepProg.ofsI, card_fst_lt G C hj]
  · rw [hIn.ofs_eq k le_rfl, SepProg.ofsI]; exact card_fst_lt_length G C
  · rw [show k + 3 + j = k + 3 + j from rfl, hIn.w_eq j hj]; unfold SepProg.wI
    exact dite_eq_left_of_eq_true (eq_true (show j < (clist (ord N) C).length from hj))
  · obtain ⟨x, hxd, hxi⟩ := hx d h1 h2
    have hlt : (dartNum H x : ℕ) < (dkeys H).card := (dartNum H x).2
    have hsym : (dartNum H).symm ⟨rkC G C (dartNum G d), by rw [← hxi]; exact hlt⟩ = x := by
      rw [Equiv.symm_apply_eq]; exact Fin.ext hxi.symm
    have hi : rkC G C (dartNum G d) < (dkeys H).card := by rw [← hxi]; exact hlt
    refine ⟨by rw [← hm']; exact hi, fun j hj hj' => ?_, ?_, ?_⟩
    · rw [hIn.tl_eq _ hi]; simp only [SepProg.tlI, hi, ↓reduceDIte]; rw [hsym]
      have : e x.fst = e ⟨j, hj⟩ := by
        rw [hj']; show (InducedRot.lift G e x).fst = _; rw [hxd]
      rw [e.injective this]
    · rw [hIn.rv_eq _ hi]; simp only [SepProg.rvI, hi, ↓reduceDIte]
      rw [hsym, dartNum_comap, lift_symm, hxd]
    · rw [hIn.ro_eq _ hi]; simp only [SepProg.roI, hi, ↓reduceDIte]
      rw [hsym, dartNum_comap, lift_indRot, hxd]
  · rw [← hm'] at hi
    set x := (dartNum H).symm ⟨i, hi⟩
    have h := InducedRot.lift_mem G e x
    rw [mem_inDarts_iff] at h
    refine ⟨InducedRot.lift G e x, h.1, h.2, ?_⟩
    rw [← dartNum_comap]; show ((dartNum H) x : ℕ) = i; simp [x]

end Piece

end PlanarSeparator
