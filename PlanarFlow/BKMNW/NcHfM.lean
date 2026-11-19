module

public import PlanarFlow.BKMNW.NcHfRun
public import PlanarFlow.BKMNW.NcTfM
public import PlanarFlow.BKMNW.LgNf
public import PlanarFlow.BKMNW.NpCntM

/-!
# The hole flags of `hfP` are the flags of the hole of the piece map

At a frame (`Lay`, holes pairwise disjoint), the label `v = hfV mem HLb m i` chosen by `hfP` from
the frame's hole labels `HL` (`HLb = d + 4 + 5m`) is `J + 1` where `pholes[i] = vimg Hs[J]`:

* `holeQ` (`vimg Hs[J]` nonempty), `holeQ_iff` (some dart has the label `J + 1`),
  `posVals_hl` (the positive labels are the `J + 1` with `holeQ J`), `filter_take_length`
  (the number of holes of the piece map among the first `J`), `filter_getElem?_of`;
* **`hfV_hole`**: for `pholes[i]? = some H`: `0 < v`, `v - 1 < #Hs`,
  `H = vimg Hs[v - 1]`;
* `mk_mem_vimg_hole` (a dart of the piece map is in the image of the hole `Hs[J]` iff its tail is
  in `Hs[J]`), **`hfFlag_hole`**: `[HL[t] = v] = flagX (pmap h) (layEn …) H t` — the flag input of
  `stCallZ_lay` for the sink `H`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open Finset Function Equiv Orbit CombMap MfDrv NsStep StCall

universe w

/-- **The element of a filtered list at the count of the earlier hits.** -/
lemma filter_getElem?_of {α : Type*} (l : List α) (p : α → Bool) {J : ℕ} (hJ : J < l.length)
    (hp : p l[J] = true) {i : ℕ} (hi : ((l.take J).filter p).length = i) :
    (l.filter p)[i]? = some l[J] := by
  have e : l = l.take J ++ l[J] :: l.drop (J + 1) := by
    conv_lhs => rw [← List.take_append_drop J l]
    rw [List.drop_eq_getElem_cons hJ]
  conv_lhs => rw [e]
  rw [List.filter_append, List.filter_cons_of_pos (by simpa using hp),
    List.getElem?_append_right (by rw [hi]), hi, Nat.sub_self]
  simp

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-- The image of the hole `J` in the piece map is nonempty. -/
def holeQ (x : MCall M) (J : ℕ) : Prop :=
  (vimg M x.2.2 (pdarts M x.1.piece x.2.1) (x.2.1.getD J ∅)).Nonempty

/-- `holeQ J` iff some dart of the frame has the label `J + 1`. -/
lemma holeQ_iff {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (hd : x.2.1.Pairwise Disjoint) {J : ℕ}
    (hJ : J < x.2.1.length) :
    holeQ x J ↔ ∃ t < m, mem (d + 4 + 5 * m + t) = J + 1 := by
  unfold holeQ
  rw [vimg_nonempty_iff]
  constructor
  · rintro ⟨y, hy, ht⟩
    obtain ⟨i, hi, rfl⟩ := hL.en_surj y hy
    exact ⟨i, hi, by rw [hL.hl i hi]; exact (hlab_eq_succ_iff hd hJ).2 ht⟩
  · rintro ⟨i, hi, he⟩
    rw [hL.hl i hi] at he
    exact ⟨en i, hL.en_mem i hi, (hlab_eq_succ_iff hd hJ).1 he⟩

/-- The positive labels of the frame are the `J + 1` with `holeQ J`. -/
lemma posVals_hl {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (hd : x.2.1.Pairwise Disjoint) {v : ℕ} :
    v ∈ posVals (segL mem (d + 4 + 5 * m) m) ↔
      0 < v ∧ v - 1 < x.2.1.length ∧ holeQ x (v - 1) := by
  classical
  rw [mem_posVals]
  constructor
  · rintro ⟨hv, hpos⟩
    obtain ⟨t, ht, rfl⟩ : ∃ t < m, mem (d + 4 + 5 * m + t) = v := by
      unfold segL at hv
      obtain ⟨t, ht, e⟩ := List.mem_map.1 hv
      exact ⟨t, List.mem_range.1 ht, e⟩
    have hlab := hL.hl t ht
    rw [hlab] at hpos ⊢
    obtain ⟨hlt, -⟩ := hlab_mem hpos
    refine ⟨hpos, hlt, (holeQ_iff hL hd hlt).2 ⟨t, ht, ?_⟩⟩
    rw [hlab]; omega
  · rintro ⟨hpos, hlt, hq⟩
    obtain ⟨t, ht, e⟩ := (holeQ_iff hL hd hlt).1 hq
    refine ⟨?_, hpos⟩
    unfold segL
    exact List.mem_map.2 ⟨t, List.mem_range.2 ht, by rw [e]; omega⟩

open Classical in
/-- The positive labels below `J + 1`. -/
lemma posVals_hl_filter {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (hd : x.2.1.Pairwise Disjoint) {J : ℕ}
    (hJ : J < x.2.1.length) :
    ((posVals (segL mem (d + 4 + 5 * m) m)).filter (· < J + 1)).card =
      ((range J).filter (holeQ x)).card := by
  classical
  have e : (posVals (segL mem (d + 4 + 5 * m) m)).filter (· < J + 1) =
      ((range J).filter (holeQ x)).image (· + 1) := by
    ext v
    simp only [mem_filter, posVals_hl hL hd, mem_image, mem_range]
    constructor
    · rintro ⟨⟨hpos, hlt, hq⟩, hvJ⟩
      exact ⟨v - 1, ⟨by omega, hq⟩, by omega⟩
    · rintro ⟨J', ⟨hJ', hq⟩, rfl⟩
      exact ⟨⟨by omega, by simp; omega, by simpa using hq⟩, by omega⟩
  rw [e, card_image_of_injective _ (fun a b h => by simpa using h)]

open Classical in
/-- The number of holes of the piece map among the first `J` holes. -/
lemma filter_take_length (x : MCall M) {J : ℕ} (hJ : J ≤ x.2.1.length) :
    (((x.2.1.map (vimg M x.2.2 (pdarts M x.1.piece x.2.1))).take J).filter
      (fun H => decide H.Nonempty)).length = ((range J).filter (holeQ x)).card := by
  classical
  rw [length_filter_eq_sum _ ∅, card_filter]
  simp only [List.length_take, List.length_map, show min J x.2.1.length = J by omega]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  have e : ((x.2.1.map (vimg M x.2.2 (pdarts M x.1.piece x.2.1))).take J).getD j ∅ =
      vimg M x.2.2 (pdarts M x.1.piece x.2.1) (x.2.1.getD j ∅) := by
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_take, List.getElem_map,
      List.getD_eq_getElem _ _ (by omega)]
  rw [e]
  unfold holeQ
  simp

/-- **The label chosen by `hfP` is that of the hole `i` of the piece map.** -/
theorem hfV_hole {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (hd : x.2.1.Pairwise Disjoint) {i : ℕ}
    {H : Finset (SVert x.2.2 (pdarts M x.1.piece x.2.1))}
    (hi : (pholes M x.2.2 (pdarts M x.1.piece x.2.1) x.2.1)[i]? = some H) :
    0 < hfV mem (d + 4 + 5 * m) m i ∧ hfV mem (d + 4 + 5 * m) m i - 1 < x.2.1.length ∧
      H = vimg M x.2.2 (pdarts M x.1.piece x.2.1)
        (x.2.1.getD (hfV mem (d + 4 + 5 * m) m i - 1) ∅) := by
  classical
  have hlen : i < (pholes M x.2.2 (pdarts M x.1.piece x.2.1) x.2.1).length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hi; cases hi
  -- the number of holes of the piece map
  have hcnt : (pholes M x.2.2 (pdarts M x.1.piece x.2.1) x.2.1).length =
      (posVals (segL mem (d + 4 + 5 * m) m)).card := by
    have e1 := filter_take_length (M := M) x (le_refl x.2.1.length)
    rw [List.take_of_length_le (by simp)] at e1
    unfold pholes
    rw [e1]
    have e2 : posVals (segL mem (d + 4 + 5 * m) m) =
        ((range x.2.1.length).filter (holeQ x)).image (· + 1) := by
      ext v
      simp only [posVals_hl hL hd, mem_image, mem_filter, mem_range]
      constructor
      · rintro ⟨hpos, hlt, hq⟩; exact ⟨v - 1, ⟨hlt, hq⟩, by omega⟩
      · rintro ⟨J', ⟨hJ', hq⟩, rfl⟩; exact ⟨by omega, by simpa using hJ', by simpa using hq⟩
    rw [e2, card_image_of_injective _ (fun a b h => by simpa using h)]
  obtain ⟨hmem, hcard⟩ := hfV_spec (mem := mem) (HLb := d + 4 + 5 * m) (m := m) (i := i)
    (by rw [← hcnt]; exact hlen)
  obtain ⟨hpos, hlt, hq⟩ := (posVals_hl hL hd).1 hmem
  refine ⟨hpos, hlt, ?_⟩
  set J := hfV mem (d + 4 + 5 * m) m i - 1 with hJdef
  have hvJ : hfV mem (d + 4 + 5 * m) m i = J + 1 := by omega
  rw [hvJ, posVals_hl_filter hL hd hlt, ← filter_take_length x hlt.le] at hcard
  have hJl : J < (x.2.1.map (vimg M x.2.2 (pdarts M x.1.piece x.2.1))).length := by simpa using hlt
  have := filter_getElem?_of _ (fun H => decide H.Nonempty) hJl
    (by simp only [List.getElem_map, decide_eq_true_eq]
        have := hq; unfold holeQ at this; rwa [List.getD_eq_getElem _ _ hlt] at this) hcard
  unfold pholes at hi
  rw [List.filter_map] at hi this
  rw [hi, List.getElem_map] at this
  rw [Option.some_inj.1 this, List.getD_eq_getElem _ _ hlt]

/-- **A dart of the piece map is in the image of a hole iff its tail is in the hole.** -/
lemma mk_mem_vimg_hole {P : Finset D} {Hs : List (Finset V)} {σ : Perm D}
    (h : PieceInv M P Hs σ) (hd : Hs.Pairwise Disjoint) {J : ℕ} (hJ : J < Hs.length)
    {x : SDart (pdarts M P Hs)} :
    Quotient.mk _ x ∈ vimg M σ (pdarts M P Hs) (Hs.getD J ∅) ↔ M.tail x.1 ∈ Hs.getD J ∅ := by
  rw [mk_mem_vimg h]
  constructor
  · rintro ⟨y, -, hy, e⟩
    have hpos : hlab Hs (M.tail y) = J + 1 := (hlab_eq_succ_iff hd hJ).2 hy
    have := (hRel_iff_hlab_of_pos hd (a := M.tail x.1) (v := M.tail y) (by omega)).1
      (hRel_symm e)
    exact (hlab_eq_succ_iff hd hJ).1 (by rw [this, hpos])
  · intro hx; exact ⟨x.1, x.2, hx, Or.inl rfl⟩

/-- **The flags of `hfP` are the flags of the hole `i` of the piece map.** -/
theorem hfFlag_hole {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (h : PieceInv M x.1.piece x.2.1 x.2.2)
    (hd : x.2.1.Pairwise Disjoint) (hm : 0 < m) {i : ℕ}
    {H : Finset (SVert x.2.2 (pdarts M x.1.piece x.2.1))}
    (hi : (pholes M x.2.2 (pdarts M x.1.piece x.2.1) x.2.1)[i]? = some H) {t : ℕ} (ht : t < m) :
    (if mem (d + 4 + 5 * m + t) = hfV mem (d + 4 + 5 * m) m i then 1 else 0) =
      flagX (pmap h) (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm) H t := by
  obtain ⟨hpos, hlt, rfl⟩ := hfV_hole hL hd hi
  have hlay : layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm t = ⟨en t, hL.en_mem t ht⟩ := by
    unfold layEn; simp only [ht, ↓reduceDIte]
  unfold flagX
  rw [hlay, pmap_tail, hL.hl t ht]
  have key : hlab x.2.1 (M.tail (en t)) = hfV mem (d + 4 + 5 * m) m i ↔
      M.tail (en t) ∈ x.2.1.getD (hfV mem (d + 4 + 5 * m) m i - 1) ∅ := by
    rw [← hlab_eq_succ_iff hd hlt]; constructor <;> intro e <;> omega
  by_cases hv : M.tail (en t) ∈ x.2.1.getD (hfV mem (d + 4 + 5 * m) m i - 1) ∅
  · rw [iteT (key.2 hv), iteT ((mk_mem_vimg_hole h hd hlt).2 hv)]
  · rw [iteF (fun e => hv (key.1 e)), iteF (fun e => hv ((mk_mem_vimg_hole h hd hlt).1 e))]

end NcStep

end BKMNW

end PlanarFlow
