module

public import PlanarFlow.BKMNW.NcTfRun
public import PlanarFlow.BKMNW.NpDiv
public import PlanarFlow.BKMNW.StCall
public import PlanarFlow.BKMNW.NsLay

/-!
# The flags of `tfP` are the flags of a part of the separator

At a frame (`Lay`) with the labels of `dvP` (`LAB[j] = olab (sgF d m mem) j + 1`), the list of the
darts of a path `π` of `M` off the holes (`en (L[t]) = π.d t`, as `SegsOut` stores the parts), the
reversals of the frame and a dart `s` with tail `π.p 0`, the flag of `tfP` is the flag
`[tail ∈ vimg π.verts]` of the piece map — the input `flagX` of the s-t flow call
(`stCallZ_lay`) for the part, `vimg … π.verts` being the vertex set of the part in the piece map
(`segsP_verts`).

* `lab_eq_iff_tail` (two labels agree iff the tails agree, the first tail off the holes);
* **`tfFlag_path`**.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open Finset Function Equiv Orbit CombMap MfDrv NsStep StCall OrbLab

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-- **Two labels agree iff the tails agree**, when the first tail is off the holes. -/
lemma lab_eq_iff_tail {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (h : PieceInv M x.1.piece x.2.1 x.2.2) {a b : ℕ}
    (ha : a < m) (hb : b < m) (hA : M.tail (en a) ∉ hunion x.2.1) :
    olab (sgF d m mem) a = olab (sgF d m mem) b ↔ M.tail (en b) = M.tail (en a) := by
  rw [← hL.vert_eq_iff h ha hb, pmap_tail, pmap_tail]
  constructor
  · intro e
    exact (hRel_of_not_mem hA).1 ((h.vert _ (hL.en_mem a ha) _ (hL.en_mem b hb)).1
      (Quotient.exact e))
  · intro e
    exact Quotient.sound ((h.vert _ (hL.en_mem a ha) _ (hL.en_mem b hb)).2
      ((hRel_of_not_mem hA).2 e))

/-- **The flags of `tfP` for a path off the holes are the flags of its vertex set in the piece
map.** -/
theorem tfFlag_path {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (h : PieceInv M x.1.piece x.2.1 x.2.2) (hm : 0 < m)
    (π : SPath M) (hX : Disjoint π.verts (hunion x.2.1)) {mem' : ℕ → ℕ} {LABb Lb RVb s : ℕ}
    (hLAB : ∀ j < m, mem' (LABb + j) = olab (sgF d m mem) j + 1)
    (hLs : ∀ t < π.k, mem' (Lb + t) < m ∧ en (mem' (Lb + t)) = π.d t)
    (hRV : ∀ j < m, mem' (RVb + j) = mem (d + 4 + m + j))
    (hs : s < m) (hst : M.tail (en s) = π.p 0) {i : ℕ} (hi : i < m) :
    tfFlag mem' LABb Lb RVb π.k s (mem' (LABb + i)) =
      flagX (pmap h) (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm)
        (vimg M x.2.2 (pdarts M x.1.piece x.2.1) π.verts) i := by
  classical
  have hlay : layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm i = ⟨en i, hL.en_mem i hi⟩ := by
    unfold layEn; simp only [hi, ↓reduceDIte]
  have hoff : ∀ v ∈ π.verts, v ∉ hunion x.2.1 := fun v hv => disjoint_left.1 hX hv
  -- the right side
  have eR : flagX (pmap h) (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm)
      (vimg M x.2.2 (pdarts M x.1.piece x.2.1) π.verts) i =
      if M.tail (en i) ∈ π.verts then 1 else 0 := by
    unfold flagX
    rw [hlay, pmap_tail]
    by_cases hv : M.tail (en i) ∈ π.verts
    · rw [iteT ((mk_mem_vimg_iff h hX).2 hv), iteT hv]
    · rw [iteF (fun h' => hv ((mk_mem_vimg_iff h hX).1 h')), iteF hv]
  rw [eR]
  unfold tfFlag
  congr 1
  apply propext
  rw [hLAB i hi]
  unfold tfHit
  rw [hLAB s hs]
  -- the three kinds of hits
  have k0 : olab (sgF d m mem) s + 1 = olab (sgF d m mem) i + 1 ↔ M.tail (en i) = π.p 0 := by
    rw [Nat.add_right_cancel_iff, lab_eq_iff_tail hL h hs hi
      (by rw [hst]; exact hoff _ (π.p_mem_init (Nat.zero_le _))), hst]
  have k1 : ∀ t < π.k, mem' (LABb + mem' (Lb + t)) = olab (sgF d m mem) i + 1 ↔
      M.tail (en i) = π.p t := fun t ht => by
    obtain ⟨hlt, he⟩ := hLs t ht
    have htl : M.tail (en (mem' (Lb + t))) = π.p t := by rw [he, π.tail_d t ht]
    rw [hLAB _ hlt, Nat.add_right_cancel_iff, lab_eq_iff_tail hL h hlt hi
      (by rw [htl]; exact hoff _ (π.p_mem_init ht.le)), htl]
  have k2 : ∀ t < π.k, mem' (LABb + mem' (RVb + mem' (Lb + t))) = olab (sgF d m mem) i + 1 ↔
      M.tail (en i) = π.p (t + 1) := fun t ht => by
    obtain ⟨hlt, he⟩ := hLs t ht
    obtain ⟨hr, hre⟩ := hL.rv _ hlt
    have htl : M.tail (en (mem (d + 4 + m + mem' (Lb + t)))) = π.p (t + 1) := by
      rw [hre, he, M.tail_rev, π.head_d t ht]
    rw [hRV _ hlt, hLAB _ hr, Nat.add_right_cancel_iff, lab_eq_iff_tail hL h hr hi
      (by rw [htl]; exact hoff _ (π.p_mem_init (by omega))), htl]
  constructor
  · rintro (h0 | ⟨t, ht, h1 | h2⟩)
    · rw [k0.1 h0]; exact π.p_mem_init (Nat.zero_le _)
    · rw [(k1 t ht).1 h1]; exact π.p_mem_init ht.le
    · rw [(k2 t ht).1 h2]; exact π.p_mem_init (by omega)
  · intro hv
    obtain ⟨l, hl, e⟩ := π.mem_init.1 hv
    rcases Nat.eq_zero_or_pos l with rfl | hl0
    · exact Or.inl (k0.2 e.symm)
    · obtain ⟨t, rfl⟩ : ∃ t, l = t + 1 := ⟨l - 1, by omega⟩
      exact Or.inr ⟨t, by omega, Or.inr ((k2 t (by omega)).2 e.symm)⟩

end NcStep

end BKMNW

end PlanarFlow
