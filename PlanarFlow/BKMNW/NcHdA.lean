module

public import PlanarFlow.BKMNW.NcHd
public import PlanarFlow.BKMNW.NcTfS

/-!
# The head of `c2sP`, stages A and B: the labels and the terminal flags

* `segs_sum` (the total number of darts of the parts from `SegsOut`:
  `mem (Gb + s) + mem (Gb + s + s)`), `SPath.k_lt_card` (`k + 1 ≤ #V` for a simple path);
* **`hdLab_exec`**: `r8430 := b + m ; dvP` writes `LAB = olab + 1` at `b + m`, the net outflows
  `DV`, `DG` at `b + 2m`, `b + 3m` with `DV[LAB i − 1] − Z · DG[LAB i − 1] = div g (tail i)`;
* **`hdTf_exec`**: `tfGl rj Vr Fr ; tfP` (the part whose index is in `rj`, read from `SegsOut'`)
  writes at `Fb` the flags `flagX (pmap h) (layEn …) (segsP …)[jj].verts` of the part `jj`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open Finset Function Equiv Orbit CombMap MfDrv NsStep StCall OrbLab WordRAM WordRAM.Machine
  WordRAM.Machine.Stmt WordRAM.Programs

universe w

/-- A simple path has at most `#V − 1` darts. -/
lemma SPath.k_lt_card {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V']
    [DecidableEq V'] [Fintype F'] [DecidableEq F'] {M' : CombMap D' V' F'} (P : SPath M') :
    P.k + 1 ≤ Fintype.card V' := by
  have h : ((range (P.k + 1)).image P.p).card = P.k + 1 := by
    rw [card_image_of_injOn (fun i hi j hj e => P.inj i (by simp at hi; omega) j
      (by simp at hj; omega) e), card_range]
  rw [← h]
  exact card_le_univ _

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-- **The total number of darts of the parts** read from `SegsOut` (two words). -/
lemma segs_sum {en : ℕ → D} {m : ℕ} {π : HSep M} {lo hi Gb : ℕ} {mem : ℕ → ℕ}
    (hS : SegsOut M en m π lo hi Gb mem) (hs : 0 < π.segs.length) :
    mem (Gb + π.segs.length) + mem (Gb + π.segs.length + π.segs.length) =
      (π.segs.map SPath.k).sum := by
  obtain ⟨-, -, -, h4⟩ := hS
  obtain ⟨g1, g2, -⟩ := h4 (π.segs.length - 1) (by omega)
  rw [show Gb + 1 + (π.segs.length - 1) = Gb + π.segs.length by omega] at g1
  rw [show Gb + 1 + π.segs.length + (π.segs.length - 1) = Gb + π.segs.length + π.segs.length by
    omega] at g2
  rw [g1, g2, List.map_take]
  have := List.sum_take_succ (π.segs.map SPath.k) (π.segs.length - 1) (by simp; omega)
  rw [show π.segs.length - 1 + 1 = π.segs.length by omega,
    List.take_of_length_le (by simp)] at this
  simp only [List.getElem_map] at this
  omega

/-- The darts of the part `j` lie below the end of the list of darts. -/
lemma segs_take_add_le {π : HSep M} {j : ℕ} (hj : j < π.segs.length) :
    ((π.segs.take j).map SPath.k).sum + (π.segs[j]).k ≤ (π.segs.map SPath.k).sum := by
  have h1 := List.sum_take_succ (π.segs.map SPath.k) j (by simp; omega)
  have h2 := sum_take_le_sum (π.segs.map SPath.k) (j + 1)
  simp only [List.getElem_map] at h1
  rw [List.map_take]
  omega

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 1000000 in
/-- **Stage A: the vertex labels and the net outflows.** -/
theorem hdLab_exec {x : MCall M} (hP : PieceInv M x.1.piece x.2.1 x.2.2) {m : ℕ} {en : ℕ → D}
    {d b : ℕ} (c : Config) (hc : WordsBounded W c) (hL : Lay M gid u S T Z x m en d c.nmem)
    (hm : 0 < m) {g : SDart (pdarts M x.1.piece x.2.1) → ℤ}
    (hFL : ∀ i < m, (c.nmem (d + 4 + 6 * m + i) : ℤ) =
      Z + g (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm i))
    (hgZ : ∀ y, g y ≤ Z)
    (r04 : c.nreg 3004 = d) (r35 : c.nreg 9835 = b + m) (hb : d + 4 + 7 * m ≤ b)
    (w : b + 4 * m + 1 ≤ W) (wS : 2 * Z * m ≤ W) (w6 : 6 ≤ W) :
    ∃ c' k, Exec P W (.seq (block [.copyN 8430 9835]) dvP) c c' k ∧ k ≤ 48 * m + 31 ∧
      (∀ i < m, c'.nmem (b + m + i) = olab (sgF d m c.nmem) i + 1) ∧
      (∀ i < m, (c'.nmem (b + 2 * m + (c'.nmem (b + m + i) - 1)) : ℤ) -
          Z * c'.nmem (b + 3 * m + (c'.nmem (b + m + i) - 1)) =
        (pmap hP).div g ((pmap hP).tail (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm i))) ∧
      (∀ v < m, c'.nmem (b + 3 * m + v) ≤ m) ∧
      (∀ a, (a < b + m ∨ b + 4 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 7350 ∨ 7352 < r) → (r < 7400 ∨ 7405 < r) → (r < 8430 ∨ 8447 < r) →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₀, k₀, e₀, hk₀, a30, g₀, m₀, rr₀, rm₀, o₀⟩ : ∃ c₀ k₀, Exec P W
      (block [.copyN 8430 9835]) c c₀ k₀ ∧ k₀ = 1 ∧ c₀.nreg 8430 = b + m ∧
      (∀ r, r ≠ 8430 → c₀.nreg r = c.nreg r) ∧ c₀.nmem = c.nmem ∧
      c₀.rreg = c.rreg ∧ c₀.rmem = c.rmem ∧ c₀.output = c.output := by
    exec_block
    refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    · exact r35
    · simp (disch := omega) only [upd_other]
  have hFLb : ∀ i < m, c.nmem (d + 4 + 6 * m + i) ≤ 2 * Z := fun i hi => by
    have := hFL i hi; have := hgZ (layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm i); omega
  have hsum : ∑ j ∈ range m, c₀.nmem (d + 6 * m + 4 + j) ≤ W := by
    rw [m₀]
    have : ∑ j ∈ range m, c.nmem (d + 6 * m + 4 + j) ≤ ∑ j ∈ range m, 2 * Z :=
      sum_le_sum fun j hj => by
        rw [show d + 6 * m + 4 + j = d + 4 + 6 * m + j by omega]
        exact hFLb j (mem_range.1 hj)
    rw [sum_const, card_range, smul_eq_mul] at this
    nlinarith
  obtain ⟨c₁, k₁, e₁, hk₁, l₁, d₁, f₁, g₁, rr₁, rm₁, o₁⟩ := dvP_exec (P := P) c₀ e₀.wb_right
    (d := d) (A := b + m) (m := m) (by rw [g₀ _ (by omega), r04]) a30
    (by rw [m₀]; exact hL.hm) (by rw [m₀]; exact hL.permOn_sg) (by omega) (by omega) w6 hsum
  rw [m₀] at l₁ d₁
  refine ⟨c₁, k₀ + k₁, e₀.seq e₁, by omega, l₁, fun i hi => ?_, fun v hv => ?_, fun a ha => ?_,
    fun r h1 h2 h3 => ?_, by rw [rr₁, rr₀], by rw [rm₁, rm₀], by rw [o₁, o₀]⟩
  · have hl := olab_lt hL.permOn_sg hi
    rw [l₁ i hi, Nat.add_sub_cancel]
    obtain ⟨u1, u2⟩ := d₁ _ hl
    rw [show b + 2 * m + olab (sgF d m c.nmem) i = b + m + m + olab (sgF d m c.nmem) i by omega,
      show b + 3 * m + olab (sgF d m c.nmem) i = b + m + m + m + olab (sgF d m c.nmem) i by omega,
      u1, u2]
    have hfl : FLHas Z m d en c.nmem g := fun j hj => by
      rw [fext_mem g (hL.en_mem j hj)]
      have := hFL j hj
      have e : layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm j = ⟨en j, hL.en_mem j hj⟩ :=
        Subtype.ext (layEn_val hj)
      rw [e] at this; exact this
    have := dvP_div hL hP hfl hi
    have e : vDart hL hi = layEn (pdarts M x.1.piece x.2.1) en m hL.en_mem hm i :=
      Subtype.ext (layEn_val hi).symm
    rw [e] at this
    exact this
  · obtain ⟨-, u2⟩ := d₁ v hv
    rw [show b + 3 * m + v = b + m + m + m + v by omega, u2]
    unfold dvC
    exact (card_filter_le _ _).trans (by rw [card_range])
  · rw [f₁ a (by omega), m₀]
  · rw [g₁ r h1 h2 (by omega), g₀ r (by omega)]

set_option maxHeartbeats 2000000 in
/-- **Stage B: the flags of a part of the separator** (whose index is in `rj`). -/
theorem hdTf_exec {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D}
    (h : SCond M l r π Hs σ) {m : ℕ} {en : ℕ → D} {d e b : ℕ} (hm : 0 < m)
    (c : Config) (hc : WordsBounded W c)
    (hL : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem) (hSeg : SegsAt' M en m π e b c)
    (hde : d + fsz m ≤ e) (heb : e ≤ b)
    {rj Vr Fr jj Vb Fb : ℕ} (hrj : 9830 ≤ rj ∨ rj < 9700)
    (hrj' : rj ≠ 9856 ∧ rj ≠ 9857 ∧ rj ≠ 9858 ∧ rj ≠ 9860 ∧ rj ≠ 9865 ∧ rj ≠ 9866 ∧
      rj ≠ 9867 ∧ rj ≠ 9868 ∧ rj ≠ 9869 ∧ rj ≠ 9870 ∧ rj ≠ 9871)
    (hV : 9830 ≤ Vr ∧ Vr < 9856) (hF : 9830 ≤ Fr ∧ Fr < 9856)
    (rjj : c.nreg rj = jj) (rV : c.nreg Vr = Vb) (rF : c.nreg Fr = Fb)
    (hjj : jj < (segsP h.1 π.segs h.2).length)
    (r32 : c.nreg 9832 = m) (r35 : c.nreg 9835 = b + m) (r74 : c.nreg 9874 = d + 4 + m)
    (hLAB : ∀ i < m, c.nmem (b + m + i) = olab (sgF d m c.nmem) i + 1)
    (l1 : b + m + m ≤ Vb) (l2 : Vb + m + 1 ≤ Fb) (w1 : Fb + m ≤ W) :
    ∃ c' k, Exec P W (.seq (tfGl rj Vr Fr) tfP) c c' k ∧
      k ≤ 25 + (5 * (m + 1) + 15 * m + 9 * m + 25) ∧
      (∀ i < m, c'.nmem (Fb + i) = flagX (pmap h.1)
        (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm)
        ((segsP h.1 π.segs h.2)[jj]).verts i) ∧
      (∀ a, (a < Vb ∨ Fb + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ TfGo r → ¬ (9856 ≤ r ∧ r ≤ 9871) → ¬ TfScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hjj' : jj < π.segs.length := by rw [← length_segsP h.1 π.segs h.2]; exact hjj
  unfold SegsAt' at hSeg
  set Gb := c.nreg 6807 with hGb
  set s := π.segs.length with hsd
  have hS := hSeg.1
  obtain ⟨o1, o2, o3, o4⟩ := hS
  obtain ⟨g1, g2, g3⟩ := o4 jj hjj'
  have hsum := segs_sum hSeg.1 (by omega)
  have htk := segs_take_add_le hjj'
  have hst := hSeg.2.2 jj hjj'
  have hend := hSeg.2.1
  unfold fsz at hde
  -- the part has fewer darts than the piece map
  have hK : (π.segs[jj]).k + 1 ≤ m := by
    have e1 := congrArg (fun L => L[jj]?) (segsP_k h.1 π.segs h.2)
    simp only [List.getElem?_map, List.getElem?_eq_getElem hjj, List.getElem?_eq_getElem hjj',
      Option.map_some, Option.some.injEq] at e1
    have := SPath.k_lt_card ((segsP h.1 π.segs h.2)[jj])
    have hVc : Fintype.card (SVert σ (pdarts M (l.piece ∪ r.piece) Hs)) ≤ m := by
      have := Fintype.card_le_of_surjective _
        (pmap_tail_surj (x := (.node l r π, Hs, σ)) h.1)
      rw [StEnc.card_eq (lay_enumOK h.1 hL hm (pmap_faceTrans h.1))] at this; exact this
    omega
  have eLb : Gb + 1 + s + s + c.nmem (Gb + 1 + jj) =
      Gb + 1 + 2 * s + ((π.segs.take jj).map SPath.k).sum := by rw [g1]; omega
  have eK : c.nmem (Gb + 1 + jj + s) = (π.segs[jj]).k := by
    rw [show Gb + 1 + jj + s = Gb + 1 + s + jj by omega]; exact g2
  have eS : c.nmem (Gb + 1 + s + s + (c.nmem (Gb + s) + c.nmem (Gb + s + s)) + jj) =
      c.nmem (Gb + 1 + 2 * s + (π.segs.map SPath.k).sum + jj) := by
    rw [hsum, show Gb + 1 + s + s = Gb + 1 + 2 * s by omega]
  obtain ⟨c₁, k₁, e₁, hk₁, a00, a01, a02, a03, a04, a05, a13, a14, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    tfGl_exec (P := P) c hc hrj hrj' hV hF rfl o2 rjj r32 r35 r74 rV rF
      (by rw [hsum]; omega) (by rw [g1]; omega) (by omega)
  rw [eLb] at a02
  rw [eK] at a03
  rw [eS] at a14
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, f₂, g₂, rr₂, rm₂, o₂⟩ := tfP_exec (P := P) c₁ e₁.wb_right
    a00 a01 a02 a03 a04 a05 a13 a14
    (fun i hi => by rw [m₁, hLAB i hi]; have := olab_lt hL.permOn_sg hi; omega)
    (fun t ht => by
      rw [m₁]
      have := (g3 t ht).1
      rwa [show Gb + 1 + 2 * π.segs.length + ((π.segs.take jj).map SPath.k).sum + t =
        Gb + 1 + 2 * s + ((π.segs.take jj).map SPath.k).sum + t by omega] at this)
    (fun i hi => by rw [m₁]; exact (hL.rv i hi).1)
    hst.1 (by omega) (by omega) (by omega) l2 w1 (by omega)
  refine ⟨c₂, k₁ + k₂, e₁.seq e₂, by omega, fun i hi => ?_, fun a ha => ?_,
    fun r h1 h2 h3 => ?_, by rw [rr₂, rr₁], by rw [rm₂, rm₁], by rw [o₂, o₁]⟩
  · rw [v₂ i hi, m₁]
    exact tfFlag_segsP hL h.1 hm h.2 hSeg hjj hLAB (fun i hi => rfl) hi
  · rw [f₂ a ha, m₁]
  · rw [g₂ r h3, f₁ r h1 h2]

end NcStep

end BKMNW

end PlanarFlow
